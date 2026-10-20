// probable_prime.cpp
//
// 概素数判定・高速走査＆精度評価プログラム
//
//   11 <= n <= N かつ下1桁 r ∈ {1,3,7,9} の整数 n = 10q + r について、
//   a = q mod 3 を用いて概素数／合成数を判定する。
//
// 使い方:
//   ./probable_prime <upper_limit>                      通常モード（概素数を列挙）
//   ./probable_prime                                    通常モード（上限値を標準入力から取得）
//   ./probable_prime <upper_limit> --eval|-e            評価モード
//       [--repeat K]       Phase 1 の計測反復回数（既定 5）
//       [--sieve-cap X]    Phase 2 で篩を構築する上限値（既定 2^35 ≈ 3.4e10, 約 2 GiB）
//
// ビルド:
//   g++ -std=c++17 -O3 -march=native -Wall -Wextra -o probable_prime probable_prime.cpp

#include <algorithm>
#include <charconv>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstring>
#include <iomanip>
#include <iostream>
#include <limits>
#include <new>
#include <optional>
#include <string>
#include <string_view>
#include <system_error>
#include <vector>

namespace {

using u64 = std::uint64_t;
using Clock = std::chrono::steady_clock;

// ============================================================================
// 3.1 判定関数（単一候補用・検証用）
// ============================================================================

enum class JudgeResult { ProbablePrime, Composite };

constexpr JudgeResult judge_from_qa(u64 a, u64 r) noexcept {
    if (r == 3 || r == 9) {
        return (a == 0) ? JudgeResult::Composite : JudgeResult::ProbablePrime;
    } else {  // r == 1 || r == 7
        return (a == 2) ? JudgeResult::Composite : JudgeResult::ProbablePrime;
    }
}

// 直接生成テーブル（2.2）が判定ルールと一致することをコンパイル時に検証する。
//   a = 0 : {1, 7}       a = 1 : {1, 3, 7, 9}       a = 2 : {3, 9}
constexpr bool block_table_is_consistent() noexcept {
    constexpr u64 kDigits[4] = {1, 3, 7, 9};
    constexpr bool kTable[3][4] = {
        {true, false, true, false},  // a = 0
        {true, true, true, true},    // a = 1
        {false, true, false, true},  // a = 2
    };
    for (u64 a = 0; a < 3; ++a)
        for (int i = 0; i < 4; ++i)
            if ((judge_from_qa(a, kDigits[i]) == JudgeResult::ProbablePrime) != kTable[a][i])
                return false;
    return true;
}
static_assert(block_table_is_consistent(), "direct generation table must match judge_from_qa");

// ============================================================================
// 高速走査コア
//   n = 10q + r を直接生成し、概素数ごとに visit(n) を呼ぶ。
//   ループ内では除算・剰余演算を行わず、a と base = 10q を加算のみで更新する。
//   最終ブロック q = floor(N/10) のみ r <= N mod 10 の境界判定を行う
//   （これにより N が u64 の上限付近でも 10q + r がオーバーフローしない）。
// ============================================================================

template <class Visitor>
inline void for_each_probable_prime(u64 N, Visitor&& visit) {
    if (N < 11) return;
    const u64 q_max = N / 10;  // >= 1
    const u64 r_max = N % 10;

    u64 a = 1;      // q = 1 のとき q mod 3 = 1
    u64 base = 10;  // = 10q
    for (u64 q = 1; q < q_max; ++q) {
        switch (a) {
            case 0:
                visit(base + 1);
                visit(base + 7);
                break;
            case 1:
                visit(base + 1);
                visit(base + 3);
                visit(base + 7);
                visit(base + 9);
                break;
            default:  // a == 2
                visit(base + 3);
                visit(base + 9);
                break;
        }
        a = (a == 2) ? 0 : a + 1;
        base += 10;
    }

    // 最終ブロック（部分ブロックの可能性あり）
    constexpr u64 kDigits[4] = {1, 3, 7, 9};
    for (u64 r : kDigits)
        if (r <= r_max && judge_from_qa(a, r) == JudgeResult::ProbablePrime) visit(base + r);
}

// ============================================================================
// 通常モード：バッファ付き高速出力
// ============================================================================

class FastWriter {
public:
    FastWriter() : buf_(kBufSize) {}
    ~FastWriter() { flush(); }
    FastWriter(const FastWriter&) = delete;
    FastWriter& operator=(const FastWriter&) = delete;

    void write_line(u64 v) {
        if (pos_ + 21 > kBufSize) flush();  // u64 は最大20桁 + '\n'
        char tmp[20];
        int len = 0;
        do {
            tmp[len++] = static_cast<char>('0' + v % 10);
            v /= 10;
        } while (v != 0);
        while (len > 0) buf_[pos_++] = tmp[--len];
        buf_[pos_++] = '\n';
    }

    void flush() {
        if (pos_ > 0) {
            std::fwrite(buf_.data(), 1, pos_, stdout);
            pos_ = 0;
        }
        std::fflush(stdout);
    }

private:
    static constexpr std::size_t kBufSize = 1 << 16;
    std::vector<char> buf_;
    std::size_t pos_ = 0;
};

// ============================================================================
// エラトステネスの篩（奇数のみ・ビット圧縮・区分篩で構築）
//   bit i が 1 ⇔ 2i+1 が合成数（または 1）。N/16 バイトのメモリを使用する。
//   全体テーブルを保持しつつ、マーキングは L2 に収まる区間ごとに行い
//   キャッシュ効率を確保する。
// ============================================================================

class OddSieve {
public:
    explicit OddSieve(u64 N) : N_(N) {
        const u64 n_odd = N / 2 + 1;  // 1, 3, 5, ..., (N 以下の最大奇数) の個数（+余裕）
        bits_.assign((n_odd + 63) / 64, 0);
        bits_[0] |= 1;  // 1 は素数でない

        // sqrt(N) 以下の奇素数を単純な篩で求める
        u64 root = isqrt(N);
        std::vector<char> small(root + 1, 1);
        std::vector<u64> primes;
        for (u64 p = 3; p <= root; p += 2) {
            if (!small[p]) continue;
            primes.push_back(p);
            for (u64 m = p * p; m <= root; m += 2 * p) small[m] = 0;
        }

        // 区分篩：奇数インデックス区間 [lo, hi) を順に処理
        constexpr u64 kSegBits = u64{1} << 21;  // 2^21 bit = 256 KiB
        std::vector<u64> next(primes.size());   // 各素数の次にマークする奇数インデックス
        for (std::size_t k = 0; k < primes.size(); ++k) next[k] = (primes[k] * primes[k]) / 2;

        for (u64 lo = 0; lo < n_odd; lo += kSegBits) {
            const u64 hi = std::min(n_odd, lo + kSegBits);
            for (std::size_t k = 0; k < primes.size(); ++k) {
                const u64 p = primes[k];  // 奇数インデックス上では p ずつ進む
                u64 j = next[k];
                if (j >= hi) continue;
                for (; j < hi; j += p) bits_[j >> 6] |= u64{1} << (j & 63);
                next[k] = j;
            }
        }
    }

    bool is_prime(u64 n) const noexcept {
        if (n < 2) return false;
        if (n == 2) return true;
        if ((n & 1) == 0) return false;
        const u64 i = n >> 1;
        return ((bits_[i >> 6] >> (i & 63)) & 1) == 0;
    }

    u64 limit() const noexcept { return N_; }
    std::size_t bytes() const noexcept { return bits_.size() * sizeof(u64); }

    static u64 isqrt(u64 n) noexcept {
        u64 r = 0;
        for (u64 bit = u64{1} << 31; bit != 0; bit >>= 1) {
            const u64 t = r | bit;
            if (t <= n / t) r = t;
        }
        return r;
    }

private:
    u64 N_;
    std::vector<u64> bits_;
};

// ============================================================================
// 引数解析
// ============================================================================

std::optional<u64> parse_u64(std::string_view s) {
    while (!s.empty() && (s.front() == ' ' || s.front() == '\t')) s.remove_prefix(1);
    while (!s.empty() && (s.back() == ' ' || s.back() == '\t' || s.back() == '\r' || s.back() == '\n'))
        s.remove_suffix(1);
    if (s.empty()) return std::nullopt;

    // 1e9 のような指数表記（整数として表せる場合のみ）も受け付ける
    if (auto e = s.find_first_of("eE"); e != std::string_view::npos) {
        auto mant = parse_u64(s.substr(0, e));
        auto expo = parse_u64(s.substr(e + 1));
        if (!mant || !expo || *expo > 19) return std::nullopt;
        u64 v = *mant;
        for (u64 i = 0; i < *expo; ++i) {
            if (v > std::numeric_limits<u64>::max() / 10) return std::nullopt;
            v *= 10;
        }
        return v;
    }

    u64 v = 0;
    auto [ptr, ec] = std::from_chars(s.data(), s.data() + s.size(), v);
    if (ec != std::errc{} || ptr != s.data() + s.size()) return std::nullopt;
    return v;
}

struct Options {
    u64 N = 0;
    bool eval = false;
    u64 repeat = 5;
    u64 sieve_cap = u64{1} << 35;
};

void print_usage(const char* prog) {
    std::cerr << "Usage:\n"
              << "  " << prog << " <upper_limit>              # 概素数を列挙\n"
              << "  " << prog << "                            # 上限値を標準入力から取得\n"
              << "  " << prog << " <upper_limit> --eval|-e [--repeat K] [--sieve-cap X]\n";
}

std::optional<Options> parse_args(int argc, char** argv) {
    Options opt;
    bool have_n = false;
    for (int i = 1; i < argc; ++i) {
        std::string_view arg = argv[i];
        if (arg == "--eval" || arg == "-e") {
            opt.eval = true;
        } else if (arg == "--repeat" || arg == "--sieve-cap") {
            if (i + 1 >= argc) return std::nullopt;
            auto v = parse_u64(argv[++i]);
            if (!v) return std::nullopt;
            if (arg == "--repeat") opt.repeat = std::max<u64>(1, *v);
            else opt.sieve_cap = *v;
        } else if (arg == "-h" || arg == "--help") {
            return std::nullopt;
        } else {
            auto v = parse_u64(arg);
            if (!v || have_n) return std::nullopt;
            opt.N = *v;
            have_n = true;
        }
    }
    if (!have_n) {
        std::string line;
        if (!(std::cin >> line)) return std::nullopt;
        auto v = parse_u64(line);
        if (!v) return std::nullopt;
        opt.N = *v;
    }
    return opt;
}

// ============================================================================
// 評価モード
// ============================================================================

struct ScanResult {
    u64 count = 0;
    u64 checksum = 0;  // XOR チェックサム（DCE 防止 & Phase 2 との整合性検証）
};

ScanResult scan_count(u64 N) {
    ScanResult res;
    for_each_probable_prime(N, [&](u64 n) {
        ++res.count;
        res.checksum ^= n;
    });
    return res;
}

// 母集団 M：11 <= n <= N かつ下1桁 ∈ {1,3,7,9}
u64 population_size(u64 N) {
    if (N < 11) return 0;
    const u64 q_max = N / 10, r_max = N % 10;
    u64 last = (r_max >= 1) + (r_max >= 3) + (r_max >= 7) + (r_max >= 9);
    return 4 * (q_max - 1) + last;
}

// 理論値：概素数 = 30 と互いに素な 11 以上 N 以下の整数（包除原理）
u64 theoretical_probable_count(u64 N) {
    if (N < 11) return 0;
    const u64 coprime30 = N - N / 2 - N / 3 - N / 5 + N / 6 + N / 10 + N / 15 - N / 30;
    return coprime30 - 2;  // 1 と 7 を除く
}

double pct(u64 num, u64 den) { return den == 0 ? 0.0 : 100.0 * static_cast<double>(num) / static_cast<double>(den); }

std::string with_commas(u64 v) {
    std::string s = std::to_string(v);
    for (int i = static_cast<int>(s.size()) - 3; i > 0; i -= 3) s.insert(static_cast<std::size_t>(i), ",");
    return s;
}

// UTF-8 ラベルを表示幅（全角=2, 半角=1）で width に揃える
std::string pad_label(std::string_view label, std::size_t width) {
    std::size_t w = 0;
    for (std::size_t i = 0; i < label.size();) {
        const unsigned char c = static_cast<unsigned char>(label[i]);
        const std::size_t len = c < 0x80 ? 1 : c < 0xE0 ? 2 : c < 0xF0 ? 3 : 4;
        w += (len >= 3) ? 2 : 1;
        i += len;
    }
    return std::string(label) + std::string(w < width ? width - w : 0, ' ');
}

void print_time(const char* label, std::chrono::nanoseconds ns) {
    std::cout << "  " << pad_label(label, 30) << ": " << std::fixed << std::setprecision(3)
              << std::setw(12) << static_cast<double>(ns.count()) / 1e6 << " ms  (" << with_commas(static_cast<u64>(ns.count()))
              << " ns)\n";
}

int run_eval(const Options& opt) {
    const u64 N = opt.N;
    const u64 M = population_size(N);

    std::cout << "==================================================================\n"
              << " 概素数判定 評価モード\n"
              << "==================================================================\n"
              << "  上限値 N                      : " << with_commas(N) << "\n"
              << "  母集団 M                      : " << with_commas(M) << "  (11<=n<=N, 下1桁∈{1,3,7,9})\n\n";

    // ---------------- Phase 1: 純粋な走査時間 ----------------
    std::vector<std::chrono::nanoseconds> times;
    ScanResult p1;
    for (u64 t = 0; t < opt.repeat; ++t) {
        auto t0 = Clock::now();
        ScanResult r = scan_count(N);
        auto t1 = Clock::now();
        times.push_back(std::chrono::duration_cast<std::chrono::nanoseconds>(t1 - t0));
        if (t == 0) p1 = r;
        else if (r.count != p1.count || r.checksum != p1.checksum) {
            std::cerr << "error: Phase 1 results differ between runs\n";
            return 1;
        }
    }
    std::vector<std::chrono::nanoseconds> sorted = times;
    std::sort(sorted.begin(), sorted.end());
    const auto t_min = sorted.front();
    const auto t_med = sorted[sorted.size() / 2];

    std::cout << "[Phase 1] 提案アルゴリズム単体の走査（I/O・篩参照なし, " << opt.repeat << " 回計測）\n"
              << "  概素数の個数                  : " << with_commas(p1.count) << "\n"
              << "  XOR チェックサム              : 0x" << std::hex << std::setw(16) << std::setfill('0') << p1.checksum
              << std::dec << std::setfill(' ') << "\n"
              << "  理論値（30と互いに素な数）    : " << with_commas(theoretical_probable_count(N))
              << (theoretical_probable_count(N) == p1.count ? "  [一致]" : "  [不一致!]") << "\n";
    print_time("走査時間 (最小)", t_min);
    print_time("走査時間 (中央値)", t_med);
    if (M > 0)
        std::cout << "  候補1個あたり (最小)          : " << std::fixed << std::setprecision(4)
                  << static_cast<double>(t_min.count()) / static_cast<double>(M) << " ns\n";
    std::cout << "\n";

    // ---------------- Phase 2: 篩との照合 ----------------
    std::cout << "[Phase 2] エラトステネスの篩との照合・精度評価\n";
    if (N > opt.sieve_cap) {
        std::cout << "  N が篩の上限 (" << with_commas(opt.sieve_cap) << ") を超えるため Phase 2 をスキップしました。\n"
                  << "  （--sieve-cap で変更可。必要メモリ ≈ N/16 バイト）\n";
        return 0;
    }

    std::optional<OddSieve> sieve;
    auto s0 = Clock::now();
    try {
        sieve.emplace(N);
    } catch (const std::bad_alloc&) {
        std::cout << "  篩のメモリ確保に失敗しました（必要 ≈ " << with_commas(N / 16) << " バイト）。\n";
        return 1;
    }
    auto s1 = Clock::now();
    const auto t_sieve = std::chrono::duration_cast<std::chrono::nanoseconds>(s1 - s0);

    // 照合：Phase 1 とは独立に、全候補を judge_from_qa で判定する
    u64 TP = 0, FP = 0, TN = 0, FN = 0;
    u64 judged_count = 0, judged_checksum = 0;
    u64 first_fp = 0, first_fn = 0;
    u64 tp_by_r[10] = {}, fp_by_r[10] = {};
    auto c0 = Clock::now();
    if (N >= 11) {
        constexpr u64 kDigits[4] = {1, 3, 7, 9};
        const u64 q_max = N / 10;
        u64 a = 1, base = 10;
        for (u64 q = 1; q <= q_max; ++q) {
            for (u64 r : kDigits) {
                const u64 n = base + r;
                if (q == q_max && r > N % 10) break;
                const bool predicted = judge_from_qa(a, r) == JudgeResult::ProbablePrime;
                const bool actual = sieve->is_prime(n);
                if (predicted) {
                    ++judged_count;
                    judged_checksum ^= n;
                    if (actual) {
                        ++TP;
                        ++tp_by_r[r];
                    } else {
                        ++FP;
                        ++fp_by_r[r];
                        if (first_fp == 0) first_fp = n;
                    }
                } else {
                    if (actual) {
                        ++FN;
                        if (first_fn == 0) first_fn = n;
                    } else {
                        ++TN;
                    }
                }
            }
            a = (a == 2) ? 0 : a + 1;
            base += 10;
        }
    }
    auto c1 = Clock::now();
    const auto t_cmp = std::chrono::duration_cast<std::chrono::nanoseconds>(c1 - c0);

    const bool consistent = judged_count == p1.count && judged_checksum == p1.checksum;
    std::cout << "  篩のメモリ使用量              : " << with_commas(sieve->bytes()) << " バイト (奇数のみ・1bit/要素)\n"
              << "  Phase 1 との整合性            : " << (consistent ? "一致 (個数・チェックサム)" : "不一致!") << "\n\n"
              << "  混同行列\n"
              << "                      真:素数        真:合成数\n"
              << "    判定:概素数  " << std::setw(15) << with_commas(TP) << "  " << std::setw(15) << with_commas(FP) << "\n"
              << "    判定:合成数  " << std::setw(15) << with_commas(FN) << "  " << std::setw(15) << with_commas(TN) << "\n\n"
              << "  TP (真陽性)                   : " << with_commas(TP) << "\n"
              << "  FP (偽陽性)                   : " << with_commas(FP)
              << (first_fp ? "  (最小の偽陽性: " + with_commas(first_fp) + ")" : std::string()) << "\n"
              << "  TN (真陰性)                   : " << with_commas(TN) << "\n"
              << "  FN (偽陰性)                   : " << with_commas(FN)
              << (first_fn ? "  (最小の偽陰性: " + with_commas(first_fn) + ")" : std::string("  (理論値 0)")) << "\n"
              << "  検算 TP+FP+TN+FN = M          : " << ((TP + FP + TN + FN == M) ? "OK" : "NG") << "\n\n"
              << std::fixed << std::setprecision(6)
              << "  正答率   (Accuracy)           : " << std::setw(12) << pct(TP + TN, M) << " %\n"
              << "  適合率   (Precision)          : " << std::setw(12) << pct(TP, TP + FP) << " %\n"
              << "  再現率   (Recall)             : " << std::setw(12) << pct(TP, TP + FN) << " %\n"
              << "  偽陽性率 (FPR)                : " << std::setw(12) << pct(FP, FP + TN) << " %\n\n"
              << "  下1桁別の内訳 (概素数判定のみ)\n"
              << "     r            TP              FP     適合率(%)\n";
    for (u64 r : {1, 3, 7, 9})
        std::cout << "     " << r << std::setw(14) << with_commas(tp_by_r[r]) << "  " << std::setw(14)
                  << with_commas(fp_by_r[r]) << "  " << std::setw(12) << pct(tp_by_r[r], tp_by_r[r] + fp_by_r[r]) << "\n";
    std::cout << "\n  実行時間\n";
    print_time("提案アルゴリズム走査 (最小)", t_min);
    print_time("エラトステネスの篩 構築", t_sieve);
    print_time("照合処理 (参考)", t_cmp);
    if (t_min.count() > 0)
        std::cout << "  篩構築 / 提案走査 の比        : " << std::setprecision(2)
                  << static_cast<double>(t_sieve.count()) / static_cast<double>(t_min.count()) << " 倍\n";
    return consistent && (TP + FP + TN + FN == M) ? 0 : 1;
}

int run_enumerate(u64 N) {
    FastWriter out;
    for_each_probable_prime(N, [&](u64 n) { out.write_line(n); });
    return 0;
}

}  // namespace

int main(int argc, char** argv) {
    std::ios::sync_with_stdio(false);
    auto opt = parse_args(argc, argv);
    if (!opt) {
        print_usage(argv[0]);
        return 2;
    }
    return opt->eval ? run_eval(*opt) : run_enumerate(opt->N);
}
