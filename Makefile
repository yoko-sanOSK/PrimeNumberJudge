CXX ?= g++
CXXFLAGS ?= -std=c++17 -O3 -march=native -Wall -Wextra -Wpedantic

probable_prime: probable_prime.cpp
	$(CXX) $(CXXFLAGS) -o $@ $<

clean:
	rm -f probable_prime

.PHONY: clean
