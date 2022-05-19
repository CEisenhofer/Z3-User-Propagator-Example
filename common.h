#pragma once

#include <algorithm>
#include <cassert>
#include <chrono>
#include <iostream>
#include <random>
#include <stack>
#include <unordered_map>
#include <unordered_set>
#include <vector>
#include <cstring>
#include <c++/z3++.h>
#include <optional>

using std::to_string;
using namespace std::chrono;

#define REPETITIONS 1

#define MIN_BOARD 4
#define MAX_BOARD1 13
#define MAX_BOARD2 13

#define SORT_CNT 128
#define BIT_CNT 32

#define DISTINCT_CNT 128

// #define RANDOM_SHUFFLE

#define SIZE(x) std::extent<decltype(x)>::value

#define MIN(x, y) ((x) < (y) ? (x) : (y))
#define MAX(x, y) ((x) > (y) ? (x) : (y))

// #define VERBOSE // Log events
#ifdef VERBOSE
#define WriteEmptyLine std::cout << std::endl
#define WriteLine(x) std::cout << (x) << std::endl
#define Write(x) std::cout << x
#else
#define WriteEmptyLine
#define WriteLine(x)
#define Write(x)
#endif

struct Params {
    bool propagator : 1;
    bool decide : 1;
    bool decide_random : 1;
    bool decide_occurences: 1;
    bool adjacent : 1;
    bool connected : 1;
    bool connected_all : 1;
    bool simulate_quantifier : 1;
    bool all_sat : 1;

    Params() = default;

    Params(bool propagator, bool decide, bool decide_random, bool decide_occurences, bool adjacent, bool connected, bool connected_all, bool simulate_quantifier, bool all_sat)
        : propagator(propagator),
        decide(decide),
        decide_random(decide_random),
        decide_occurences(decide_occurences),
        adjacent(adjacent),
        connected(connected),
        connected_all(connected_all),
        simulate_quantifier(simulate_quantifier),
        all_sat(all_sat) {

        assert(!decide_random || decide);
        assert(!decide_occurences || decide);
        assert(!decide_random || !decide_occurences);
        assert(!connected_all || connected);
        assert(!all_sat || simulate_quantifier);
    }
};

int distinct1(unsigned num, unsigned bits);

int distinct2(unsigned num, unsigned bits);

int distinct3(unsigned num, unsigned bits);

int distinct4(unsigned num, unsigned bits);

int opt_sorting(unsigned* args, Params params = Params());

void checkSorting(const z3::model &model, const z3::expr_vector &in, const z3::expr_vector &out);

enum sortingConstraints : unsigned char {
    inputDisjoint = 1,
    outputDisjoint = 2,
    inputReverse = 4,
    outputReverse = 8 //unsat
};

void applyConstraints(z3::solver& s, const z3::expr_vector& in, const z3::expr_vector& out, sortingConstraints constraints);

int sorting1(unsigned size, sortingConstraints constraints);

int sorting2(unsigned size, sortingConstraints constraints);

int sorting3(unsigned size, sortingConstraints constraints);

int sorting4(unsigned size, sortingConstraints constraints);

int sorting5(unsigned size, sortingConstraints constraints);

int sorting6(unsigned size, sortingConstraints constraints);

int sorting7(unsigned size, sortingConstraints constraints);

int sorting8(unsigned size, sortingConstraints constraints);

void disjointness();

int nqueensNoPropagatorSAT(unsigned board);

int nqueensNoPropagatorBV(unsigned board);

int nqueensPropagator(unsigned board, bool singleSolution, bool addConflicts, bool pureSAT, bool withTheory, bool withDecide);

int nqueensMaximization1(unsigned *num);

int nqueensMaximization2(unsigned *num);

int nqueensMaximization3(unsigned *num);

int nqueensMaximization4(unsigned *num);

inline int nqueensNoPropagator1(unsigned *num) {
    return nqueensNoPropagatorSAT(*num);
}

inline int nqueensNoPropagator2(unsigned *num) {
    return nqueensNoPropagatorBV(*num);
}

inline int nqueensNoPropagator3(unsigned* num) {
    return nqueensPropagator(*num, false, false, false, false, true);
}

inline int nqueensPropagator1(unsigned* num) {
    return nqueensPropagator(*num, false, true, true, false, false);
}

inline int nqueensPropagator2(unsigned *num) {
    return nqueensPropagator(*num, false, true, false, false, false);
}

inline int nqueensPropagator3(unsigned *num) {
    return nqueensPropagator(*num, false, true, false, true, false);
}

inline int nqueensPropagator4(unsigned* num) {
    return nqueensPropagator(*num, false, true, false, true, true);
}

int nqueensHigherDimensionAllCover(unsigned args[2]);

void printStatistics(z3::solver& s);

inline int log2i(unsigned n) {
    if (n <= 0) {
        return 0;
    }
    if (n <= 2) {
        return 1;
    }
    unsigned l = 1;
    int i = 0;
    while (l < n) {
        l <<= 1;
        i++;
    }
    return i;
}

typedef std::vector<unsigned> simple_model;

// For putting z3 expressions in hash-tables
namespace std {

    template<>
    struct hash<simple_model> {
        std::size_t operator()(const simple_model &m) const {
            size_t hash = 0;
            for (unsigned i = 0; i < m.size(); i++) {
                hash *= m.size();
                hash += m[i];
            }
            return hash;
        }
    };

    template<>
    struct hash<z3::expr> {
        std::size_t operator()(const z3::expr &k) const {
            return k.hash();
        }
    };

    // Do not use Z3's == operator in the hash table
    template<>
    struct equal_to<z3::expr> {
        bool operator()(const z3::expr &lhs, const z3::expr &rhs) const {
            return z3::eq(lhs, rhs);
        }
    };
}

class exprNetwork {

    z3::context& ctx;
    std::vector<std::vector<z3::expr>> inputs; // 1st level: line; 2nd depth

public:

    exprNetwork(z3::context& ctx, unsigned lines) : ctx(ctx) {
        for (unsigned i = 0; i < lines; i++) {
            inputs.emplace_back();
        }
    }

    unsigned size() const {
        return (unsigned)inputs.size();
    }

    const z3::expr& getCurrentLineValue(unsigned line) const {
        assert(line < inputs.size());
        return inputs[line].back();
    }

    unsigned getCurrentLineSize(unsigned line) {
        assert(line < inputs.size());
        return (unsigned)inputs[line].size();
    }

    void add(unsigned line, const z3::expr& expr) {
        assert(line < inputs.size());
        inputs[line].push_back(expr);
    }

    void addComparision(unsigned line1, unsigned line2) {
        assert(line1 < inputs.size());
        assert(line2 < inputs.size());
        const auto v1 = getCurrentLineValue(line1);
        const auto v2 = getCurrentLineValue(line2);
        add(line1, z3::ite(z3::ule(v1, v2), v1, v2));
        add(line2, z3::ite(!z3::ule(v1, v2), v1, v2));
    }

    z3::expr_vector getOutputs() const {
        z3::expr_vector out(ctx);
        for (const auto& v : inputs) {
            out.push_back(v.back());
        }
        return out;
    }
};

struct destination {
    unsigned line;
    unsigned position;
};

class symbolicNetwork {

    std::vector<std::vector<destination>> inputs;

public:

    symbolicNetwork(unsigned lines) {
        for (unsigned i = 0; i < lines; i++) {
            inputs.emplace_back();
        }
    }

    unsigned getCurrentLineSize(unsigned line) const {
        assert(line < inputs.size());
        return (unsigned)inputs[line].size();
    }

    const destination& getDestination(unsigned line, unsigned pos) const {
        assert(line < inputs.size());
        assert(pos < inputs[line].size());
        return inputs[line][pos];
    }

    void add(unsigned line, const destination& destination) {
        assert(line < inputs.size());
        inputs[line].push_back(destination);
    }

    void addComparision(unsigned line1, unsigned line2) {
        assert(line1 < inputs.size());
        assert(line2 < inputs.size());
        const auto v1 = getCurrentLineSize(line1);
        const auto v2 = getCurrentLineSize(line2);
        add(line1, { line2, v2 });
        add(line2, { line1, v1 });
    }
};