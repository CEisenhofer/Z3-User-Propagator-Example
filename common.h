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

enum sortingConstraints : unsigned char;
using std::to_string;
using namespace std::chrono;

#define BIT_CNT 32

static_assert(BIT_CNT <= 32); // conflict with checkSorting otherwise 

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

enum InstantiationStrategy {
    None = 0,
    CompleteModel = 1,
    MinimalModel = 2,
    Repropagate = 4,
    Restart = 8,
    Randomized = 16,
    NearlyCompleteModel = 32,
};

struct Params {
    bool propagator : 1;
    bool decide : 1;
    bool decide_occurences: 1;
    bool adjacent : 1;
    bool connected : 1;
    bool connected_all : 1;
    bool all_sat : 1;
    InstantiationStrategy strategy;

    Params() = default;

    Params(bool propagator, bool decide, bool decide_occurences, bool adjacent, bool connected, bool connected_all, bool all_sat, InstantiationStrategy strategy)
        : propagator(propagator),
        decide(decide),
        decide_occurences(decide_occurences),
        adjacent(adjacent),
        connected(connected),
        connected_all(connected_all),
        all_sat(all_sat),
        strategy(strategy) {

        assert(!decide_occurences || decide);
        assert(!connected_all || connected);
        assert(!all_sat || propagator);
    }
};

int distinct1(unsigned num, unsigned bits);

int distinct2(unsigned num, unsigned bits);

int distinct3(unsigned num, unsigned bits);

int distinct4(unsigned num, unsigned bits);

int opt_sorting(unsigned* args, Params params = Params());

void checkSorting(const z3::model &model, const z3::expr_vector &in, const z3::expr_vector &out, const sortingConstraints constraints);

enum sortingConstraints : unsigned char {
    nonConstraint = 0,
    inputDisjoint = 1,
    outputDisjoint = 2,
    inputReverse = 4,
    outputReverse = 8, //unsat
    pseudoBoolean = 16,
    intervals = 32,
};

struct multiSort {

    z3::expr_vector* in = nullptr, * out = nullptr;

    virtual ~multiSort() {
        delete in;
        delete out;
    }

    virtual void add(z3::expr_vector& in, z3::expr_vector& out) = 0;

    void assertDefault(unsigned size, z3::context& context) {
        if (in == nullptr) {
            in = new z3::expr_vector(context);
            out = new z3::expr_vector(context);
        }

        for (unsigned i = 0; i < size; i++) {
            in->push_back(context.bv_const(("in_" + std::to_string(i)).c_str(), BIT_CNT));
            out->push_back(context.bv_const(("out_" + std::to_string(i)).c_str(), BIT_CNT));
        }
        add(*in, *out);
    }
};

void applyConstraints(z3::solver& s, unsigned size, multiSort& sort, sortingConstraints constraints);

int sorting1(unsigned size, sortingConstraints constraints);

int sorting2(unsigned size, sortingConstraints constraints);

int sorting3(unsigned size, sortingConstraints constraints);

int sorting4(unsigned size, sortingConstraints constraints);

int sorting5(unsigned size, sortingConstraints constraints, bool guess);

int sorting6(unsigned size, sortingConstraints constraints);

int sorting7(unsigned size, sortingConstraints constraints);

int sorting8(unsigned size, sortingConstraints constraints, bool guess);

int sorting9(unsigned size);

void disjointness();

int nqueensNoPropagatorSAT(unsigned board);

int nqueensNoPropagatorBV(unsigned board);

int nqueensPropagator(unsigned board, bool singleSolution, bool addConflicts, bool pureSAT, bool withTheory, bool withDecide, bool hybrid);

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
    return nqueensPropagator(*num, false, false, false, false, true, false);
}

inline int nqueensPropagator1(unsigned* num) {
    return nqueensPropagator(*num, false, true, true, false, false, false);
}

inline int nqueensPropagator2(unsigned *num) {
    return nqueensPropagator(*num, false, true, false, false, false, false);
}

inline int nqueensPropagator3(unsigned *num) {
    return nqueensPropagator(*num, false, true, false, true, false, false);
}

inline int nqueensPropagator4(unsigned* num) {
    return nqueensPropagator(*num, false, true, false, true, true, false);
}

inline int nqueensPropagator5(unsigned* num) {
    return nqueensPropagator(*num, false, true, true, true, false, false);
}

inline int nqueensPropagator6(unsigned* num) {
    return nqueensPropagator(*num, false, true, true, true, true, false);
}

inline int nqueensPropagator7(unsigned* num) {
    return nqueensPropagator(*num, false, true, false, true, true, true);
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
    unsigned start = 0;

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
        assert(line + start < inputs.size());
        return inputs[line + start].back();
    }

    z3::expr getValue(unsigned line, unsigned pos) const {
        assert(line + start < inputs.size());
        assert(pos < inputs[line].size());
        return inputs[line + start][pos];
    }

    unsigned getCurrentLineSize(unsigned line) {
        assert(line + start < inputs.size());
        return (unsigned)inputs[line + start].size();
    }

    void add(unsigned line, const z3::expr& expr) {
        assert(line + start < inputs.size());
        inputs[line + start].push_back(expr);
    }

    void addComparision(unsigned line1, unsigned line2) {
        assert(line1 + start < inputs.size());
        assert(line2 + start < inputs.size());
        const auto v1 = getCurrentLineValue(line1);
        const auto v2 = getCurrentLineValue(line2);
        add(line1, z3::ite(z3::ule(v1, v2), v1, v2));
        add(line2, z3::ite(!z3::ule(v1, v2), v1, v2));
    }

    z3::expr_vector getInputs() const {
        z3::expr_vector in(ctx);
        for (const auto& v : inputs) {
            in.push_back(v[0]);
        }
        return in;
    }

    z3::expr_vector getOutputs() const {
        z3::expr_vector out(ctx);
        for (const auto& v : inputs) {
            out.push_back(v.back());
        }
        return out;
    }

    z3::expr_vector getCurrentOutputs() const {
        z3::expr_vector out(ctx);
        for (unsigned i = start; i < inputs.size(); i++) {
            out.push_back(inputs[i].back());
        }
        return out;
    }

	void increase(unsigned size) {
        start = inputs.size();
        for (unsigned i = 0; i < size; i++) {
            inputs.emplace_back();
        }
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

    unsigned size() const {
        return inputs.size();
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

    void merge(const symbolicNetwork& network) {
        inputs.reserve(inputs.size() + network.inputs.size());
        unsigned start = inputs.size();
        for (unsigned i = 0; i < network.inputs.size(); i++) {
            inputs.emplace_back();
            for (unsigned j = 0; j < network.inputs[i].size(); j++) {
                const destination& cur = network.inputs[i][j];
                destination dest { .line = cur.line + start, .position = cur.position };
                inputs.back().push_back(dest);
            }
        }
    }
};