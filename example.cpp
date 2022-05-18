#if defined(WIN32) || defined(_WIN32) || defined(__WIN32__) || defined(__NT__)
#define WINDOWS
#include <Windows.h>
#include <conio.h>
#define getch() _getch()
#else
#define getch() exit(9)
#endif


#include "user_propagator.h"
#include "user_propagator_with_theory.h"
#include "user_propagator_subquery_maximisation.h"
#include "user_propagator_internal_maximisation.h"
#include "user_propagator_created_maximisation.h"
#include "big_num.h"
// #include "interval_tree.hpp"

/**
 * The program solves the n-queens problem (number of solutions) with 4 different approaches
 * 1) Bit-Vector constraints + Default solver + Blocking Clauses
 * 2) Bit-Vector constraints + Simple solver + Blocking Clauses
 * 3) Bit-Vector constraints + Simple solver + Adding contradictions in the propagator
 * 4) Constraints only implicit via the propagator + Simple solver + Adding contradictions in the propagator
 *
 * Runs 1 + 2 are done for comparison with 3 + 4
 */

typedef int (*benchark_fct)(unsigned[]);

bool isPrintStatistics = false;

void printStatistics(z3::solver& s) {
    if (!isPrintStatistics)
        return;

    const std::string interestingKeys[] {
        "conflicts",
        "decisions",
        "del clause",
        "final checks",
        "memory",
        "mk bool var",
        "mk clause",
        "propagations",
        "user-propagations"
    };

    z3::stats stats = s.statistics();

    std::vector<double> values;
    values.resize(SIZE(interestingKeys), 0.0);

    const unsigned size = stats.size();

    for (unsigned i = 0; i < size; i++) {
        const std::string key = stats.key(i);
        for (unsigned j = 0; j < values.size(); j++) {
            if (key == interestingKeys[j]) {
                if (stats.is_double(i))
                    values[j] = stats.double_value(i);
                else if (stats.is_uint(i))
                    values[j] = (double)stats.uint_value(i);
                else
                    assert(false);
                break;
            }
        }
    }

    for (unsigned i = 0; i < values.size(); i++) {
        std::cout << interestingKeys[i] << ": " << values[i] << std::endl;
    }

    std::cout << "{ " << values[0];

    for (unsigned i = 1; i < values.size(); i++) {
        std::cout << ", " << values[i];
    }

    std::cout << " }" << std::endl;

    //std::cout << "Stats: " << Z3_stats_to_string(s.ctx(), stats) << std::endl;

}

void benchmark(unsigned *arg, const benchark_fct *testFcts, const char **testNames, unsigned cnt) {
    unsigned seed = (unsigned)high_resolution_clock::now().time_since_epoch().count();
    auto e = std::default_random_engine(seed);
    std::vector<int> permutation;
    for (unsigned i = 0; i < cnt; i++)
        permutation.push_back(i);

    std::vector<std::vector<double>> timeResults;
    for (unsigned i = 0; i < cnt; i++) {
        timeResults.emplace_back();
    }

    for (int rep = 0; rep < REPETITIONS; rep++) {
#ifdef RANDOM_SHUFFLE
        // Execute strategies in a randomised order
        std::shuffle(permutation.begin(), permutation.end(), e);
#endif
        unsigned random_seed = e() % 100000;
        std::cout << "Random seed: " << random_seed << std::endl;

        for (int i: permutation) {

            z3::set_param("sat.random_seed", (int)random_seed);
            z3::set_param("smt.random_seed", (int)random_seed);
            auto now1 = high_resolution_clock::now();
            int res = testFcts[i](arg);
            auto now2 = high_resolution_clock::now();
            duration<double, std::milli> ms = now2 - now1;
            std::cout << testNames[i] << " took " << ms.count() << "ms";
            if (res != -1) {
                std::cout << " (" << res << ")";
            }
            std::cout << std::endl;
            timeResults[i].push_back(ms.count());
            WriteLine("-------------");
        }
    }

    std::cout << "\n" << std::endl;

    std::vector<double> results;

    for (unsigned i = 0; i < cnt; i++) {
        std::cout << testNames[i];
        double sum = 0;
        for (int j = 0; j < REPETITIONS; j++) {
            std::cout << " " << timeResults[i][j] << "ms";
            sum += timeResults[i][j];
        }
        std::cout << " | avg: " << sum / REPETITIONS << "ms" << std::endl;
        results.push_back(sum / REPETITIONS);
    }

    std::cout << std::endl;

    // For copying to Mathematica
    std::cout << "{ " << results[0];
    for (unsigned i = 1; i < results.size(); i++) {
        std::cout << ", " << results[i];
    }
    std::cout << " }" << std::endl;
}

void benchmark(unsigned* arg, const std::initializer_list<benchark_fct> testFcts, const std::initializer_list<const char*> testNames) {
    std::vector<const char*> names;
    std::vector<benchark_fct> fcts;
    names.reserve(testNames.size());
    fcts.reserve(testNames.size());
    for (const auto& name : testNames) {
        names.push_back(name);
    }
    for (const auto& fct: testFcts) {
        fcts.push_back(fct);
    }
    return benchmark(arg, fcts.data(), names.data(), (unsigned)testNames.size());
}

void testNQueens() {
    std::cout << "#n-Queens:" << std::endl;

    for (unsigned num = MIN_BOARD; num <= MAX_BOARD1; num++) {

        std::cout << "num = " << num << ":\n" << std::endl;

        const benchark_fct testFcts[] = {
                nqueensNoPropagator1,
                nqueensNoPropagator2,
                nqueensNoPropagator3,
                nqueensPropagator1,
                nqueensPropagator2
                //nqueensPropagator3,
        };
        const char *testNames[] = {
                "BV + Blocking clauses (Default solver)",
                "BV + Blocking clauses (Simple solver)",
                "BV + Blocking clauses + Useless Propagator",
                "BV + Adding conflicts",
                "Custom theory + conflicts",
                //"Custom theory + conflicts + ordered",
        };
        static_assert(SIZE(testFcts) == SIZE(testNames));
        if (num == 11)
            isPrintStatistics = true;
        benchmark(&num, testFcts, testNames, SIZE(testFcts));
        isPrintStatistics = false;
    }
}

void testSingleNQueens() {
    std::cout << "n-Queens:" << std::endl;

    for (unsigned num = MIN_BOARD; num <= MAX_BOARD1; num++) {

        std::cout << "num = " << num << ":\n" << std::endl;

        const benchark_fct testFcts[] = {
                [](unsigned* num) { return nqueensPropagator(*num, true, false, false, false); },
                [](unsigned* num) { return nqueensPropagator(*num, true, false, true, false); },
        };
        const char* testNames[] = {
                "BV + Adding conflicts",
                "Custom theory + conflicts",
        };
        static_assert(SIZE(testFcts) == SIZE(testNames));
        if (num == 50)
            isPrintStatistics = true;
        benchmark(&num, testFcts, testNames, SIZE(testFcts));
        isPrintStatistics = false;
    }
}

void testNQueensOptimization() {
    z3::set_param("smt.ematching", "false");
    z3::set_param("smt.mbqi", "true");

    std::cout << "\nMaximal distance:" << std::endl;

    for (unsigned num = MIN_BOARD; num <= MAX_BOARD2; num++) {

        std::cout << "num = " << num << ":\n" << std::endl;

        const benchark_fct testFcts[] = {
                nqueensMaximization1,
                nqueensMaximization2,
                nqueensMaximization3,
                nqueensMaximization4,
        };
        const char *testNames[] = {
                "Ordinary/Direct Encoding",
                "SubQuery in final",
                "Assert Smaller in final",
                "created",
        };
        static_assert(SIZE(testFcts) == SIZE(testNames));
        benchmark(&num, testFcts, testNames, SIZE(testFcts));
    }
}

void testDistinctness() {
    std::cout << "Distinctness:" << std::endl;

    for (unsigned num = 4; num <= DISTINCT_CNT; num <<= 1) {

        std::cout << "num = " << num << ":\n" << std::endl;

        const benchark_fct testFcts[] = {
                distinct1,
                distinct2,
                distinct3,
                distinct4,
        };
        const char *testNames[] = {
                "Distinct-O(n^2)",
                "Bijection-O(n^2)",
                "Distinct-Propagator",
                "Bijection-Propagator",
        };
        unsigned bits = log2i(num);
        static_assert(SIZE(testFcts) == SIZE(testNames));
        unsigned args[2];
        args[0] = num;
        args[1] = (unsigned)std::min((int)num, 32); // enough space
        std::cout << "enough space\n" << std::endl;
        benchmark(args, testFcts, testNames, SIZE(testFcts));
        args[1] = bits; // 1 : 1
        std::cout << "1:1\n" << std::endl;
        benchmark(args, testFcts, testNames, SIZE(testFcts));
        if (bits > 1) {
            args[1] = bits - 1; // unsat
            std::cout << "not enough space\n" << std::endl;
            benchmark(args, testFcts, testNames, SIZE(testFcts));
        }
    }
}

void testSorting() {

    std::cout << "Sorting:" << std::endl;

    for (unsigned num = 2; num <= SORT_CNT; num <<= 1) {

        std::cout << "num = " << num << ":\n" << std::endl;
        const benchark_fct testFcts[] = {
                //sorting1,
                sorting2,
                //sorting3,
                sorting4,
                sorting5,
                //sorting6,
                sorting7,
                sorting8,
        };
        const char *testNames[] = {
                //"Merge-Sort (BMC)",
                "Direct Sort (Predicate)",
                //"Direct Sort (Function)",
                "Insertion-Sort Network",
                "Lazy Insertion-Sort Network",
                //"Permutation",
                "Odd-Even Sorting Network",
                "Lazy Odd-Even Sorting Network",
        };
        static_assert(SIZE(testFcts) == SIZE(testNames));
        benchmark(&num, testFcts, testNames, SIZE(testFcts));
    }
}

struct Test: z3::user_propagator_base {

    Test(z3::solver* s) : user_propagator_base(s) {
        this->register_fixed();
        this->register_decide();
        z3::expr unregistered = ctx().bool_const("unregistered");
        z3::expr a = ctx().bool_const("a");
        z3::expr b = ctx().bool_const("b");
        z3::expr c = ctx().bool_const("c");
        z3::expr d = ctx().bv_const("d", 3);
        z3::expr e = ctx().bv_const("e", 3);
        z3::expr x = ctx().int_const("x");
        z3::expr y = ctx().int_const("y");
        //s->add(((a || b) || c || unregistered /*|| x + y == 2*/) && d == e);
        s->add(a || b);
        //this->add(a);
        //this->add(b);
        //this->add(c);
        this->add(a || b);
        //this->add(d);
        //this->add(e);
        //this->add(d == e);
        //this->add(x + y == 2);
    }

    void push() override {
        std::cout << "Push" << std::endl;
    }

    void pop(unsigned int num_scopes) override {
        std::cout << "Pop: " << num_scopes << std::endl;
    }

    void fixed(const z3::expr& ast, const z3::expr& value) override {
        std::cout << "Fixed " + ast.to_string() + " to " + value.to_string() << std::endl;
    }

    void decide(z3::expr& val, unsigned& bit, Z3_lbool& is_pos) override {
        std::cout << "Decide: " + val.to_string() + 
            " bit: " + std::to_string(bit) + 
            " = " + (is_pos == Z3_L_FALSE ? "false" : "true") << std::endl;
        is_pos = Z3_L_TRUE;
        bit = 0;
    }

    user_propagator_base* fresh(z3::context& ctx) override { return this; }

};

const std::initializer_list<benchark_fct> optSortingFcts = {
    //[](unsigned* a) { return opt_sorting(a, Params(false, false, false, false, false, false, false, false, false)); },
    [](unsigned* a) { return opt_sorting(a, Params(true , false, false, false, false , false, false, true, false)); },
    //[](unsigned* a) { return opt_sorting(a, Params(true , false, false, false, true , false, false, false, false)); },
    //[](unsigned* a) { return opt_sorting(a, Params(true , false, false, false, true , false, true , false, false)); },
    //[](unsigned* a) { return opt_sorting(a, Params(true , false, false, false, true , true , true , false, false)); },
    //[](unsigned* a) { return opt_sorting(a, Params(true , false, false, false, true , true , true , true, false)); },
    //[](unsigned* a) { return opt_sorting(a, Params(true, true, false, false, true, true, true , false, false)); },
    //[](unsigned* a) { return opt_sorting(a, Params(true , true , true , false, true , true , true , false, false)); },
    //[](unsigned* a) { return opt_sorting(a, Params(true, true, false, true, true, true, true, false, false)); },
};

const std::initializer_list<const char*> optSortingNames = {
    //"Nothing",
    "Simulated Quantifier",
    //"Adjacent",
    //"Adjacent + Connected",
    //"Adjacent + Connected (All)",
    //"Adjacent + Connected (All) + Simulated Quantifier",
    //"Adjacent + Connected (All) + Decide",
    //"Adjacent + Connected (All) + Decide + Random",
    //"Adjacent + Connected (All) + Decide + Occurrences",
};

void findOptimalUnsat() {
    unsigned int _args[] = { 3, 1, (unsigned)false };
    benchmark(
        _args,
        optSortingFcts,
        optSortingNames
    );
}

void findOptimalSat() {
    unsigned solutions[] = {0, 0, 1, 3, 5, 9, 12, 16, 19, 25, 29, 35, 39 };
    unsigned _args[] = { 0, 0, (unsigned)false };
    for (unsigned i = 2; i < SIZE(solutions); i++) {
        _args[0] = i;
        _args[1] = solutions[i];
        benchmark(
            _args,
            optSortingFcts,
            optSortingNames
        );
    }
}

void findAllOptimalSolutions(unsigned sz) {
    unsigned args[] = { sz, 1, (unsigned)false };
    opt_sorting(args, Params(true, true, false, true, true, true, true, true, true));
}

int main() {

#ifdef WINDOWS
    CONSOLE_SCREEN_BUFFER_INFO csbi = {};
    HANDLE con = GetStdHandle(STD_OUTPUT_HANDLE);
    GetConsoleScreenBufferInfo(con, &csbi);
    csbi.dwSize.Y = SHRT_MAX - 1;
    SetConsoleScreenBufferSize(con, csbi.dwSize);
#endif

    //z3::context _ctx;
    //z3::solver _s(_ctx, z3::solver::simple());
    //Test t(&_s);
    //_s.check();

    // z3::set_param("smt.bv.eq_axioms", false);

    testSorting();

    _getch();
    //testSingleNQueens();
    //testNQueens();
    _getch();

    z3::set_param("smt.mbqi.max_iterations", 100000000);

    //findAllOptimalSolutions(5);
    //findOptimalSat();
    findOptimalUnsat();
    //getch();

    unsigned _args[] = { 5, 1, (unsigned)false };

    // sorting2(_args);
    // sorting3(_args);
    // sorting4(_args);
    // sorting5(_args);
    // sorting6(_args);
    // opt_sorting(_args, Params(true, true, false, true, true, true, true, false, false));
    getch();
    //std::cout << opt_sorting(_args, Params(true, true, false, false, true, true)) << std::endl;
    getch();

    std::cout << "Optimal sorting network of size " << _args[0] << ": \n" << opt_sorting(_args) << std::endl;
    
    exit(19);
    //sorting7(_args);
    testSorting();
    exit(14);
    
    unsigned int args[] = {5, 2};
    std::cout << nqueensHigherDimensionAllCover(args) << std::endl;
    exit(100);
    std::cout << "Starting" << std::endl;

    testSorting();
    exit(1);
    testDistinctness();

    // disjointness();

    /*BigNum a(1, 8);
    BigNum b(2, 8);
    std::cout << "1 - 2 = " << (a - b).toString() << std::endl;
    BigNum c(3, 8);
    std::cout << "1 - 3 = " << (a - c).toString() << std::endl;
    BigNum d((uint64_t)0, 8);
    std::cout << "3 - 0 = " << (c - d).toString() << std::endl;
    BigNum e(8, 8);
    std::cout << "8 - 1 = " << (e - a).toString() << std::endl;
    std::cout << "8 - 8 = " << (e - e).toString() << std::endl;
    std::cout << "8 - 3 = " << (e - c).toString() << std::endl;

    Interval toAdd(90, 100);
    toAdd.id = 0;

    Interval collision1(91, 100);
    collision1.id = 1;
    Interval collision2(90, 99);
    collision2.id = 2;
    Interval collision3(99, 100);
    collision3.id = 3;
    Interval collision4(90, 91);
    collision4.id = 4;
    Interval collision5(90, 100);
    collision5.id = 5;

    Interval collision1_(90, 91);
    collision1_.id = 10;
    Interval collision2_(99, 100);
    collision2_.id = 11;
    Interval collision3_(90, 99);
    collision3_.id = 13;
    Interval collision4_(91, 100);
    collision4_.id = 14;

    Interval noCollision1(0, 90);
    noCollision1.id = 21;
    Interval noCollision2(100, 200);
    noCollision2.id = 22;
    Interval noCollision3(0, 89);
    noCollision1.id = 23;
    Interval noCollision4(101, 200);
    noCollision2.id = 24;

    util::interval_tree<Interval> tree;

    std::vector<unsigned> collisions;
    tree.insert(collision1);
    assert(tree.size() == 1);
    tree.insert(collision2);
    assert(tree.size() == 2);
    tree.insert(collision3);
    assert(tree.size() == 3);
    tree.insert(collision4);
    assert(tree.size() == 4);
    tree.insert(collision5);
    assert(tree.size() == 5);
    // same elements; reverse order
    tree.insert(collision4_);
    assert(tree.size() == 6);
    tree.insert(collision3_);
    assert(tree.size() == 7);
    tree.insert(collision2_);
    assert(tree.size() == 8);
    tree.insert(collision1_);
    assert(tree.size() == 9);
    // no collision
    tree.insert(noCollision1);
    assert(tree.size() == 10);
    tree.insert(noCollision2);
    assert(tree.size() == 11);
    tree.insert(noCollision3);
    assert(tree.size() == 12);
    tree.insert(noCollision4);
    assert(tree.size() == 13);

    Interval intervals[] = {
            collision1, collision2, collision3, collision4, collision5,
            collision1_, collision2_, collision3_, collision4_,
            noCollision1, noCollision2,
    };

    int intersections = 0;
    for (int i = 0; i < SIZE(intervals); i++) {
        for (int j = i + 1; j < SIZE(intervals); j++) {
            if (intervals[i].overlaps(intervals[j]))
                intersections++;
        }
    }

    // assert(collisions.size() == intersections);
    collisions.clear();
    tree.overlap_find_all(toAdd, [&](auto iter) {
        collisions.push_back(iter->interval().id);
        return true;
    }, true);
    assert(collisions.size() == 9);*/

    testNQueens();
    testNQueensOptimization();
    exit(2);
}