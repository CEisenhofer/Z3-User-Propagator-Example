#if defined(WIN32) || defined(_WIN32) || defined(__WIN32__) || defined(__NT__)
#define WINDOWS
#include <Windows.h>
#include <conio.h>
#define getch() _getch()
#else
#include <termios.h>
#include <stdio.h>

static struct termios old, current;

char getch() {
    char ch;
    tcgetattr(0, &old);
    current = old;
    current.c_lflag &= ~ICANON;
    if (echo) {
        current.c_lflag |= ECHO;
    }
    else {
        current.c_lflag &= ~ECHO;
    }
    tcsetattr(0, TCSANOW, &current);
    ch = getchar();
    tcsetattr(0, TCSANOW, &old);
    return ch;
}

#endif


#include "user_propagator.h"
#include "user_propagator_with_theory.h"
#include "user_propagator_subquery_maximisation.h"
#include "user_propagator_internal_maximisation.h"
#include "user_propagator_created_maximisation.h"
#include "big_num.h"

#define REPETITIONS 1

#define MIN_BOARD 14
#define MAX_BOARD1 15
#define MAX_BOARD2 14

#define MIN_BOARD_SINGLE 5
#define MAX_BOARD_SINGLE 60
#define BOARD_SINGLE_INC 5

#define SORT_CNT 128

#define DISTINCT_CNT 32

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

void printResultVector(std::vector<double> results) {
    // For copying to Mathematica
    std::cout << "{ " << results[0];
    for (unsigned i = 1; i < results.size(); i++) {
        std::cout << ", " << results[i];
    }
    std::cout << " }" << std::endl;
}

std::vector<std::vector<double>> benchmarkResults;

void printResults() {
    for (int i = 0; i < benchmarkResults.size(); i++)
        printResultVector(benchmarkResults[i]);
}

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

    std::cout << "\n" << interestingKeys[0] << " = " << values[0];
    for (unsigned i = 1; i < values.size(); i++) {
        std::cout << ", " << interestingKeys[i] << " = " << values[i];
    }
    std::cout << std::endl;

    std::cout << "{ " << values[0];

    for (unsigned i = 1; i < values.size(); i++) {
        std::cout << ", " << values[i];
    }

    std::cout << " }" << std::endl;

    //std::cout << "Stats: " << Z3_stats_to_string(s.ctx(), stats) << std::endl;

}

void benchmark(unsigned args[], const benchark_fct* testFcts, const char** testNames, unsigned cnt) {
    unsigned seed = (unsigned)high_resolution_clock::now().time_since_epoch().count();
    auto e = std::default_random_engine(seed);
    std::vector<int> permutation;
    for (unsigned i = 0; i < cnt; i++)
        permutation.push_back(i);

    std::vector<std::vector<double>> timeResults;
    for (unsigned i = 0; i < cnt; i++) {
        timeResults.emplace_back();
    }

    benchmarkResults.emplace_back();

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
            int res = testFcts[i](args);
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

    for (unsigned i = 0; i < cnt; i++) {
        std::cout << testNames[i];
        double sum = 0;
        for (int j = 0; j < REPETITIONS; j++) {
            std::cout << " " << timeResults[i][j] << "ms";
            sum += timeResults[i][j];
        }
        std::cout << " | avg: " << sum / REPETITIONS << "ms" << std::endl;
        benchmarkResults.back().push_back(sum / REPETITIONS);
    }

    std::cout << std::endl;
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

void testNQueens(double perc = 1.0) {
    benchmarkResults.clear();
    std::cout << "#n-Queens:" << std::endl;
    constexpr int solutions[] =
        { 0, 0, 0, 0, 2, 10, 4, 40, 92, 352, 724, 2680, 14200, 73712, 365596, 2279184 };

    for (unsigned num = MIN_BOARD; num <= MAX_BOARD1; num++) {

        std::cout << "num = " << num << ":\n" << std::endl;

        const benchark_fct testFcts[] = {
                //nqueensNoPropagator2,
                //nqueensNoPropagator3,
                //nqueensNoPropagator1,
                //nqueensPropagator2,
                nqueensPropagator1,
                nqueensPropagator8,
                //nqueensPropagator3,
                //nqueensPropagator4,
                nqueensPropagator5,
                //nqueensPropagator6,
                //nqueensPropagator7,
        };
        const char *testNames[] = {
                //"Eager BV + Blocking clauses",
                //"Eager BV + Blocking clauses + Useless Propagator",
                //"Eager Bool + Blocking clauses",
                //"Eager BV + final conflicts",
                "Eager Bool + final conflicts",
                "Eager Bool + final conflicts + decide",
                //"Lazy BV theory + final conflicts",
                //"Lazy BV theory + final conflicts + ordered",
                "Lazy Bool theory + final conflicts",
                //"Lazy Bool theory + final conflicts + decide",
                //"Hybrid BV theory + final conflicts",
        };
        static_assert(SIZE(testFcts) == SIZE(testNames));

        unsigned args[2];
        args[0] = num;
        args[1] = (unsigned)ceil(perc * solutions[num]);

        benchmark(args, testFcts, testNames, SIZE(testFcts));
        isPrintStatistics = false;
    }
}

void testSingleNQueens() {
    benchmarkResults.clear();
    std::cout << "n-Queens:" << std::endl;
    
    for (unsigned num = MIN_BOARD_SINGLE; num <= MAX_BOARD_SINGLE; num += BOARD_SINGLE_INC) {

        std::cout << "num = " << num << ":\n" << std::endl;

        const benchark_fct testFcts[] = {
                [](unsigned* num) { return nqueensPropagator(*num, true, false, false, false, false, false, -1); },
                [](unsigned* num) { return nqueensPropagator(*num, true, false, true, false, false, false, -1); },
                [](unsigned* num) { return nqueensPropagator(*num, true, false, true, false, 1, false, -1); },
                //[](unsigned* num) { return nqueensPropagator(*num, true, false, true, false, 2, false, -1); },

                [](unsigned* num) { return nqueensPropagator(*num, true, false, false, true, false, false, -1); },
                [](unsigned* num) { return nqueensPropagator(*num, true, false, true, true, false, false, -1); },
                [](unsigned* num) { return nqueensPropagator(*num, true, false, true, true, 1, false, -1); },
                //[](unsigned* num) { return nqueensPropagator(*num, true, false, true, true, 2, false, -1); },
        };
        const char* testNames[] = {
                "Eager BV",
                "Eager Bool",
                "Eager Bool + decide",
                //"Eager Bool + decide (neg)",

                "Lazy BV",
                "Lazy Bool",
                "Lazy Bool + decide",
                //"Lazy Bool + decide (neg)",
        };
        static_assert(SIZE(testFcts) == SIZE(testNames));
        if (num == MAX_BOARD_SINGLE)
            isPrintStatistics = true;

        benchmark(&num, testFcts, testNames, SIZE(testFcts));
        isPrintStatistics = false;
    }
}

void testNQueensOptimization() {
    benchmarkResults.clear();
    z3::set_param("smt.ematching", "false");
    z3::set_param("smt.mbqi", "true");

    std::cout << "\nMaximal distance:" << std::endl;

    for (unsigned num = MIN_BOARD; num <= MAX_BOARD2; num++) {

        std::cout << "num = " << num << ":\n" << std::endl;

        const benchark_fct testFcts[] = {
            [](unsigned num[]) { return nqueensMaximization1(num); },
            [](unsigned num[]) { return nqueensMaximization2(num); },
            [](unsigned num[]) { return nqueensMaximization3(num); },
            [](unsigned num[]) { return nqueensMaximization4(num); }
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
    benchmarkResults.clear();
    std::cout << "Distinctness:" << std::endl;

    for (unsigned num = 4; num <= DISTINCT_CNT; num <<= 1) {

        std::cout << "num = " << num << ":\n" << std::endl;

        unsigned args[2];
        const benchark_fct testFcts[] = {
                [](unsigned args[]) { return distinct1(args[0], args[1]); },
                [](unsigned args[]) { return distinct2(args[0], args[1]); },
                [](unsigned args[]) { return distinct3(args[0], args[1]); },
                [](unsigned args[]) { return distinct4(args[0], args[1]); }
        };
        const char *testNames[] = {
                "Distinct-O(n^2)",
                "Bijection-O(n^2)",
                "Distinct-Propagator",
                "Bijection-Propagator",
        };
        unsigned bits = log2i(num);
        static_assert(SIZE(testFcts) == SIZE(testNames));
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

int disjointnessPairs(unsigned size) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    z3::expr_vector in(context);

    for (unsigned i = 0; i < size; i++) {
        in.push_back(context.bv_const(("in_" + std::to_string(i)).c_str(), BIT_CNT));
    }

    constexpr unsigned bits = BIT_CNT;

    for (unsigned i = 0; i < size; i++) {
        z3::expr size1 = in[i].extract(bits / 2 - 1, 0);
        z3::expr addr1 = in[i].extract(bits - 1, bits / 2);
        for (unsigned j = i + 1; j < size; j++) {
            z3::expr size2 = in[j].extract(bits / 2 - 1, 0);
            z3::expr addr2 = in[j].extract(bits - 1, bits / 2);
            s.add(z3::ule(z3::zext(addr1, 1) + z3::zext(size1, 1), z3::zext(addr2, 1)) || z3::ule(z3::zext(addr2, 1) + z3::zext(size2, 1), z3::zext(addr1, 1)));
        }
    }

    s.check();
    z3::model m = s.get_model();

    std::vector<unsigned> v;
    for (unsigned i = 0; i < in.size(); i++) {
        v.push_back(m.eval(in[i]).get_numeral_uint());
    }
    unsigned mask = (unsigned)-1;
    mask >>= ((sizeof(unsigned) * 8) - (bits / 2));

    for (unsigned i = 0; i < v.size(); i++) {
        const unsigned size1 = v[i] & mask;
        const unsigned addr1 = (v[i] >> (bits / 2)) & mask;

        for (unsigned j = i + 1; j < v.size(); j++) {

            const unsigned size2 = v[j] & mask;
            const unsigned addr2 = (v[j] >> (bits / 2)) & mask;
            if (!(addr1 + size1 <= addr2 || addr2 + size2 <= addr1)) {
                exit(15);
            }
        }
    }

    return -1;
}

void testDisjointness() {
    benchmarkResults.clear();
    std::cout << "Disjointness:" << std::endl;

    for (unsigned num = 2; num <= SORT_CNT; num <<= 1) {

        std::cout << "num = " << num << ":\n" << std::endl;

        const benchark_fct testFcts[] = {
            [](unsigned num[]) { return sorting4(num[0], intervals); },
            [](unsigned num[]) { return sorting7(num[0], intervals); },
            [](unsigned num[]) { return sorting9(num[0]); },
            [](unsigned num[]) { return disjointnessPairs(num[0]); },
        };
        const char* testNames[] = {
            "Insertion-Sort Network",
            "Odd-Even Sorting Network",
            "On-demand Network",
            "Eager pairs",
        };
        static_assert(SIZE(testFcts) == SIZE(testNames));
        benchmark(&num, testFcts, testNames, SIZE(testFcts));
    }
}

void testSorting() {
    benchmarkResults.clear();
    std::cout << "Sorting:" << std::endl;

    for (unsigned num = 2; num <= SORT_CNT; num <<= 1) {

        std::cout << "num = " << num << ":\n" << std::endl;

#define CONSTRAINT (sortingConstraints)(intervals)

        const benchark_fct testFcts[] = {
                //[](unsigned num[]) { return sorting1(num[0], CONSTRAINT); },
                //[](unsigned num[]) { return sorting2(num[0], CONSTRAINT); },
                //[](unsigned num[]) { return sorting3(num[0], CONSTRAINT); },
                //[](unsigned num[]) { return sorting4(num[0], CONSTRAINT); },
                //[](unsigned num[]) { return sorting5(num[0], CONSTRAINT,false); },
                //[](unsigned num[]) { return sorting5(num[0], CONSTRAINT,true); },
                [](unsigned num[]) { return sorting6(num[0], CONSTRAINT); },
                [](unsigned num[]) { return sorting7(num[0], CONSTRAINT); },
                //[](unsigned num[]) { return sorting8(num[0], CONSTRAINT, false); },
                [](unsigned num[]) { return sorting8(num[0], CONSTRAINT, true); },
                //[](unsigned num[]) { return sorting10(num[0], CONSTRAINT); },
                [](unsigned num[]) { return sorting11(num[0], CONSTRAINT); },
                [](unsigned num[]) { return sorting12(num[0], CONSTRAINT); },
                [](unsigned num[]) { return sorting13(num[0], CONSTRAINT); },
                [](unsigned num[]) { return sorting14(num[0], CONSTRAINT); },
        };
        const char *testNames[] = {
                //"Merge-Sort (BMC)",
                //"Direct Sort (Predicate)",
                //"Direct Sort (Function)",
                //"Insertion-Sort Network",
                //"Lazy Insertion-Sort Network",
                //"Lazy Insertion-Sort Network (Persistent)",
                "Permutation",
                "Odd-Even Sorting Network",
                //"Lazy Odd-Even Sorting Network",
                "Lazy Odd-Even Sorting Network (Persistent)",
                //"Matching",
                "Bijection",
                "Lazy Bijection",
                "Bijection Numeric",
                "Lazy Bijection Numeric",
        };
        static_assert(SIZE(testFcts) == SIZE(testNames));
        benchmark(&num, testFcts, testNames, SIZE(testFcts));
    }
}

struct Test: z3::user_propagator_base {

    z3::expr_vector v;
    int r[15];
    int assigned = 0;

    Test(z3::solver* s) : user_propagator_base(s), v(ctx()) {
        this->register_fixed();
        this->register_final();
        this->register_decide();
        this->register_eq();
        Z3_solver_propagate_diseq(ctx(), *s, diseq_eh);

        z3::expr unregistered = ctx().bool_const("unregistered");
        z3::expr a = ctx().bool_const("a");
        z3::expr b = ctx().bool_const("b");
        z3::expr c = ctx().bool_const("c");
        z3::expr d = ctx().bv_const("d", 3);
        z3::expr e = ctx().bv_const("e", 3);
        z3::expr g = ctx().bool_const("g");
        z3::expr h = ctx().bool_const("h");
        z3::expr x = ctx().int_const("x");
        z3::expr y = ctx().int_const("y");
        z3::expr z = ctx().int_const("z");

        srand((unsigned)time(nullptr));

        for (int i = 0; i < 15; i++) {
            r[i] = i;
        }

        for (int i = 0; i < 15; i++) {
            const int swp = rand() % 15;
            const int tmp = r[i];
            r[i] = r[swp];
            r[swp] = tmp;
        }
        for (int i = 0; i < 15; i++) {
            v.push_back(ctx().bool_const(("v" + std::to_string(i)).c_str()));
            this->add(v.back());
            std::cout << "v" << r[i] << std::endl;
        }
        s->add(z3::mk_or(v));

        //z3::sort_vector domain(ctx());
        //domain.push_back(ctx().int_sort());
        //z3::func_decl f = ctx().function(ctx().str_symbol("f"), domain, domain.back());
        //s->add(((a || b) || c || unregistered || x + y == 2) && d == e && f == g && y != x && z >= x && z <= x);
        /*s->add(x >= 2);
        s->add(a || b);
        s->add(g || h);
        this->add(a);
        this->add(b);
        std::cout << (a || b).simplify().to_string() << std::endl;
        std::cout << (g || h).simplify().to_string() << std::endl;
        this->add(g);
        this->add(h);*/
        //s->add((z >= x && z <= x) || (y >= z && y <= z) || (x >= z && x <= z) && f(x) > 0 && f(y) > 0 && f(z) > 0 && f(z) != z);
        //this->add(f(x));
        //this->add(f(y));
        //this->add(f(z));

        //s->add(a || b);
        /*this->add(a);
        this->add(b);
        this->add(c);
        this->add(a || b);
        this->add(d);
        this->add(e);
        this->add(d == e);
        this->add(g);
        this->add(h);
        this->add(x + y == 2);*/
        /*this->add(x);
        this->add(y);
        this->add(z);*/

        /*for (unsigned i = 0; i < 10; i++) {
            z3::expr z = ctx().bool_const(("z" + std::to_string(i + 1)).c_str());
            this->add(z);
            s->add(z);
        }*/
    }

    void final() override {
        //z3::expr_vector empty(ctx());
        //this->propagate(empty, !ctx().bool_const("g"));
        //this->propagate(empty, !ctx().bool_const("h"));
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
        is_pos = (rand() & 1) == 1 ? Z3_L_TRUE : Z3_L_FALSE;
        bit = 0;
        if (assigned < 14) {
            this->next_split(v[r[++assigned]], 0, (rand() & 1) == 1 ? Z3_L_TRUE : Z3_L_FALSE);
        }
    }

    void eq(z3::expr const& lhs, z3::expr const& rhs) override {
        std::cout << "Eq " + lhs.to_string() + " = " + rhs.to_string() << std::endl;
    }

    static void diseq_eh(void* _p, Z3_solver_callback cb, Z3_ast _x, Z3_ast _y) {
        Test* p = static_cast<Test*>(_p);
        z3::expr x(p->ctx(), _x), y(p->ctx(), _y);
        std::cout << "Diseq " + x.to_string() + " != " + y.to_string() << std::endl;
    }

    user_propagator_base* fresh(z3::context& ctx) override {
        return this;
    }

};

const std::initializer_list<benchark_fct> optSortingFcts = {
    //[](unsigned a[]) { return opt_sorting(a, Params(false, false, false, false, false, false, false, false, false, None)); },
    //[](unsigned a[]) { return opt_sorting(a, Params(true , false, false, true , false, false, false, MinimalModel)); },
    //[](unsigned a[]) { return opt_sorting(a, Params(true , false, false, true , false, false, false, CompleteModel)); },
    [](unsigned a[]) { return opt_sorting(a, Params(true , false, false, true , false, false, false, (InstantiationStrategy)(MinimalModel | Repropagate))); },
    [](unsigned a[]) { return opt_sorting(a, Params(true , false, false, true , false, false, false, (InstantiationStrategy)(CompleteModel | Repropagate))); },
    //[](unsigned a[]) { return opt_sorting(a, Params(true , false, false, true , false, false, false, (InstantiationStrategy)(NearlyCompleteModel | Repropagate))); },
    //[](unsigned a[]) { return opt_sorting(a, Params(true , false, false, true , false, false, false, (InstantiationStrategy)(MinimalModel | CompleteModel | Repropagate))); },
    //[](unsigned a[]) { return opt_sorting(a, Params(true , false, false, true , false, false, false, (InstantiationStrategy)(CompleteModel | Restart | Repropagate))); },
    [](unsigned a[]) { return opt_sorting(a, Params(true , false, false, true , false, false, false, (InstantiationStrategy)(Randomized))); },
    [](unsigned a[]) { return opt_sorting(a, Params(true , false, false, true , false, false, false, None)); },
    [](unsigned a[]) { return opt_sorting(a, Params(true , true , false, true , false, false, false, None)); },
    [](unsigned a[]) { return opt_sorting(a, Params(true , true , true , true , false, false, false, None)); },
    [](unsigned a[]) { return opt_sorting(a, Params(true , true , true , true , false, false, false, CompleteModel)); },
    //[](unsigned a[]) { return opt_sorting(a, Params(true , false, false, true , true , false, false, false, false, None)); },
    //[](unsigned a[]) { return opt_sorting(a, Params(true , false, false, true , true , true , false, false, false, None)); },
};

const std::initializer_list<const char*> optSortingNames = {
    //"Nothing",
    //"Adjacent + Simulated Quantifier + Minimal Model",
    //"Adjacent + Simulated Quantifier + Complete Model",
    // "Adjacent + Simulated Quantifier + Minimal Model (Rep)",
    // "Adjacent + Simulated Quantifier + Complete Model (Rep)",
    //"Adjacent + Simulated Quantifier + Nearly Complete Model",
    //"Adjacent + Simulated Quantifier + Complete/Minimal Model",
    //"Adjacent + Simulated Quantifier + Complete Model + Restart",
    // "Adjacent + Randomized",
    // "Adjacent",
    // "Adjacent + Decide",
    // "Adjacent + Decide + Occurrence",
    "Adjacent + Decide + Occurrence + Complete Model",
    //"Adjacent + Connected",
    //"Adjacent + Connected (All)",
};

void findOptimalUnsat() {
    unsigned int _args[] = { 3, 1, (unsigned)false };
    benchmark(
        _args,
        optSortingFcts,
        optSortingNames
    );
}

void findOptimalSat(int start = 0) {
    unsigned solutions[] = {0, 0, 1, 3, 5, 9, 12, 16, 19, 25, 29, 35, 39 };
    unsigned _args[] = { 0, 0, (unsigned)false };
    for (unsigned i = std::max(3, start); i < SIZE(solutions); i++) {
        std::cout << "Size " << i << ":" << std::endl;
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
    opt_sorting(args, Params(true, true, true, true, true, true, true, None));
}

int main() {

    z3::set_param("smt.mbqi.max_iterations", 100000000);
    z3::set_param("smt.relevancy", 0);

#ifdef WINDOWS
    CONSOLE_SCREEN_BUFFER_INFO csbi = {};
    HANDLE con = GetStdHandle(STD_OUTPUT_HANDLE);
    GetConsoleScreenBufferInfo(con, &csbi);
    csbi.dwSize.Y = SHRT_MAX - 1;
    SetConsoleScreenBufferSize(con, csbi.dwSize);
#endif
    /*
    z3::set_param("rewriter.blast_eq_value", true);
    z3::set_param("smt.phase_selection", 5); // random

    const benchark_fct testFcts[] = {
            [](unsigned args[]) { return distinct1(1000, 32); },
            [](unsigned args[]) { return distinct3(1000, 32); },
    };
    const char* testNames[] = {
            "Distinct-O(n^2)",
            "Distinct-Propagator",
    };
    
    static_assert(SIZE(testFcts) == SIZE(testNames));

    isPrintStatistics = true;
    benchmark(nullptr, testFcts, testNames, 2);
    //testDistinctness();
    getch();
    
    testNQueens();
    getch();*/

    z3::set_param("rewriter.blast_eq_value", true);
    z3::set_param("smt.phase_selection", 5); // random

    testNQueens();
    /*printResults();
    getch();
    getch();
    getch();*/
    /*getch();
    testSingleNQueens();
    printResults();
    getch();*/

    //findOptimalSat();
    /*unsigned solutions[] = { 0, 0, 1, 3, 5, 9, 12, 16, 19, 25, 29, 35, 39 };
    unsigned __args[] = { 0, 0, (unsigned)true };
    __args[0] = 5;
    __args[1] = 6;
    benchmark(
        __args,
        optSortingFcts,
        optSortingNames
    );
    __args[1] = 7;
    benchmark(
        __args,
        optSortingFcts,
        optSortingNames
    );
    std::cout << "Done" << std::endl;
    getch();*/

    //getch();
    //testDisjointness();
    z3::set_param("rewriter.blast_eq_value", false);
    //testSorting();
    getch();

    //unsigned _args[] = { 6, 1, (unsigned)false };

    // sorting2(_args);
    // sorting3(_args);
    // sorting4(_args);
    // sorting5(_args);
    // sorting6(_args);
    /*std::cout << "Optimal sorting network of size " << _args[0] << ": \n" << 
        opt_sorting(_args, Params(true, false, false, false, true, true, true, false, true))
    << std::endl;*/
    findOptimalSat(11);
    std::cout << "Done" << std::endl;
    getch();
    //testDistinctness();
    //testNQueens();
    //testSingleNQueens();
    //std::cout << "Results:\n\n";
    //printResults();

    getch();

    z3::context _ctx;
    z3::solver _s(_ctx, z3::solver::simple());
    Test t(&_s);
    _s.check();
    std::cout << _s.get_model() << std::endl;

    /*z3::sort_vector vec(_ctx);
    vec.push_back(_ctx.bv_sort(3));
    z3::func_decl f = _ctx.function("f", vec, vec.back());
    z3::expr x = _ctx.constant("x", vec.back());
    z3::expr y = _ctx.constant("y", vec.back());
    _s.add(f(x) != f(y));
    _s.add(x + y == 0);*/
    /*_s.add(_ctx.int_const("x") == -_ctx.int_const("y"));
    _s.add(_ctx.int_const("y") == -_ctx.int_const("z"));
    _s.add(_ctx.int_const("x") != _ctx.int_const("z"));*/
    z3::expr x = _ctx.bv_const("x", 3);
    z3::expr y = _ctx.bv_const("y", 3);
    //z3::expr z = _ctx.bool_const("z");
    //z3::expr z = _ctx.bv_const("z", 3);
    //_s.add(x == 0 || z3::forall(y, x * y == y));
    //_s.add(x > 0);
    //_s.add(z && z == z3::forall(y, x * y == y));
    //_s.add(z3::exists(x, z3::forall(y, z3::exists(z, x * y == z))));
    _s.add(x == y);
    std::cout << "Asserted: " << _s.assertions().to_string() << std::endl;
    _s.check();
    std::cout << "Asserted: " << _s.assertions().to_string() << std::endl;
    std::cout << _s.get_model().to_string() << std::endl;

    // z3::set_param("smt.bv.eq_axioms", false);

    //getch();
    testSorting();

    getch();
    //testSingleNQueens();
    //testNQueens();
    getch();

    //findAllOptimalSolutions(5);
    findOptimalSat();
    //findOptimalUnsat();
    getch();
    getch();

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