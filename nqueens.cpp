#include "user_propagator_with_theory2.h"
#include "user_propagator_created_maximisation.h"
#include "user_propagator_internal_maximisation.h"
#include "user_propagator_subquery_maximisation.h"
#include "user_propagator_higher_dimension.h"

static z3::expr_vector createQueens(z3::context &context, unsigned board, int bits, std::string prefix) {
    z3::expr_vector queens(context);
    for (unsigned i = 0; i < board; i++) {
        queens.push_back(context.bv_const((prefix + "q" + to_string(i)).c_str(), bits));
    }
    return queens;
}

static z3::expr_vector createQueens(z3::context &context, unsigned board) {
    return createQueens(context, board, log2i(board) + 1, "");
}

static z3::expr_vector createTiles(z3::context& context, unsigned board) {
    z3::expr_vector queens(context);
    for (unsigned y = 0; y < board; y++) {
        for (unsigned x = 0; x < board; x++) {
            queens.push_back(context.bool_const(("q_{" + to_string(x) + "," + to_string(y) + "}").c_str()));
        }
    }
    return queens;
}

static z3::expr createConstraintsBV(z3::context &context, const z3::expr_vector &queens) {
    z3::expr_vector assertions(context);
    // assert column range
    for (unsigned i = 0; i < queens.size(); i++) {
        assertions.push_back(z3::uge(queens[i], 0));
        assertions.push_back(z3::ule(queens[i], (int)(queens.size() - 1)));
    }

    // no queens may attack vertically
    z3::expr_vector distinct(context);
    for (const z3::expr &queen: queens) {
        distinct.push_back(queen);
    }

    assertions.push_back(z3::distinct(distinct));

    // no queens may attack diagonally

    for (unsigned i = 0; i < queens.size(); i++) {
        for (unsigned j = i + 1; j < queens.size(); j++) {
            assertions.push_back((int)(j - i) != (queens[j] - queens[i]));
            assertions.push_back((int)(j - i) != (queens[i] - queens[j]));
        }
    }

    return z3::mk_and(assertions);
}


static z3::expr createConstraintsBool(z3::context& context, const z3::expr_vector& queens, const unsigned board) {

    assert(queens.size() == board * board);

    std::vector<z3::expr_vector> tiles;
    for (unsigned y = 0; y < board; y++) {
        tiles.emplace_back(context);
        for (unsigned x = 0; x < board; x++) {
            tiles.back().push_back(queens[x * board + y]);
        }
    }
    z3::expr_vector assertions(context);

    for (unsigned i = 0; i < board; i++) {
        // in every line at least one tile is occupied
        assertions.push_back(z3::mk_or(tiles[i]));

        // in every column at least one tile is occupied
        z3::expr_vector atLeastOne(context);
        for (unsigned j = 0; j < board; j++) {
            atLeastOne.push_back(tiles[j][i]);
        }
        assertions.push_back(z3::mk_or(atLeastOne));

        // in every line/column no two tiles are occupied
        for (unsigned j1 = 0; j1 < board; j1++) {
            for (unsigned j2 = j1 + 1; j2 < board; j2++) {
                assertions.push_back(!tiles[i][j1] || !tiles[i][j2]);
                assertions.push_back(!tiles[j1][i] || !tiles[j2][i]);
            }
        }
    }

    // no two queens may attack on a diagonal
    for (unsigned i = 0; i < 2 * board - 1; i++) {
        const unsigned x = i < board ? i : 0;
        const unsigned y = i >= board ? i - board + 1 : 0;

        const unsigned length = board - (i % board + i / board);

        for (unsigned j1 = 0; j1 < length; j1++) {
            for (unsigned j2 = j1 + 1; j2 < length; j2++) {
                assertions.push_back(!tiles[y + j1][x + j1] || !tiles[y + j2][x + j2]);
                assertions.push_back(!tiles[y + j1][board - 1 - x - j1] || !tiles[y + j2][board - 1 - x - j2]);
            }
        }
    }
    return z3::mk_and(assertions);
}

int enumerateSolutions(z3::context& context, z3::solver& solver, const z3::expr_vector& queens) {
    int solutionId = 0;
    
    while (true) {
        z3::check_result res = solver.check();

        if (res != z3::check_result::sat) {
            break;
        }

        z3::model model = solver.get_model();

        WriteLine("Model #" + to_string(solutionId) + ":");
        solutionId++;

        z3::expr_vector blocking(context);

        for (unsigned i = 0; i < queens.size(); i++) {
            z3::expr eval = model.eval(queens[i]);
            WriteLine(("q" + to_string(i) + " = " + to_string(eval.get_numeral_int())));
            /*for (int j = 0; j < queens[i].get_sort().bv_size(); j++) {
                bool b = (eval.get_numeral_int() >> j) & 1;
                blocking.push_back(b ? !queens[i].bit2bool(j) : queens[i].bit2bool(j));
            }*/
            blocking.push_back(queens[i] != eval);
        }

        solver.add(z3::mk_or(blocking));

        WriteEmptyLine;
    }

    printStatistics(solver);
    return solutionId;
}

int nqueensNoPropagatorSAT(unsigned board) {
    z3::context context;
    z3::solver solver(context, z3::solver::simple());

    z3::expr_vector queens = createTiles(context, board);

    solver.add(createConstraintsBool(context, queens, board));

    return enumerateSolutions(context, solver, queens);
}

int nqueensNoPropagatorBV(unsigned board) {
    z3::context context;
    z3::solver solver(context, Z3_mk_simple_solver(context));

    z3::expr_vector queens = createQueens(context, board);

    solver.add(createConstraintsBV(context, queens));

    return enumerateSolutions(context, solver, queens);
}

int nqueensPropagator(unsigned board, bool singleSolution, bool addConflict, bool pureSAT, bool withTheory, bool withDecide, bool hybrid) {

    if (singleSolution)
        addConflict = false;

    z3::context context;
    z3::solver solver(context, z3::solver::simple());
    
    z3::expr_vector queens(context);
    if (!pureSAT) {
        queens = createQueens(context, board);
    }
    else {
        queens = createTiles(context, board);
    }

    user_propagator* propagator;

    if (!withTheory) {
    	propagator = new user_propagator(&solver, queens, board, addConflict);
    }
    else {
        if (!pureSAT)
            propagator = new user_propagator_with_theory(&solver, queens, board, addConflict);
        else {
            propagator = new user_propagator_with_theory2(&solver, queens, board, addConflict);
        }
    }

    if (withDecide)
        propagator->register_decide();

    if (!withTheory) {
        if (!pureSAT) {
            solver.add(createConstraintsBV(context, queens));
        }
        else {
            solver.add(createConstraintsBool(context, queens, board));
        }
    }

    if (withTheory && !pureSAT && hybrid) {
        solver.add(z3::distinct(queens));
    }

    int res;

    if (!addConflict && !singleSolution) {
        res = enumerateSolutions(context, solver, queens);
    }
    else {
        solver.check();
        res = propagator->getModelCount();
    }

    delete propagator;
    printStatistics(solver);

    return res;
}

int nqueensMaximization1(unsigned *num) {
    unsigned n = *num;
    z3::context context;
    z3::solver solver(context, z3::solver::simple());

    z3::expr_vector queens1 = createQueens(context, n, log2i(n * n), ""); // square to avoid overflow during summation

    z3::expr valid1 = createConstraintsBV(context, queens1);

    z3::expr_vector queens2 = createQueens(context, n, log2i(n * n), "forall_");

    z3::expr valid2 = createConstraintsBV(context, queens2);

    z3::expr manhattanSum1 = context.bv_val(0, queens1[0].get_sort().bv_size());
    z3::expr manhattanSum2 = context.bv_val(0, queens2[0].get_sort().bv_size());

    for (unsigned i = 1; i < queens1.size(); i++) {
        manhattanSum1 = manhattanSum1 + z3::ite(z3::uge(queens1[i], queens1[i - 1]), queens1[i] - queens1[i - 1], queens1[i - 1] - queens1[i]);
        manhattanSum2 = manhattanSum2 + z3::ite(z3::uge(queens2[i], queens2[i - 1]), queens2[i] - queens2[i - 1], queens2[i - 1] - queens2[i]);
    }


    solver.add(valid1 && z3::forall(queens2, z3::implies(valid2, manhattanSum1 >= manhattanSum2)));

    solver.check();
    z3::model model = solver.get_model();

    int max = 0;

    int prev, curr;
    curr = model.eval(queens1[0]).get_numeral_int();

    for (unsigned i = 1; i < n; i++) {
        prev = curr;
        curr = model.eval(queens1[i]).get_numeral_int();
        max += abs(curr - prev);
    }

    return max;
}

int nqueensMaximization2(unsigned *num) {
    unsigned n = *num;
    z3::context context;
    z3::solver solver(context, z3::solver::simple());
    
    z3::expr_vector queens = createQueens(context, n, log2i(n * n), "");

    solver.add(createConstraintsBV(context, queens));

    user_propagator_subquery_maximisation propagator(&solver, n, queens);

    solver.check();
    z3::model model = solver.get_model();

    int max = 0;

    int prev, curr;
    curr = model.eval(queens[0]).get_numeral_int();
    for (unsigned i = 1; i < n; i++) {
        prev = curr;
        curr = model.eval(queens[i]).get_numeral_int();
        max += abs(curr - prev);
    }

    return max;
}

int nqueensMaximization3(unsigned *num) {
    unsigned n = *num;
    z3::context context;
    z3::solver solver(context, z3::solver::simple());
    std::unordered_map<z3::expr, unsigned> idMapping;

    z3::expr_vector queens = createQueens(context, n, log2i(n * n), "");

    solver.add(createConstraintsBV(context, queens));

    user_propagator_internal_maximisation propagator(&solver, idMapping, n, queens);

    for (unsigned i = 0; i < queens.size(); i++) {
        propagator.add(queens[i]);
        idMapping[queens[i]] = i;
    }

    solver.check();
    return propagator.best;
}

int nqueensMaximization4(unsigned *num) {
    unsigned n = *num;
    z3::context context;
    z3::solver solver(context, z3::solver::simple());

    z3::expr_vector queens1 = createQueens(context, n, log2i(n * n), "");
    z3::expr_vector queens2 = createQueens(context, n, log2i(n * n), "forall_");

    z3::expr manhattanSum1 = context.bv_val(0, queens1[0].get_sort().bv_size());
    z3::expr manhattanSum2 = context.bv_val(0, queens2[0].get_sort().bv_size());

    for (unsigned i = 1; i < queens1.size(); i++) {
        manhattanSum1 = manhattanSum1 + z3::ite(z3::uge(queens1[i], queens1[i - 1]), queens1[i] - queens1[i - 1], queens1[i - 1] - queens1[i]);
        manhattanSum2 = manhattanSum2 + z3::ite(z3::uge(queens2[i], queens2[i - 1]), queens2[i] - queens2[i - 1], queens2[i - 1] - queens2[i]);
    }

    z3::sort_vector domain(context);
    for (unsigned i = 0; i < queens1.size(); i++) {
        domain.push_back(queens1[i].get_sort());
    }
    z3::func_decl validFunc = context.user_propagate_function(context.str_symbol("valid"), domain, context.bool_sort());

    solver.add(validFunc(queens1) && z3::forall(queens2, z3::implies(validFunc(queens2), manhattanSum1 >= manhattanSum2)));
    user_propagator_created_maximisation propagator(&solver, n);

    solver.check();
    z3::model model = solver.get_model();

    int max = 0;

    int prev, curr;
    curr = model.eval(queens1[0]).get_numeral_int();

    for (unsigned i = 1; i < n; i++) {
        prev = curr;
        curr = model.eval(queens1[i]).get_numeral_int();
        max += abs(curr - prev);
    }

    return max;
}

int nqueensHigherDimensionAllCover(unsigned args[2]) {
    unsigned board = args[0];
    unsigned dim = args[1];

    z3::context context;
    z3::solver solver(context, z3::solver::simple());
    user_propagator_higher_dimension propagator(&solver, board, 2, dim);
    z3::check_result result = solver.check();
    if (result == z3::check_result::sat) {
        std::cout << solver.get_model().to_string();
    }
    assert(result == z3::unsat);

    return propagator.getQueenCnt();
}