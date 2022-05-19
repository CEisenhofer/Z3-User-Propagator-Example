#include "common.h"


int sorting4(unsigned size, sortingConstraints constraints) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    exprNetwork network(context, size);
    z3::expr_vector inputs(context);
    z3::expr_vector outputs(context);

    for (unsigned i = 0; i < size; i++) {
        inputs.push_back(context.bv_const(("in_" + std::to_string(i)).c_str(), BIT_CNT));
        outputs.push_back(context.bv_const(("out_" + std::to_string(i)).c_str(), BIT_CNT));
        network.add(i, inputs.back());
    }

    // insertion sort: O(n^2)
    for (unsigned i = 0; i < size - 1; i++) {
        for (unsigned j = 0; j < size - i - 1; j++) {
            network.addComparision(j, j + 1);
        }
    }

    const auto &outputExpr = network.getOutputs();

    for (unsigned i = 0; i < outputExpr.size(); i++) {
        s.add(outputs[i] == outputExpr[i]);
    }

    applyConstraints(s, inputs, outputExpr, constraints);

    z3::check_result result = s.check();
    if (constraints & outputReverse) {
        assert(result == z3::unsat);
    }
    else {
        z3::model m = s.get_model();
        checkSorting(m, inputs, outputs);
    }
    return -1;
}
