#include "common.h"

int sorting7(unsigned* size) {
    unsigned cnt = *size;
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    exprNetwork network(context, cnt);
    z3::expr_vector inputs(context);
    z3::expr_vector outputs(context);

    for (unsigned i = 0; i < cnt; i++) {
        inputs.push_back(context.bv_const(("in_" + std::to_string(i)).c_str(), BIT_CNT));
        outputs.push_back(context.bv_const(("out_" + std::to_string(i)).c_str(), BIT_CNT));
        network.add(i, inputs.back());
    }

    // odd-even sort: O(n*log(n)^2)
    for (unsigned p = 1; p < cnt; p <<= 1) {
        for (unsigned k = p; k >= 1; k >>= 1) {
            for (unsigned j = k % p; j < cnt - k; j += 2 * k) {
                for (unsigned i = 0; i < MIN(k, cnt - j - k); i++) {
                    if ((i + j) / (2 * p) == (i + j + k) / (2 * p)) {
                        network.addComparision(i + j, i + j + k);
                    }
                }
            }
        }
    }

    const auto& outputExpr = network.getOutputs();

    for (unsigned i = 0; i < outputExpr.size(); i++) {
        s.add(outputs[i] == outputExpr[i]);
    }

    s.add(z3::distinct(inputs));

    z3::expr_vector counterOrder(context);
    for (int i = 0; i < cnt - 1; i++) {
        counterOrder.push_back(inputs[i] >= inputs[i + 1]);
    }
    s.add(z3::mk_and(counterOrder));

    s.check();
    z3::model m = s.get_model();
    checkSorting(m, inputs, outputs);
    return -1;
}
