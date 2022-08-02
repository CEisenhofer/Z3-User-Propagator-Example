#include "common.h"

int sorting7(unsigned size, sortingConstraints constraints) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    exprNetwork network(context, 0);

    struct sort : multiSort {

    	exprNetwork& n;
        z3::solver& s;

        sort(exprNetwork& n, z3::solver& s) : n(n), s(s) {}

        void add(z3::expr_vector& in, z3::expr_vector& out) override {
            n.increase(in.size());
            for (unsigned i = 0; i < in.size(); i++) {
                n.add(i, in[i]);
            }

            // odd-even sort: O(n*log(n)^2)
            for (unsigned p = 1; p < in.size(); p <<= 1) {
                for (unsigned k = p; k >= 1; k >>= 1) {
                    for (unsigned j = k % p; j < in.size() - k; j += 2 * k) {
                        for (unsigned i = 0; i < MIN(k, in.size() - j - k); i++) {
                            if ((i + j) / (2 * p) == (i + j + k) / (2 * p)) {
                                n.addComparision(i + j, i + j + k);
                            }
                        }
                    }
                }
            }

            const auto& outputExpr = n.getCurrentOutputs();

            for (unsigned i = 0; i < outputExpr.size(); i++) {
                s.add(out[i] == outputExpr[i]);
            }
        }
    };

    sort sort(network, s);

    applyConstraints(s, size, sort, constraints);

    z3::check_result result = s.check();
    printStatistics(s);
    if (constraints & outputReverse) {
        assert(result == z3::unsat);
    }
    else if (!(constraints & pseudoBoolean)) {
        z3::model m = s.get_model();
        checkSorting(m, network.getInputs(), network.getOutputs(), constraints);
    }
    else {
        assert(result == z3::sat);
    }
    return -1;
}
