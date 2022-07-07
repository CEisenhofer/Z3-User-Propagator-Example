#include "common.h"


int sorting4(unsigned size, sortingConstraints constraints) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    exprNetwork network(context, 0);

    struct sort : multiSort {

    	exprNetwork& n;
        z3::solver& s;

    	sort(exprNetwork& n, z3::solver& s) : n(n), s(s) { }

        void add(z3::expr_vector& in, z3::expr_vector& out) override {
            assert(in.size() == out.size());
            n.increase(in.size());
            for (unsigned i = 0; i < in.size(); i++) {
                n.add(i, in[i]);
            }
            // insertion sort: O(n^2)
            for (unsigned i = 0; i < in.size() - 1; i++) {
                for (unsigned j = 0; j < in.size() - i - 1; j++) {
                    n.addComparision(j, j + 1);
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
    z3::expr_vector a = s.assertions();
    z3::check_result result = s.check();
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
