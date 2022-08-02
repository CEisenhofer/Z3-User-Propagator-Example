#include "LazySortingNetworkPropagator.h"


int sorting8(unsigned size, sortingConstraints constraints, bool persistent) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    struct sort : multiSort {
        LazySortingNetworkPropagator* prop;
        sort(LazySortingNetworkPropagator* prop) : prop(prop) {}

        void add(z3::expr_vector& in, z3::expr_vector& out) override {
            symbolicNetwork network(in.size());
            // odd-even sort: O(n*log(n)^2)
            for (unsigned p = 1; p < in.size(); p <<= 1) {
                for (unsigned k = p; k >= 1; k >>= 1) {
                    for (unsigned j = k % p; j < in.size() - k; j += 2 * k) {
                        for (unsigned i = 0; i < MIN(k, in.size() - j - k); i++) {
                            if ((i + j) / (2 * p) == (i + j + k) / (2 * p)) {
                                network.addComparision(i + j, i + j + k);
                            }
                        }
                    }
                }
            }
            prop->addInputOutput(network, in, out);
        }
    };

    LazySortingNetworkPropagator propagator(&s, BIT_CNT, persistent);
    sort sort(&propagator);

    applyConstraints(s, size, sort, constraints);


    z3::check_result result = s.check();
    printStatistics(s);
    if (constraints & outputReverse) {
        assert(result == z3::unsat);
    }
    else if (!(constraints & pseudoBoolean)) {
        z3::model m = s.get_model();
        checkSorting(m, propagator.getInputs(), propagator.getOutputs(), constraints);
    }
    else {
        assert(result == z3::sat);
    }
    return -1;
}
