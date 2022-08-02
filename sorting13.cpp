#include "common.h"

int sorting13(unsigned size, sortingConstraints constraints) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    struct sort : multiSort {

        z3::solver& s;
        sort(z3::solver& s) : s(s) {}

        void add(z3::expr_vector& in, z3::expr_vector& out) override {
            for (int i = 1; i < out.size(); i++) {
                s.add(z3::ule(out[i - 1], out[i]));
            }

            z3::context& ctx = s.ctx();

            const z3::sort range = in[0].get_sort();
            z3::sort_vector domain(ctx);
            domain.push_back(ctx.bv_sort(log2i(in.size())));
            
            z3::func_decl mappingFct = ctx.function("mappingFct", domain, range);

            z3::expr_vector mapping(ctx);

            for (int i = 0; i < in.size(); i++) {

                z3::expr e = ctx.constant(("mapping_" + std::to_string(i)).c_str(), domain.back());
                
                s.add(in[i] == mappingFct(i));
                s.add(out[i] == mappingFct(e));

                s.add(z3::ule(e, in.size() - 1));
                z3::expr_vector a = s.assertions();
                mapping.push_back(e);
            }

            for (int j = 0; j < mapping.size(); j++) {
                for (int k = j + 1; k < mapping.size(); k++) {
                    s.add(mapping[j] != mapping[k]);
                }
            }
        }
    };

    sort sort(s);

    applyConstraints(s, size, sort, constraints);

    z3::check_result result = s.check();
    printStatistics(s);
    if (constraints & outputReverse) {
        assert(result == z3::unsat);
    }
    else if (!(constraints & pseudoBoolean)) {
        z3::model m = s.get_model();
        checkSorting(m, *sort.in, *sort.out, constraints);
    }
    else {
        assert(result == z3::sat);
    }
    return -1;
}
