#include "common.h"

int sorting11(unsigned size, sortingConstraints constraints) {
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
            domain.push_back(ctx.bv_sort(in.size()));
            int bits = domain.back().bv_size();

            z3::func_decl mappingFct = ctx.function("mappingFct", domain, range);

            std::vector<z3::expr_vector> bitExprs;

            for (int i = 0; i < in.size(); i++) {

                z3::expr e = ctx.constant(("mapping_" + std::to_string(i)).c_str(), domain.back());
                
                z3::expr index = ctx.bv_val(1, in.size());
                index = z3::shl(index, i);
                s.add(in[i] == mappingFct(index));
                s.add(out[i] == mappingFct(e));

                z3::expr_vector bitSequence(ctx);

                for (int j = 0; j < bits; j++) {
                    z3::expr e2 = e.bit2bool(j);
                    bitSequence.push_back(e2);
                }
                bitExprs.push_back(bitSequence);
            }

            for (int i = 0; i < bitExprs.size(); i++) {
                for (int j = 0; j < bitExprs[i].size(); j++) {
                    for (int k = j + 1; k < bitExprs[i].size(); k++) {
                        s.add(!bitExprs[i][j] || !bitExprs[i][k]);
                    }
                }
                s.add(z3::mk_or(bitExprs[i]));
            }

            for (int i = 0; i < bitExprs[0].size(); i++) {
                for (int j = 0; j < bitExprs.size(); j++) {
                    for (int k = j + 1; k < bitExprs.size(); k++) {
                        s.add(!bitExprs[j][i] || !bitExprs[k][i]);
                    }
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
