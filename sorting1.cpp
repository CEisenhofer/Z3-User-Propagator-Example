#include "common.h"

void checkSorting(const z3::model &model, const z3::expr_vector &in, const z3::expr_vector &out) {
    if (in.size() != out.size()) {
        exit(13);
    }
    std::vector<uint64_t> inputs;
    inputs.reserve(in.size());
    for (unsigned i = 0; i < in.size(); i++) {
        inputs.push_back(model.eval(in[i]).get_numeral_uint64());
    }
#ifdef VERBOSE
    for (unsigned i = 0; i < inputs.size(); i++) {
        std::cout << "in" << i << " = " << inputs[i] << std::endl;
    }
#endif
    std::ranges::sort(inputs);
    for (unsigned i = 0; i < out.size(); i++) {
        uint64_t v = model.eval(out[i]).get_numeral_uint64();
        if (inputs[i] != v) {
            exit(14);
        }
#ifdef VERBOSE
        std::cout << "out" << i << " = " << inputs[i] << std::endl;
#endif
    }

}

void applyConstraints(z3::solver& s, const z3::expr_vector& in, const z3::expr_vector& out, sortingConstraints constraints) {
    if (constraints == 0)
        return;

    if (constraints & inputDisjoint) {
        s.add(z3::distinct(in));
    }
    if (constraints & outputDisjoint) {
        s.add(z3::distinct(out));
    }
    if (constraints & inputReverse) {
        z3::expr_vector counterOrder(s.ctx());
        for (int i = 0; i < in.size() - 1; i++) {
            counterOrder.push_back(z3::uge(in[i], in[i + 1]));
        }
        s.add(z3::mk_and(counterOrder));
    }
    if (constraints & outputReverse) {
        z3::expr_vector counterOrder(s.ctx());
        for (int i = 0; i < out.size() - 1; i++) {
            counterOrder.push_back(z3::ugt(out[i], out[i + 1]));
        }
        s.add(z3::mk_and(counterOrder));
    }
}

int sorting1(unsigned size, sortingConstraints constraints) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    std::vector<std::vector<z3::func_decl>> subResults;
    // First level: "recursion level"
    // Second level: variable ordering that are already sorted locally

    std::vector<z3::func_decl> firstLevel;
    z3::expr_vector disj(context);

    for (unsigned i = 0; i < size; i++) {
        z3::sort_vector domain(context);
        domain.push_back(context.bv_sort(1));
        z3::func_decl v = context.function((std::string("v_{0,") + std::to_string(i) + "}").c_str(), domain, context.bv_sort(BIT_CNT));
        firstLevel.push_back(v);
        disj.push_back(v(0));
    }
    s.add(z3::distinct(disj));

    subResults.push_back(firstLevel);

    for (unsigned i = 1; (1 << (i - 1)) < firstLevel.size(); i++) {
        std::vector<z3::func_decl> nextLevel;
        std::vector<z3::func_decl> &prevBlock = subResults[i - 1];
        z3::sort_vector domain(context);
        domain.push_back(context.bv_sort(i + 1));

        for (unsigned j = 0; j < prevBlock.size(); j += 2) {
            z3::func_decl v = context.function((std::string("v_{") + std::to_string(i) + "," + std::to_string(j) + "}").c_str(), domain, context.bv_sort(BIT_CNT));

            z3::expr_vector block(context);
            const z3::func_decl &b1 = prevBlock[j];
            const z3::func_decl &b2 = prevBlock[j + 1];
            z3::expr
                    prevLeft = context.bv_val(0, i),
                    prevRight = context.bv_val(0, i);

            for (unsigned k = 0; k < (1 << i); k++) {
                z3::expr nextLeft = context.bv_const(std::string("i_{" + std::to_string(i) + "," + std::to_string(j) + "," + std::to_string(k) + "}").c_str(), i);
                z3::expr nextRight = context.bv_const(std::string("i_{" + std::to_string(i) + "," + std::to_string(j + 1) + "," + std::to_string(k) + "}").c_str(), i);
                s.add(z3::ite(
                        z3::ult(prevLeft, 1 << (i - 1)) && z3::ule(b1(prevLeft), b2(prevRight)) || (z3::uge(prevRight, 1 << (i - 1))),
                        nextLeft == prevLeft + 1 && nextRight == prevRight && v(k) == b1(prevLeft),
                        nextLeft == prevLeft && nextRight == prevRight + 1 && v(k) == b2(prevRight)
                ));
                prevLeft = nextLeft;
                prevRight = nextRight;
            }

            nextLevel.push_back(v);

        }
        subResults.push_back(nextLevel);
    }

    z3::expr_vector in(context), out(context);
    for (unsigned i = 0; i < firstLevel.size(); i++) {
        in.push_back(subResults[0][i](0));
        out.push_back(subResults.back()[0](i));
    }

    applyConstraints(s, in, out, constraints);

    z3::check_result result = s.check();
    if (constraints & outputReverse) {
        assert(result == z3::unsat);
    }
    else {
        z3::model m = s.get_model();
        checkSorting(m, in, out);
    }
    return -1;
}
