#include "common.h"

void sorting1() {

    z3::context context;
    z3::solver s(context, z3::solver::simple());

    std::vector<std::vector<z3::func_decl>> subResults;
    // First level: "recursion level"
    // Second level: variable ordering that are already sorted locally

    std::vector<z3::func_decl> firstLevel;
    z3::expr_vector disj(context);

    for (unsigned i = 0; i < SORT_CNT; i++) {
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

    // std::cout << "Problem: " << s.assertions().to_string() << "\n" << std::endl;

    auto result = s.check();
    if (result == z3::check_result::sat) {

        std::cout << "Sat" << std::endl;
        z3::model m = s.get_model();

        std::cout << "Model: " << m.to_string() << std::endl;

        for (unsigned i = 0; i < firstLevel.size(); i++) {
            std::cout << "v[" << i << "] = " << m.eval(subResults[0][i](0)).get_numeral_uint64() << std::endl;
        }
        for (unsigned i = 0; i < firstLevel.size(); i++) {
            std::cout << "w[" << i << "] = " << m.eval(subResults.back()[0](i)).get_numeral_uint64() << std::endl;
        }
    }
    else {
        std::cout << "Unsat" << std::endl;
    }

    exit(1);
}
