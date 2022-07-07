#include "common.h"

void checkSorting(const z3::model &model, const z3::expr_vector &in, const z3::expr_vector &out, const sortingConstraints constraints) {
    if (in.size() != out.size()) {
        exit(13);
    }
    std::vector<uint64_t> inputs;
    std::unordered_set<unsigned> set;
    inputs.reserve(in.size());
    for (unsigned i = 0; i < in.size(); i++) {
        inputs.push_back(model.eval(in[i]).get_numeral_uint64());
        if ((constraints & (inputDisjoint | outputDisjoint)) && set.contains(inputs.back()))
            exit(14);
        set.insert(inputs.back());
    }
#ifdef VERBOSE
    for (unsigned i = 0; i < inputs.size(); i++) {
        std::cout << "in" << i << " = " << inputs[i] << std::endl;
    }
#endif
    std::ranges::sort(inputs);
    std::vector<uint64_t> outputs;
    for (unsigned i = 0; i < out.size(); i++) {
        uint64_t v = model.eval(out[i]).get_numeral_uint64();
        if (inputs[i] != v)
            exit(14);
        outputs.push_back(v);
#ifdef VERBOSE
        std::cout << "out" << i << " = " << inputs[i] << std::endl;
#endif
    }

    if (constraints & intervals) {
        unsigned mask = (unsigned)-1;
        mask >>= ((sizeof(unsigned) * 8) - (BIT_CNT / 2));
        unsigned prevSize = outputs[0] & mask;
        unsigned prevAddr = (outputs[0] >> (BIT_CNT / 2)) & mask;

        for (unsigned i = 1; i < outputs.size(); i++) {
            unsigned size = outputs[i] & mask;
            unsigned addr = (outputs[i] >> (BIT_CNT / 2)) & mask;
            if (prevAddr + prevSize > addr) {
                exit(15);
            }
            prevSize = size;
            prevAddr = addr;
        }
    }
}

z3::expr clone(z3::solver& s, z3::expr& e, const char* name) {
    z3::expr c = s.ctx().bv_const(name, 1);
    s.add(e == c);
    return c;
}

void applyConstraints(z3::solver& s, unsigned size, multiSort& sort, sortingConstraints constraints) {
    if (!(constraints & pseudoBoolean)) {
        sort.assertDefault(size, s.ctx());
    }
    if (constraints == 0)
        return;

    if (constraints & inputDisjoint) {
        s.add(z3::distinct(*sort.in));
    }
    if (constraints & outputDisjoint) {
        s.add(z3::distinct(*sort.out));
    }
    if (constraints & inputReverse) {
        z3::expr_vector counterOrder(s.ctx());
        for (unsigned  i = 0; i < sort.in->size() - 1; i++) {
            counterOrder.push_back(z3::uge((*sort.in)[i], (*sort.in)[i + 1]));
        }
        s.add(z3::mk_and(counterOrder));
    }
    if (constraints & outputReverse) {
        z3::expr_vector counterOrder(s.ctx());
        for (unsigned  i = 0; i < sort.out->size() - 1; i++) {
            counterOrder.push_back(z3::ugt((*sort.out)[i], (*sort.out)[i + 1]));
        }
        s.add(z3::mk_and(counterOrder));
    }
    if (constraints & intervals) {
        z3::expr_vector addresses(s.ctx());
        z3::expr_vector sizes(s.ctx());
        unsigned bits = (*sort.out)[0].get_sort().bv_size();
        assert((bits & 1) == 0);
        for (unsigned i = 0; i < sort.out->size(); i++) {
            z3::expr firstHalf = (*sort.out)[i].extract(bits / 2 - 1, 0);
            z3::expr secondHalf = (*sort.out)[i].extract(bits - 1, bits / 2);
            assert(bits == 2 * firstHalf.get_sort().bv_size());
            assert(bits == 2 * secondHalf.get_sort().bv_size());
            addresses.push_back(secondHalf);
            sizes.push_back(firstHalf);
        }
        for (unsigned i = 0; i < addresses.size() - 1; i++) {
            s.add(z3::ule(z3::zext(addresses[i], 1) + z3::zext(sizes[i], 1), z3::zext(addresses[i + 1], 1)));
        }
    }
    if (constraints & pseudoBoolean) {
        z3::expr x0 = s.ctx().bv_const("x0", 1);
        z3::expr x1 = s.ctx().bv_const("x1", 1);
        z3::expr x2 = s.ctx().bv_const("x2", 1);
        z3::expr x3 = s.ctx().bv_const("x3", 1);

        s.add(x0 != x2);
        s.add(x0 != x3);

        // x0 + x1 + 2*x2 - x3 >= 2
        // x0 + x1 + 2*x2 + !x3 >= 3
        z3::expr_vector in1(s.ctx());
        in1.push_back(clone(s, x0, "in1_0"));
        in1.push_back(clone(s, x1, "in1_1"));
        in1.push_back(clone(s, x2, "in1_2"));
        in1.push_back(clone(s, x2, "in1_3"));
        in1.push_back(~clone(s, x3, "in1_4"));

        z3::expr_vector out1(s.ctx());
        z3::expr assertion1(s.ctx());
        out1.push_back(s.ctx().bv_const("out1_0", 1));
        out1.push_back(s.ctx().bv_const("out1_1", 1));
        out1.push_back(assertion1 = s.ctx().bv_const("out1_2", 1));
        out1.push_back(s.ctx().bv_const("out1_3", 1));
        out1.push_back(s.ctx().bv_const("out1_4", 1));
        sort.add(in1, out1);
        s.add(assertion1 == 1);

        // -x0 - x1 - x2 + 2 * x3 >= 0
        // !x0 + !x1 + !x2 + 2 * x3 >= 3
        z3::expr_vector in2(s.ctx());
        in2.push_back(~clone(s, x0, "in2_0"));
        in2.push_back(~clone(s, x1, "in2_1"));
        in2.push_back(~clone(s, x2, "in2_2"));
        in2.push_back(clone(s, x3, "in2_3"));
        in2.push_back(clone(s, x3, "in2_4"));

        z3::expr_vector out2(s.ctx());
        z3::expr assertion2(s.ctx());
        out2.push_back(s.ctx().bv_const("out2_0", 1));
        out2.push_back(s.ctx().bv_const("out2_1", 1));
        out2.push_back(assertion2 = s.ctx().bv_const("out2_2", 1));
        out2.push_back(s.ctx().bv_const("out2_3", 1));
        out2.push_back(s.ctx().bv_const("out2_4", 1));
        sort.add(in2, out2);
        s.add(assertion2 == 1);

        // x0 + x1 + x2 >= 2
        z3::expr_vector in3(s.ctx());
        in3.push_back(clone(s, x0, "in3_0"));
        in3.push_back(clone(s, x1, "in3_1"));
        in3.push_back(clone(s, x2, "in3_2"));

        z3::expr_vector out3(s.ctx());
        z3::expr assertion3(s.ctx());
        out3.push_back(s.ctx().bv_const("out3_0", 1));
        out3.push_back(s.ctx().bv_const("out3_1", 1));
        out3.push_back(assertion3 = s.ctx().bv_const("out3_2", 1));
        sort.add(in3, out3);
        s.add(assertion3 == 1);
    }
}

int sorting1(unsigned size, sortingConstraints constraints) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    struct sort : multiSort {

        z3::solver& s;

        sort(z3::solver& s) : s(s) { }

        void add(z3::expr_vector& in, z3::expr_vector& out) override {
            std::vector<std::vector<z3::func_decl>> subResults;
            // First level: "recursion level"
            // Second level: variable ordering that are already sorted locally

            std::vector<z3::func_decl> firstLevel;
            z3::expr_vector disj(in.ctx());

            for (unsigned i = 0; i < in.size(); i++) {
                z3::sort_vector domain(in.ctx());
                domain.push_back(in.ctx().bv_sort(1));
                z3::func_decl v = in.ctx().function((std::string("v_{0,") + std::to_string(i) + "}").c_str(), domain, in.ctx().bv_sort(BIT_CNT));
                firstLevel.push_back(v);
                disj.push_back(v(0));
            }
            s.add(z3::distinct(disj));

            subResults.push_back(firstLevel);

            for (unsigned i = 1; (1 << (i - 1)) < firstLevel.size(); i++) {
                std::vector<z3::func_decl> nextLevel;
                std::vector<z3::func_decl>& prevBlock = subResults[i - 1];
                z3::sort_vector domain(in.ctx());
                domain.push_back(in.ctx().bv_sort(i + 1));

                for (unsigned j = 0; j < prevBlock.size(); j += 2) {
                    z3::func_decl v = in.ctx().function((std::string("v_{") + std::to_string(i) + "," + std::to_string(j) + "}").c_str(), domain, in.ctx().bv_sort(BIT_CNT));

                    z3::expr_vector block(in.ctx());
                    const z3::func_decl& b1 = prevBlock[j];
                    const z3::func_decl& b2 = prevBlock[j + 1];
                    z3::expr
                        prevLeft = in.ctx().bv_val(0, i),
                        prevRight = in.ctx().bv_val(0, i);

                    for (unsigned k = 0; k < (1 << i); k++) {
                        z3::expr nextLeft = in.ctx().bv_const(std::string("i_{" + std::to_string(i) + "," + std::to_string(j) + "," + std::to_string(k) + "}").c_str(), i);
                        z3::expr nextRight = in.ctx().bv_const(std::string("i_{" + std::to_string(i) + "," + std::to_string(j + 1) + "," + std::to_string(k) + "}").c_str(), i);
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

                for (unsigned i = 0; i < firstLevel.size(); i++) {
                    s.add(subResults[0][i](0) == in[i]);
                    s.add(subResults.back()[0](i) == out[i]);
                }
            }
        }
    };

    sort sort(s);

    applyConstraints(s, size, sort, constraints);

    z3::check_result result = s.check();
    if (constraints & outputReverse) {
        assert(result == z3::unsat);
    }
    else {
        z3::model m = s.get_model();
        checkSorting(m, *sort.in, *sort.out, constraints);
    }
    return -1;
}
