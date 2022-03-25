#include "common.h"

class SortedPropagator : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    z3::expr_vector fixedValues;
    std::unordered_map<z3::expr, uint64_t> model;

    unsigned funcValues = 0, inValues = 0, outValues = 0;
    const z3::expr &func;
    const z3::expr_vector &in;
    const z3::expr_vector &out;


    std::unordered_map<z3::expr, int> astToIndex;

    inline bool hasAllFuncValues() const {
        return funcValues > 0;
    }

    inline bool hasAllInValues() const {
        return inValues == in.size();
    }

    inline bool hasAllOutValues() const {
        return outValues == out.size();
    }

    inline bool hasEverything() const {
        return model.size() == in.size() + out.size() + 1;
    }

public:

    SortedPropagator(z3::solver *s, const z3::expr &func, const z3::expr_vector &in, const z3::expr_vector &out) :
            user_propagator_base(s), fixedValues(s->ctx()), func(func), in(in), out(out) {

        this->register_fixed();

        assert(in.size() == out.size());
        astToIndex.emplace(func, 0);
        this->add(func);
        for (unsigned i = 0; i < in.size(); i++) {
            astToIndex.emplace(in[i], i + 1);
            this->add(in[i]);
            astToIndex.emplace(out[i], -(i + 1));
            this->add(out[i]);
        }
    }

    void push() override {
        prevFixedCnt.push(fixedValues.size());
    }

    void pop(unsigned int num_scopes) override {
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned prevFixed = prevFixedCnt.top();
            prevFixedCnt.pop();
            for (unsigned j = fixedValues.size(); j > prevFixed; j--) {
                model.erase(fixedValues[j - 1]);
                int index = astToIndex.at(fixedValues[j - 1]);
                if (index == 0) {
                    funcValues--;
                }
                else if (index > 0) {
                    inValues--;
                }
                else {
                    outValues--;
                }
                fixedValues.pop_back();
            }
        }
    }

    void fixed(const z3::expr &ast, const z3::expr &value) override {
        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        uint64_t v = value.is_true() ? 1 : (value.is_false() ? 0 : value.get_numeral_uint64());
        fixedValues.push_back(ast);
        model.emplace(ast, v);

        int index = astToIndex.at(ast);

        if (index == 0) {
            funcValues++;
        }
        else if (index > 0) {
            inValues++;
        }
        else {
            outValues++;
        }

        if (!hasAllInValues() || !hasAllFuncValues())
            // Not everything assigned so far
            return;

        bool funcValue = model.at(func);
        if (funcValue) {
            /*std::vector<unsigned> associatedInOut;
            std::vector<unsigned> associatedOutIn;
            for (unsigned i = 0; i < in.size(); i++) {
                associatedInOut.push_back((unsigned)-1);
                associatedOutIn.push_back((unsigned)-1);
            }
            bool allArgumentsMatched = true;
            for (unsigned i = 0; i < out.size(); i++) {
                bool argumentMatched = false;
                for (unsigned j = 0; j < in.size(); j++) {
                    if (associatedInOut[j] == (unsigned)-1 && model.at(out[i]) == model.at(in[j])) {
                        associatedInOut[j] = i;
                        associatedOutIn[i] = j;
                        argumentMatched = true;
                        break;
                    }
                }
                allArgumentsMatched &= argumentMatched;
            }
            if (!allArgumentsMatched) {
                z3::expr_vector conjunction(ctx());
                for (unsigned i = 0; i < out.size(); i++) {
                    z3::expr_vector possibilities(ctx());
                    for (unsigned j = 0; j < in.size(); j++) {
                        if (associatedInOut[j] == (unsigned)-1) {
                            possibilities.push_back(out[i] == in[j]);
                        }
                    }
                    conjunction.push_back(z3::mk_or(possibilities));
                }
                z3::expr_vector empty(ctx());
                this->propagate(empty, z3::implies(func, z3::mk_and(conjunction)));
                return;
            }
            z3::expr_vector empty(ctx());
            uint64_t last = model[out[0]];
            for (unsigned i = 0; i < out.size(); i++) {
                uint64_t current = model[out[i]];
                if (last > current) {
                    this->propagate(empty, z3::implies(func, z3::ule(out[i - 1], out[i])));
                }
                last = current;
            }*/
            std::vector<uint64_t> sortedValues;
            sortedValues.reserve(in.size());
            for (unsigned i = 0; i < in.size(); i++) {
                uint64_t w = model.at(in[i]);
                sortedValues.push_back(w);
            }
            std::sort(sortedValues.begin(), sortedValues.end());
            z3::expr_vector premiss(ctx());
            z3::expr_vector sorted(ctx());
            premiss.push_back(func);
            for (unsigned i = 0; i < in.size(); i++) {
                premiss.push_back(in[i] == ctx().bv_val(model.at(in[i]), BIT_CNT));
            }
            for (unsigned i = 0; i < out.size(); i++) {
                sorted.push_back(out[i] == ctx().bv_val(sortedValues[i], BIT_CNT));
            }
            z3::expr_vector empty(ctx());
            // std::cout << "Prop: " << z3::implies(z3::mk_and(premiss), z3::mk_and(sorted)).to_string() << std::endl;
            this->propagate(empty, z3::implies(z3::mk_and(premiss), z3::mk_and(sorted)));
        }
        else {
            // TODO: Implement
            assert(false);
        }
    }

    user_propagator_base *fresh(z3::context &ctx) override { return this; }

};

void sorting2() {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    z3::expr_vector in(context);
    z3::expr_vector out(context);
    z3::expr_vector args(context);
    z3::sort_vector domain(context);

    std::cout << "Sorting (2) " << SORT_CNT << " elements" << std::endl;
    for (unsigned i = 0; i < SORT_CNT; i++) {
        domain.push_back(context.bv_sort(BIT_CNT));
        in.push_back(context.constant((std::string("in") + std::to_string(i)).c_str(), domain[i]));
        args.push_back(in.back());
    }
    for (unsigned i = 0; i < SORT_CNT; i++) {
        domain.push_back(domain[i]);
        out.push_back(context.constant((std::string("out") + std::to_string(i)).c_str(), domain[i]));
        args.push_back(out.back());
    }

    z3::func_decl sorted = context.user_propagate_function(context.str_symbol("sorted"), domain, context.bool_sort());

    auto func = sorted(args);

    s.add(z3::distinct(in));
    s.add(func);

    SortedPropagator propagator(&s, func, in, out);

    auto result = s.check();
    if (result == z3::check_result::sat) {

        std::cout << "Sat" << std::endl;
        z3::model m = s.get_model();

        std::cout << "Model: " << m.to_string() << std::endl;

        for (unsigned i = 0; i < in.size(); i++) {
            std::cout << "in" << i << " = " << m.eval(in[i]).get_numeral_uint64() << std::endl;
        }
        for (unsigned i = 0; i < out.size(); i++) {
            std::cout << "out" << i << " = " << m.eval(out[i]).get_numeral_uint64() << std::endl;
        }
    }
    else {
        std::cout << "Unsat" << std::endl;
    }

    exit(1);
}
