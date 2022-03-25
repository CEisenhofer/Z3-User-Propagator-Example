#include "common.h"

class SortedPropagator3 : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    z3::expr_vector fixedValues;
    std::unordered_map<z3::expr, uint64_t> model;

    const z3::expr_vector &funcs;
    const z3::expr_vector &in;

    std::vector<uint64_t> currentSorted;
    std::unordered_map<z3::expr, int> astToIndex;
    unsigned fixedInputs = 0;
    bool alreadyPropagated = false;

    inline bool hasAllInValues() const {
        return fixedInputs == in.size();
    }

public:

    SortedPropagator3(z3::solver *s, const z3::expr_vector &funcs, const z3::expr_vector &in) :
            user_propagator_base(s), fixedValues(s->ctx()), funcs(funcs), in(in) {

        this->register_fixed();
        assert(in.size() == funcs.size());
        currentSorted.reserve(in.size());
        for (unsigned i = 0; i < in.size(); i++) {
            astToIndex.emplace(in[i], i + 1);
            astToIndex.emplace(funcs[i], -(i + 1));
            this->add(in[i]);
            currentSorted.push_back(0);
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
                if (astToIndex.at(fixedValues[j - 1]) > 0) {
                    fixedInputs--;
                }
                fixedValues.pop_back();
                alreadyPropagated = false;
            }
        }
    }

    void fixed(const z3::expr &ast, const z3::expr &value) override {
        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        uint64_t v = value.is_true() ? 1 : (value.is_false() ? 0 : value.get_numeral_uint64());
        fixedValues.push_back(ast);
        model.emplace(ast, v);

        if (astToIndex.at(ast) > 0) {
            fixedInputs++;
        }

        if (!hasAllInValues() || alreadyPropagated)
            // Not everything assigned so far
            return;

        alreadyPropagated = true;

        for (unsigned i = 0; i < in.size(); i++) {
            uint64_t w = model.at(in[i]);
            currentSorted.push_back(w);
        }
        std::sort(currentSorted.begin(), currentSorted.end());
        for (unsigned i = 0; i < funcs.size(); i++) {
            z3::expr_vector premiss(ctx());
            for (unsigned j = 0; j < in.size(); j++) {
                premiss.push_back(in[j] == ctx().bv_val(model.at(in[j]), BIT_CNT));
            }
            z3::expr_vector empty(ctx());
            // std::cout << "Prop: " << z3::implies(z3::mk_and(premiss), z3::mk_and(sorted)).to_string() << std::endl;
            this->propagate(empty, z3::implies(z3::mk_and(premiss), funcs[i] == ctx().bv_val(currentSorted[i], BIT_CNT)));
        }
    }

    user_propagator_base *fresh(z3::context &ctx) override { return this; }

};

void sorting3() {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    z3::sort_vector domain(context);
    z3::expr_vector in(context);
    z3::expr_vector out(context);
    z3::expr_vector funcs(context);

    std::cout << "Sorting (3) " << SORT_CNT << " elements" << std::endl;
    for (unsigned i = 0; i < SORT_CNT; i++) {
        domain.push_back(context.bv_sort(BIT_CNT));
        in.push_back(context.constant((std::string("in") + std::to_string(i)).c_str(), domain[i]));
    }
    for (unsigned i = 0; i < SORT_CNT; i++) {
        z3::func_decl sorted = context.user_propagate_function(
                context.str_symbol(("sorted_" + std::to_string(i)).c_str()),
                domain,
                domain[0]);
        z3::expr func = sorted(in);
        funcs.push_back(func);
        z3::expr o = context.constant((std::string("out") + std::to_string(i)).c_str(), domain[i]);
        s.add(o == func);
        out.push_back(o);
    }

    s.add(z3::distinct(in));

    SortedPropagator3 propagator(&s, funcs, in);

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
