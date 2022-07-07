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
        this->register_created();
        this->register_decide();
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
            currentSorted[i] = model.at(in[i]);
        }
        std::sort(currentSorted.begin(), currentSorted.end());
        for (unsigned i = 0; i < funcs.size(); i++) {
            z3::expr_vector premiss(ctx());
            for (unsigned j = 0; j < in.size(); j++) {
                premiss.push_back(in[j] == ctx().bv_val(model.at(in[j]), BIT_CNT));
            }
            z3::expr_vector empty(ctx());
            this->propagate(empty, z3::implies(z3::mk_and(premiss), funcs[i] == ctx().bv_val(currentSorted[i], BIT_CNT)));
        }
    }

    void decide(z3::expr& val, unsigned& bit, Z3_lbool& is_pos) override {
        if (hasAllInValues() || astToIndex.at(val) > 0) {
            return;
        }
        for (unsigned i = 0; i < in.size(); i++) {
            if (!model.contains(in[i])) {
                WriteLine("Changed " + val.to_string() + " to " + in[i].to_string());
                val = in[i];
                bit = 0;
                is_pos = Z3_L_UNDEF;
                return;
            }
        }
        assert(false);
    }

    user_propagator_base *fresh(z3::context &ctx) override { return this; }

};

int sorting3(unsigned size, sortingConstraints constraints) {
    /*z3::context context;
    z3::solver s(context, z3::solver::simple());

    z3::sort_vector domain(context);
    z3::expr_vector in(context);
    z3::expr_vector out(context);
    z3::expr_vector funcs(context);

    for (unsigned i = 0; i < size; i++) {
        domain.push_back(context.bv_sort(BIT_CNT));
        in.push_back(context.constant((std::string("in") + std::to_string(i)).c_str(), domain[i]));
    }
    for (unsigned i = 0; i < size; i++) {
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

    applyConstraints(s, in, out, constraints);

    SortedPropagator3 propagator(&s, funcs, in);

    z3::check_result result = s.check();
    if (constraints & outputReverse) {
        assert(result == z3::unsat);
    }
    else {
        z3::model m = s.get_model();
        checkSorting(m, in, out);
    }*/
    return -1;
}
