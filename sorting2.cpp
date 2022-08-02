#include "common.h"

class SortedPropagator : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    z3::expr_vector fixedValues;
    std::unordered_map<z3::expr, uint64_t> model;

    unsigned funcValues = 0, inValues = 0, outValues = 0;
    const z3::expr func;
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
        this->register_created();
        this->register_decide();

        assert(in.size() == out.size());
        astToIndex.emplace(func, 0);
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

        if (model.at(func)) {
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
            // std::cout << "Prop: " << z3::implies(z3::mk_and(premiss), z3::mk_and(sorted)).to_string() << std::endl;
            this->propagate(in, z3::implies(z3::mk_and(premiss), z3::mk_and(sorted)));
        }
        else {
            assert(false);
        }
    }

    void decide(z3::expr& val, unsigned& bit, Z3_lbool& is_pos) override {
        if (hasAllInValues() || astToIndex.at(val) >= 0) {
            return;
        }
        for (unsigned i = 0; i < in.size(); i++) {
            if (!model.contains(in[i])) {
                WriteLine("Changed " + val.to_string() + " to " + in[i].to_string());
                val = in[i];
                bit = 0;
                is_pos = rand() % 2 == 0 ? Z3_L_TRUE : Z3_L_FALSE;
                return;
            }
        }
        assert(false);
    }

    user_propagator_base *fresh(z3::context &ctx) override { return this; }

};

int sorting2(unsigned size, sortingConstraints constraints) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    SortedPropagator* propagator = nullptr;

    struct sort : multiSort {

        SortedPropagator** propagator;
        z3::solver& s;

        sort(SortedPropagator** propagator, z3::solver& s) : propagator(propagator), s(s) { }

        void add(z3::expr_vector& in, z3::expr_vector& out) override {
            z3::expr_vector args(in.ctx());
            z3::sort_vector domain(in.ctx());

            for (unsigned i = 0; i < in.size(); i++) {
                domain.push_back(in.ctx().bv_sort(BIT_CNT));
                args.push_back(in.back());
            }
            for (unsigned i = 0; i < in.size(); i++) {
                domain.push_back(domain[i]);
                args.push_back(out.back());
            }

            z3::func_decl sorted = in.ctx().user_propagate_function(in.ctx().str_symbol("sorted"), domain, in.ctx().bool_sort());

            auto func = sorted(args);
            s.add(func);
            *propagator = new SortedPropagator(&s, func, in, out);
        }
    };

    sort sort(&propagator, s);

    applyConstraints(s, size, sort, constraints);

    z3::check_result result = s.check();
    printStatistics(s);
    if (constraints & outputReverse) {
        assert(result == z3::unsat);
    }
    else {
        z3::model m = s.get_model();
        checkSorting(m, *sort.in, *sort.out, constraints);
    }
    delete propagator;
    return -1;
}
