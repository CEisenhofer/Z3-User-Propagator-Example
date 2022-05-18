#include "common.h"

class SortedPropagator6 : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    z3::expr_vector fixedValues;
    std::unordered_map<z3::expr, uint64_t> model;

    const z3::expr_vector &in;
    const z3::expr_vector &out;
    std::unordered_map<z3::expr, int> astToIndex;

public:

    SortedPropagator6(z3::solver *s, const z3::expr_vector &in, const z3::expr_vector &out) :
            user_propagator_base(s), fixedValues(s->ctx()), in(in), out(out) {

        this->register_fixed();
        this->register_decide();

        for (unsigned i = 0; i < in.size(); i++) {
            this->add(in[i]);
        	astToIndex.emplace(in[i], i + 1);
            this->add(out[i]);
        	astToIndex.emplace(out[i], -(i + 1));
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
                fixedValues.pop_back();
            }
        }
    }

    struct sort_fct {
        bool operator()(const std::pair<uint64_t, unsigned> &o1, const std::pair<uint64_t, unsigned> &o2) const {
            return o1.first < o2.first;
        }
    };

    void fixed(const z3::expr &ast, const z3::expr &value) override {

        if (astToIndex.at(ast) <= 0)
            return;

        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());

        uint64_t v = value.is_true() ? 1 : (value.is_false() ? 0 : value.get_numeral_uint64());
        fixedValues.push_back(ast);
        model.emplace(ast, v);

        if (model.size() < in.size())
            // Not everything assigned so far
            return;

        std::vector<std::pair<uint64_t, unsigned>> sorted;
        sorted.reserve(model.size());
        for (unsigned i = 0; i < in.size(); i++) {
            sorted.emplace_back(model.at(in[i]), i);
        }
        std::sort(sorted.begin(), sorted.end(), sort_fct());
        z3::expr_vector conjunction(ctx());
        z3::expr_vector mapping(ctx());
        mapping.push_back(out[0] == in[sorted[0].second]);
        for (unsigned i = 1; i < sorted.size(); i++) {
            conjunction.push_back(z3::ule(in[sorted[i - 1].second], in[sorted[i].second]));
            mapping.push_back(out[i] == in[sorted[i].second]);
        }
        z3::expr_vector empty(ctx());
        this->propagate(empty, z3::implies(z3::mk_and(conjunction), z3::mk_and(mapping)));
    }

    user_propagator_base *fresh(z3::context &ctx) override { return this; }

    void decide(z3::expr& val, unsigned& bit, Z3_lbool& is_pos) override {
        if (astToIndex.at(val) > 0) {
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
};

int sorting6(unsigned *size) {
    unsigned cnt = *size;
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    z3::expr_vector in(context);
    z3::expr_vector out(context);

    for (unsigned i = 0; i < cnt; i++) {
        in.push_back(context.bv_const((std::string("in") + std::to_string(i)).c_str(), BIT_CNT));
        out.push_back(context.bv_const((std::string("out") + std::to_string(i)).c_str(), BIT_CNT));
    }

    s.add(z3::distinct(in));

    z3::expr_vector counterOrder(context);
    for (int i = 0; i < cnt - 1; i++) {
        counterOrder.push_back(in[i] >= in[i + 1]);
    }
    s.add(z3::mk_and(counterOrder));

    SortedPropagator6 propagator(&s, in, out);

    s.check();
    z3::model m = s.get_model();
    checkSorting(m, in, out);
    return -1;
}
