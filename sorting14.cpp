#include "common.h"

class BijectionPropagator2 : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    z3::expr_vector fixedAsts;
    std::vector<int> fixedPositions;

    std::vector<unsigned> model;
    std::vector<unsigned> inverseModel;

    int decisionLevel = 0;
    int bits = 0;

    std::vector<std::pair<int, const z3::expr>> instantiations;
    
    std::unordered_map<z3::expr, unsigned> astToPos;
    std::unordered_map<unsigned, z3::expr> posToAst;

    z3::expr_vector conflicting;
    z3::expr_vector empty;


public:

    BijectionPropagator2(z3::solver* s, const z3::expr_vector& in, const z3::expr_vector& out)
        : user_propagator_base(s), fixedAsts(ctx()), conflicting(ctx()), empty(ctx()) {

        assert(in.size() == out.size());
        this->register_fixed();

        const z3::sort range = in[0].get_sort();
        z3::sort_vector domain(ctx());
        domain.push_back(ctx().bv_sort(log2i(in.size())));
        bits = domain.back().bv_size();

        z3::func_decl mappingFct = ctx().function("mappingFct", domain, range);

        for (int i = 0; i < in.size(); i++) {

            z3::expr e = ctx().constant(("mapping_" + std::to_string(i)).c_str(), domain.back());
            
            s->add(in[i] == mappingFct(i));
            s->add(out[i] == mappingFct(e));
            s->add(z3::ule(e, in.size() - 1));

            astToPos.emplace(e, model.size());
            posToAst.emplace(model.size(), e);
            model.push_back(-1);
            inverseModel.push_back(-1);
            this->add(e);
        }
    }

    void push() override {
        prevFixedCnt.push(fixedPositions.size());
        decisionLevel++;
    }

    void pop(unsigned int num_scopes) override {
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned prevFixed = prevFixedCnt.top();
            prevFixedCnt.pop();
            for (unsigned j = fixedPositions.size(); j > prevFixed; j--) {
                const int p = fixedPositions[j - 1];
                unsigned val = model[p];
                model[p] = -1;
                fixedPositions.pop_back();
                fixedAsts.pop_back();
                if (inverseModel[val] == p) 
					inverseModel[val] = (unsigned)-1;
            }
        }
        decisionLevel -= (int)num_scopes;
        assert(decisionLevel >= 0);
        for (auto& inst : instantiations) {
            if (inst.first > decisionLevel) {
                z3::expr_vector empty(ctx());
                inst.first = decisionLevel;
                this->propagate(empty, inst.second);
            }
        }
    }

    void fixed(const z3::expr& ast, const z3::expr& value) override {
        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        unsigned val = value.is_true() ? 1 : (value.is_false() ? 0 : value.get_numeral_uint());
        int p = astToPos.at(ast);
        fixedAsts.push_back(ast);
        fixedPositions.push_back(p);
        model[p] = val;

        if (inverseModel[val] != (unsigned)-1) {
            conflicting.resize(0);
            conflicting.push_back(ast);
            conflicting.push_back(posToAst.at(inverseModel[val]));
            this->conflict(conflicting);
        }
        else {
            inverseModel[val] = p;
        }
    }

    user_propagator_base* fresh(z3::context& ctx) override {
        assert(false);
        return nullptr;
    }
};

int sorting14(unsigned size, sortingConstraints constraints) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    BijectionPropagator2* propagator = nullptr;

    struct sort : multiSort {

        z3::solver& s;
        BijectionPropagator2** propagator;
        sort(z3::solver& s, BijectionPropagator2** propagator) : s(s), propagator(propagator) {}

        void add(z3::expr_vector& in, z3::expr_vector& out) override {
            for (int i = 1; i < out.size(); i++) {
                s.add(z3::ule(out[i - 1], out[i]));
            }
            *propagator = new BijectionPropagator2(&s, in, out);
        }
    };

    sort sort(s, &propagator);

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
    delete propagator;
    return -1;
}
