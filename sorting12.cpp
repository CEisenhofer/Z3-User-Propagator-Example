#include "common.h"

class BijectionPropagator : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    z3::expr_vector fixedAsts;
    std::vector<int> fixedPositions;

    std::vector<unsigned> model;
    std::vector<unsigned> assignedBits;
    std::vector<unsigned> alreadyAssigned;
    std::vector<unsigned> inverseModel;

    int decisionLevel = 0;
    int bits = 0;

    std::vector<std::pair<int, const z3::expr>> instantiations;
    z3::expr_vector matchingExprs;
    std::vector<z3::expr_vector> bitExprs;

    std::unordered_map<z3::expr, unsigned> astToPos;
    std::unordered_map<unsigned, z3::expr> posToAst;

    z3::expr_vector vec;
    z3::expr_vector empty;

    std::random_device rd;
    std::mt19937 rng;
    std::uniform_int_distribution<int> idist;

public:

    BijectionPropagator(z3::solver* s, const z3::expr_vector& in, const z3::expr_vector& out)
        : user_propagator_base(s), fixedAsts(ctx()), matchingExprs(ctx()), vec(ctx()), empty(ctx()), rng(rd()), idist(0, in[0].get_sort() - 1) {

        assert(in.size() == out.size());
        this->register_fixed();

        const z3::sort range = in[0].get_sort();
        z3::sort_vector domain(ctx());
        domain.push_back(ctx().bv_sort(in.size()));
        bits = domain.back().bv_size();

        z3::func_decl mappingFct = ctx().function("mappingFct", domain, range);

        for (int i = 0; i < in.size(); i++) {

            z3::expr e = ctx().constant(("mapping_" + std::to_string(i)).c_str(), domain.back());
            matchingExprs.push_back(e);

            z3::expr index = ctx().bv_val(1, in.size());
            index = z3::shl(index, i);
            s->add(in[i] == mappingFct(index));
            s->add(out[i] == mappingFct(e));

            z3::expr_vector bitSequence(ctx());

            for (int j = 0; j < bits; j++) {
                z3::expr e2 = e.bit2bool(j);
                this->add(e2);
                bitSequence.push_back(e2);
                astToPos.emplace(e2, model.size());
                posToAst.emplace(model.size(), e2);
                model.push_back(-1);
            }
            bitExprs.push_back(bitSequence);
            alreadyAssigned.push_back((unsigned)-1);
            assignedBits.push_back(0);
            inverseModel.push_back(-1);
        }

        this->register_decide();
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
                model[p] = -1;
                fixedPositions.pop_back();
                fixedAsts.pop_back();
                const unsigned mp1 = p / bits;
                const unsigned mp2 = p % bits;
                assignedBits[mp1]--;
                assert(assignedBits[mp1] != (unsigned)-1);
                if (alreadyAssigned[mp1] == p) {
                    assert(inverseModel[mp2] == mp1);
                    alreadyAssigned[mp1] = (unsigned)-1;
                    inverseModel[mp2] = (unsigned)-1;
                }
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

        const unsigned mp1 = p / bits;
        const unsigned mp2 = p % bits;

        unsigned assigned = ++assignedBits[mp1];

        if (val) {
            if (alreadyAssigned[mp1] != (unsigned)-1) {
                // not more than one must be set
                vec.resize(0);
                vec.push_back(ast);
                vec.push_back(posToAst.at(alreadyAssigned[mp1]));
                this->conflict(vec);
                return;
            }

            if (inverseModel[mp2] != (unsigned)-1) {
                // multiple elements may not map to the same element
                vec.resize(0);
                vec.push_back(ast);
                vec.push_back(posToAst.at(alreadyAssigned[inverseModel[mp2]]));
                this->conflict(vec);
                return;
            }

            alreadyAssigned[mp1] = p;
            inverseModel[mp2] = mp1;
        }

        if (assigned == bits && val == 0 && alreadyAssigned[mp1] == (unsigned)-1) {
            // at least one must be set
            z3::expr_vector& conf = bitExprs[mp1];
            this->conflict(conf);
        }
    }

    void decide(z3::expr& ast, unsigned&, Z3_lbool& phase) override {
        unsigned p = astToPos.at(ast);
        const unsigned mp1 = p / bits;
        const unsigned mp2 = p % bits;

        if (alreadyAssigned[mp1] != -1 || inverseModel[mp2] != (unsigned)-1) {
            phase = Z3_L_FALSE;
        }
        else if (assignedBits[mp1] == bits - 1) {
            phase = Z3_L_TRUE;
        }
        else {
            phase = idist(rng) == 0 ? Z3_L_TRUE : Z3_L_FALSE;
        }
    }

    user_propagator_base* fresh(z3::context& ctx) override {
        assert(false);
        return nullptr;
    }
};

int sorting12(unsigned size, sortingConstraints constraints) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    BijectionPropagator* propagator = nullptr;

    struct sort : multiSort {

        z3::solver& s;
        BijectionPropagator** propagator;
        sort(z3::solver& s, BijectionPropagator** propagator) : s(s), propagator(propagator) {}

        void add(z3::expr_vector& in, z3::expr_vector& out) override {
            for (int i = 1; i < out.size(); i++) {
                s.add(z3::ule(out[i - 1], out[i]));
            }
            *propagator = new BijectionPropagator(&s, in, out);
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
