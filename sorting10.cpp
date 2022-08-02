#include "common.h"

class MatchingPropagator : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    z3::expr_vector fixedAsts;
    std::vector<int> fixedPositions;
    std::unordered_map<int, unsigned> model;

    int decisionLevel = 0;

    std::vector<std::pair<int, const z3::expr>> instantiations;
    const z3::expr_vector& in;
    const z3::expr_vector& out;
    
    std::unordered_map<z3::expr, int> astToPos;
    std::unordered_map<int, z3::expr> posToAst;

    std::unordered_map<int, int> matching;

    z3::expr_vector vec;
    z3::expr_vector empty;
    z3::expr_vector justfc;

    bool tryGetModel(int p, unsigned& v) const {
        auto it = model.find(p);
        if (it == model.end())
            return false;
        v = it->second;
        return true;
    }

    bool tryGetMatching(int p, int& v) const {
        auto it = matching.find(p);
        if (it == matching.end())
            return false;
        v = it->second;
        return true;
    }


public:

    MatchingPropagator(z3::solver* s, const z3::expr_vector& in, const z3::expr_vector& out)
        : user_propagator_base(s), fixedAsts(ctx()), in(in), out(out), vec(ctx()), empty(ctx()), justfc(ctx()) {

        assert(in.size() == out.size());
        this->register_fixed();
        
        for (int i = 0; i < in.size(); i++) {
            this->add(in[i]);
            this->add(out[i]);

            astToPos.emplace(in[i], (i + 1));
            posToAst.emplace((i + 1), in[i]);

            astToPos.emplace(out[i], -(i + 1));
            posToAst.emplace(-(i + 1), out[i]);
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
                model.erase(p);
                fixedPositions.pop_back();
                fixedAsts.pop_back();

                int p2;
                if (tryGetMatching(p, p2)) {
                    matching.erase(p);
                    assert(matching.contains(p2));
                    matching.erase(p2);
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

    void matchAnythingNotAlreadyMatched(const z3::expr& ast, const z3::expr_vector& other, const z3::expr_vector& current, int neg, int start, int end, bool protectMatched) {

        bool containsUnassiged = false;

        for (int i = start; i <= end; i++) {
            unsigned ignored;
            if (!tryGetModel(neg * (i + 1), ignored)) {
                containsUnassiged = true;
                break;
            }
        }

        // justfc.push_back(ast);

        if (!containsUnassiged) {
            start = 0;
            end = other.size() - 1;
        }

        for (int i = start; i <= end; i++) {
            justfc.push_back(other[i]);
            unsigned ignored;
            int matched = 0;
            unsigned v;
            if (!tryGetModel(neg * (i + 1), v) || (!containsUnassiged && !tryGetMatching(neg * (i + 1), matched))) {
                vec.push_back(ast == other[i]);
            }
            else if (matched != 0) {
                justfc.push_back(current[abs(matched) - 1]);
            }
        }

        this->propagate(justfc, z3::mk_or(vec));
    }

    void fixed(const z3::expr& ast, const z3::expr& value) override {
        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        unsigned val = value.get_numeral_uint();
        int p1 = astToPos.at(ast);
        fixedAsts.push_back(ast);
        fixedPositions.push_back(p1);
        model.emplace(p1, val);

        assert(p1 != 0);

        int neg;

        if (p1 < 0) {
            neg = 1;
        }
        else {
            neg = -1;
        }

        const z3::expr_vector& other = p1 > 0 ? out : in;
        const z3::expr_vector& current = p1 > 0 ? in : out;
        
        // first try matching without adding to vector as this is expensive
        for (int i = 0; i < in.size(); i++) {
            int p2 = (i + 1) * neg;
            unsigned val2;
            int ignored;
            if (tryGetModel(p2, val2)) {
                if (val2 == val && !tryGetMatching(p2, ignored)) {
                    assert(!matching.contains(p1));
                    assert(!matching.contains(p2));
                    matching.emplace(p1, p2);
                    matching.emplace(p2, p1);
                    return;
                }
            }
        }

        // nothing matched
        vec.resize(0);
        justfc.resize(0);

        // assert that one element has to match
        if (p1 > 0) {
            // the out position has to be sorted
            int end, start;
            unsigned val2;
            for (end = 0; end < in.size(); end++) {
                if (tryGetModel(-(end + 1), val2) && val < val2)
                    break;
            }
            for (start = end - 1; start >= 0; start--) {
                if (tryGetModel(-(start + 1), val2) && val > val2)
                    break;
            }

            matchAnythingNotAlreadyMatched(ast, other, current, -1, start + 1, end - 1, false);
        }
        else {
            // just put it somewhere
            matchAnythingNotAlreadyMatched(ast, other, current, 1, 0, other.size() - 1, true);
        }
    }

    user_propagator_base* fresh(z3::context& ctx) override {
        assert(false);
        return nullptr;
    }
};

int sorting10(unsigned size, sortingConstraints constraints) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    MatchingPropagator* propagator = nullptr;

    struct sort : multiSort {

        z3::solver& s;
        MatchingPropagator** propagator;
        sort(z3::solver& s, MatchingPropagator** propagator) : s(s), propagator(propagator) {}

        void add(z3::expr_vector& in, z3::expr_vector& out) override {
            for (int i = 1; i < out.size(); i++) {
                s.add(z3::ule(out[i - 1], out[i]));
            }
            *propagator = new MatchingPropagator(&s, in, out);
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
