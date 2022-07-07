#pragma once
#include <queue>

#include "common.h"

class LazySortingNetworkPropagator : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    std::vector<uint64_t> fixedPositions;
    std::unordered_map<uint64_t, unsigned> model;
    symbolicNetwork network;

    std::unordered_map<z3::expr, uint64_t> astToPosition;
    std::unordered_map<uint64_t, z3::expr> positionToAst;

    std::vector<z3::expr_vector> nodes;
    z3::expr_vector empty;

    std::vector<std::pair<int, const z3::expr>> instantiations;
    std::vector<std::pair<int, const z3::expr>> registrations;
    std::unordered_set<z3::expr> alreadyConsidered;

    int decisionLevel = 0;
    const unsigned bvSize;

    const bool forward = false, backward = true;
    const bool guessRatherThanPropagate = true;

    std::random_device rd;
    std::mt19937 rng;
    std::uniform_int_distribution<int> idist;
    std::bernoulli_distribution bdist;

    uint64_t next;

    z3::expr createNode(const unsigned line, const unsigned pos) {
        assert(!nodes.empty() && !nodes[0].empty());
        return ctx().constant((std::string("!x_{") + std::to_string(line) + "," + std::to_string(pos) + "}").c_str(), nodes[0][0].get_sort());
    }

    uint64_t encodePosition(const unsigned short line, const unsigned short pos, const unsigned short bit = -1) const {
        return (uint64_t)((unsigned short)(bit + 1)) | ((uint64_t) line << (8 * sizeof(short))) | ((uint64_t)pos << (2 * 8 * sizeof(short)));
    }

    void decodePosition(const uint64_t enc, unsigned short& line, unsigned short& pos, unsigned short& bit) const {
        bit = ((unsigned short)enc) - 1;
        line = (unsigned short)(enc >> (8 * sizeof(short)));
        pos = (unsigned short)(enc >> (2 * 8 * sizeof(short)));
    }

    void getPosition(const z3::expr& ast, unsigned short& line, unsigned short& pos, unsigned short& bit) const {
        uint64_t p = astToPosition.at(ast);
        decodePosition(p, line, pos, bit);
    }

    bool getModelValue(const uint64_t enc, unsigned& value) const {
        const auto it = model.find(enc);
        if (it != model.end()) {
            value = it->second;
            return true;
        }
        return false;
    }

    bool getModelValue(unsigned short line, unsigned short pos, unsigned& value, const unsigned short bit = -1) const {
        return getModelValue(encodePosition(line, pos, bit), value);
    }

    void initNode(unsigned line, unsigned pos, const z3::expr& e, bool reg) {
        uint64_t p = encodePosition((unsigned short)line, (unsigned short)pos);
        astToPosition.emplace(e, p);
        positionToAst.emplace(p, e);

        if (reg)
            this->add(e, false);

        //if (!guessRatherThanPropagate)
            return;

        for (unsigned k = 0; k < bvSize; k++) {
            p++;
            z3::expr b = e.bit2bool(k);
            astToPosition.emplace(b, p);
            positionToAst.emplace(p, b);

            if (reg)
                this->add(b, false);
        }
    }

    void addAndBits(const z3::expr& e) {
        this->add(e, false);
        //if (!guessRatherThanPropagate)
            return;
        for (unsigned k = 0; k < e.get_sort().bv_size(); k++)
            this->add(e.bit2bool(k), false);
    }

    void propagate(const z3::expr& e, bool force) {
        propagateOrRegister(e, false, force);
    }

    void add(const z3::expr& e, bool force) {
        propagateOrRegister(e, true, force);
    }

    void propagateOrRegister(const z3::expr& e, bool reg, bool force) {

        if (guessRatherThanPropagate && !force && alreadyConsidered.contains(e))
            return;

        if (reg)
            user_propagator_base::add(e);
        else 
            user_propagator_base::propagate(empty, e);

        if (!guessRatherThanPropagate || force)
            return;

        if (reg)
            registrations.emplace_back(decisionLevel, e);
        else
            instantiations.emplace_back(decisionLevel, e);

        alreadyConsidered.insert(e);
    }

public:

    LazySortingNetworkPropagator(z3::solver* s, unsigned bvSize, bool guessRatherThanPropagate) :
        user_propagator_base(s), network(0), empty(ctx()), bvSize(bvSize),
        guessRatherThanPropagate(guessRatherThanPropagate), rng(rd()), idist(0, 0), bdist(), next((uint64_t)-1) {

        assert(forward || backward);

        this->register_fixed();

        if (guessRatherThanPropagate)
            this->register_decide();
    }

    void addInputOutput(const symbolicNetwork& network, const z3::expr_vector& inputs, const z3::expr_vector& outputs) {
        unsigned start = this->network.size();
        this->network.merge(network);
        for (unsigned i = 0; i < inputs.size(); i++) {
            nodes.emplace_back(ctx());
            nodes[i + start].push_back(inputs[i]);

            initNode(i + start, 0, inputs[i], forward);

            for (unsigned j = 0; j < this->network.getCurrentLineSize(i + start); j++) {
                z3::expr e = this->network.getCurrentLineSize(i + start) == j + 1 ? outputs[i] : createNode(i + start, j + 1);
                nodes[i + start].push_back(e);
                initNode(i + start, j + 1, e, false);
            }

            if (backward || guessRatherThanPropagate)
                this->add(nodes[i + start].back(), false);
        }
        idist = std::uniform_int_distribution<int>(0, inputs.size() - 1);
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
                model.erase(fixedPositions[j - 1]);
                fixedPositions.pop_back();
            }
        }
        decisionLevel -= (int)num_scopes;
        assert(decisionLevel >= 0);
        if (guessRatherThanPropagate) {
            for (auto& inst : instantiations) {
                if (inst.first > decisionLevel) {
                    inst.first = decisionLevel;
                    this->propagate(inst.second, true);
                }
            }
            for (auto& reg : registrations) {
                if (reg.first > decisionLevel) {
                    reg.first = decisionLevel;
                    this->add(reg.second, true);
                }
            }
        }
    }

    bool first = false;

    void fixed(const z3::expr& ast, const z3::expr& value) override {
        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        /*if (!first && guessRatherThanPropagate) {

            exprNetwork network(ctx(), nodes.size());
            for (unsigned i = 0; i < nodes.size(); i++) {
                network.add(i, nodes[i][0]);
            }
            // insertion sort: O(n^2)
            for (unsigned i = 0; i < nodes.size() - 1; i++) {
                for (unsigned j = 0; j < nodes.size() - i - 1; j++) {
                    network.addComparision(j, j + 1);
                }
            }

            const auto& outputExpr = network.getOutputs();

            for (unsigned i = 0; i < outputExpr.size(); i++) {
                this->propagate(empty,
                nodes[i].back() == outputExpr[i]);
                instantiations.emplace_back(decisionLevel,
                    nodes[i].back() == outputExpr[i]);
            }

            first = false;
        }*/
        unsigned val = value.is_true() ? 1 : (value.is_false() ? 0 : value.get_numeral_uint());
        uint64_t p = astToPosition.at(ast);
        fixedPositions.push_back(p);
        unsigned short line, pos, bit;
        decodePosition(p, line, pos, bit);
        model.emplace(p, val);

        /*if (guessRatherThanPropagate)
            return;*/

        if (next == p)
            setNext();

        if (bit != (unsigned short)-1)
            return;
        
        const z3::expr_vector empty(ctx());

        if (pos + 1 < nodes[line].size()) { // not an output 
            destination destination = network.getDestination(line, pos);
            unsigned siblingVal;
            if (getModelValue(destination.line, destination.position, siblingVal)) {
                // forward propagation
                uint64_t nextAstPos = encodePosition(line, pos + 1);
                uint64_t siblingAstPos = encodePosition(destination.line, destination.position);
                uint64_t siblingNextAstPos = encodePosition(destination.line, destination.position + 1);

                const auto& nextAst = positionToAst.at(nextAstPos);
                const auto& siblingAst = positionToAst.at(siblingAstPos);
                const auto& siblingNextAst = positionToAst.at(siblingNextAstPos);

                // we register them always in case it is not an output node. Z3 will anyway check if they have been registered already
                if (pos + 1 <= nodes[line].size())
                    addAndBits(nextAst);
                if (destination.position + 1 <= nodes[destination.line].size())
                    addAndBits(siblingNextAst);

                if (val == siblingVal || ((line < destination.line) == (val < siblingVal))) {
                    // already ordered correctly
                    unsigned o1, o2;
                    /*if (!guessRatherThanPropagate || 
                        (getModelValue(nextAstPos, o1) && getModelValue(siblingNextAst, o2) &&
                            (line <= destination.line 
                                ? !(val == o1 && siblingVal == o2)
                                : !(val == o2 && siblingVal == o1)))) {*/
                        // simply pass them through
                        if (line <= destination.line) {
                            const z3::expr pr = z3::implies(z3::ule(ast, siblingAst), nextAst == ast && siblingNextAst == siblingAst);
                            this->propagate(pr, false);
                        }
                        else {
                            const z3::expr pr = z3::implies(z3::ule(siblingAst, ast), nextAst == ast && siblingNextAst == siblingAst);
                            this->propagate(pr, false);
                        }
                    //}
                }
                else {
                    // not ordered correctly
                    // add if-then-else
                    if (line <= destination.line) {
                        const z3::expr pr = z3::ite(z3::ule(ast, siblingAst),
                            nextAst == ast && siblingNextAst == siblingAst,
                            nextAst == siblingAst && siblingNextAst == ast);
                        this->propagate(pr, false);
                    }
                    else {
                        const z3::expr pr = z3::ite(z3::ule(siblingAst, ast),
                            nextAst == ast && siblingNextAst == siblingAst,
                            nextAst == siblingAst && siblingNextAst == ast);
                        this->propagate(pr, false);
                    }
                }
            }
        }
        if (pos > 0) { // not an input
            destination destination = network.getDestination(line, pos - 1);
            // backward propagation
            const auto& prevAst = positionToAst.at(encodePosition(line, pos - 1));
            const auto& prevSiblingAst = positionToAst.at(encodePosition(destination.line, destination.position));

            // we register them always in case it is not an input node. Z3 will anyway check if they have been registered already
            if (pos - 1 > 0)
                addAndBits(prevAst);
            if (destination.position > 0)
                addAndBits(prevSiblingAst);

            this->propagate(z3::ite(z3::ule(prevAst, prevSiblingAst),
                ast == (line < destination.line ? prevAst : prevSiblingAst),
                ast == (line < destination.line ? prevSiblingAst : prevAst)), false);
        }
    }

#define RETURN(n, b, p) { ast = (positionToAst.at(n)); next = (n); bit = (b); is_pos = (p); return; }

    void setNext() {
        z3::expr ast(ctx());
        unsigned bit = 0;
        Z3_lbool is_pos = Z3_L_UNDEF;
        setDecision2(ast, bit, is_pos);
        next_split(ast, bit, is_pos);
    }

    /*void setDecision(z3::expr& ast, unsigned& bit, Z3_lbool& is_pos) {
        unsigned prev;
        for (unsigned i = 0; i < nodes.size(); i++) {
            z3::expr_vector& v = nodes[i];
            const unsigned s = v.size();
            for (unsigned j = 0; j < s; j++) {
                uint64_t p = encodePosition(i, j);
                if (getModelValue(p, prev))
                    // already assigned
                    continue;

                if (j == 0) {
                    // just guess input bits
                    for (unsigned k = 0; k < bvSize; k++) {
                        p++;
                        if (!getModelValue(p, prev))
                            RETURN(p, 0, Z3_L_UNDEF);
                    }
                    break;
                }

                destination destination = network.getDestination(i, j - 1);
                unsigned other;

                // get value of sibling of predecessor
                if (!getModelValue((unsigned short)destination.line, (unsigned short)destination.position, other))
                    // blocked
                    break;
                //assert(prev == other || ((i < destination.line) == (prev < other))); // it has to be sorted

                unsigned ignored;
                uint64_t nextAstPos = encodePosition((unsigned short)i, (unsigned short)j);
                for (unsigned k = 0; k < bvSize; k++) {
                    nextAstPos++;
                    if (!getModelValue(nextAstPos, ignored))
                        RETURN(nextAstPos, 0,
                            ((i < destination.line) == (prev < other)) ?
                            ((prev >> k) & 1) ? Z3_L_TRUE : Z3_L_FALSE :
                            ((other >> k) & 1) ? Z3_L_TRUE : Z3_L_FALSE
                        );
                }

                uint64_t siblingNextAstPos = encodePosition((unsigned short)(destination.line), (unsigned short)(destination.position + 1));
                for (unsigned k = 0; k < bvSize; k++) {
                    siblingNextAstPos++;
                    if (!getModelValue(siblingNextAstPos, ignored))
                        RETURN(siblingNextAstPos, 0,
                            ((i < destination.line) == (prev < other)) ?
                            ((other >> k) & 1) ? Z3_L_TRUE : Z3_L_FALSE :
                            ((prev >> k) & 1) ? Z3_L_TRUE : Z3_L_FALSE
                        );
                }
            }
        }
    }*/
    void setDecision2(z3::expr& ast, unsigned& bit, Z3_lbool& is_pos) {
        int pos = idist(rng);
        bool fwd = bdist(rng);
        int inc = fwd ? 1 : -1;

        for (unsigned i = 0; i < nodes.size(); i++, pos = (pos + 1) % nodes.size()) {
            for (int j = fwd ? 0 : nodes[i].size() - 1; j >= 0 && j < nodes[i].size(); j += inc) {
                uint64_t p = encodePosition((unsigned short)i, (unsigned short)j);
                unsigned v;
                if (!getModelValue(p, v)) {
                    ast = nodes[i][j];
                    bit = 0;
                    is_pos = Z3_L_UNDEF;
                    this->add(ast, false);
                    return;
                }
            }
        }
    }

    void decide(z3::expr& ast, unsigned& bit, Z3_lbool& is_pos) override {
        if (next != (uint64_t)-1 && astToPosition.at(ast) == next)
            return;
        //setDecision(ast, bit, is_pos);
        setDecision2(ast, bit, is_pos);
    }

    user_propagator_base* fresh(z3::context& ctx) override { return this; }

    z3::expr_vector getOutputs() {
        z3::expr_vector output(ctx());
        for (unsigned i = 0; i < nodes.size(); i++) {
            output.push_back(nodes[i].back());
        }
        return output;
    }

    z3::expr_vector getInputs() {
        z3::expr_vector input(ctx());
        for (unsigned i = 0; i < nodes.size(); i++) {
            input.push_back(nodes[i][0]);
        }
        return input;
    }
};

inline void testIntervalDistinct() {

}