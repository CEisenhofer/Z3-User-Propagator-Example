#include "common.h"

class LazySortingNetworkPropagator : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    std::vector<uint64_t> fixedPositions;
    std::unordered_map<uint64_t, uint64_t> model;
    const symbolicNetwork& network;

    std::unordered_map<z3::expr, uint64_t> astToPosition;
    std::unordered_map<uint64_t, z3::expr> positionToAst;

    std::vector<z3::expr_vector> nodes;

    inline z3::expr createNode(unsigned line, unsigned pos) {
        assert(!nodes.empty() && !nodes[0].empty());
        return ctx().constant((std::string("!x_{") + std::to_string(line) + "," + std::to_string(pos) + "}").c_str(), nodes[0][0].get_sort());
    }

    inline uint64_t encodePosition(unsigned line, unsigned pos) const {
        return (uint64_t)line | ((uint64_t)pos << (8 * sizeof(unsigned)));
    }

    inline void decodePosition(uint64_t enc, unsigned& line, unsigned& pos) const {
        line = (unsigned)enc;
        pos = (unsigned)(enc >> (8 * sizeof(unsigned)));
    }

    inline void getPosition(const z3::expr& ast, unsigned& line, unsigned& pos) const {
        uint64_t p = astToPosition.at(ast);
        decodePosition(p, line, pos);
    }

    bool getModelValue(unsigned line, unsigned pos, unsigned& value) const {
        const auto it = model.find(encodePosition(line, pos));
        if (it != model.end()) {
            value = it->second;
            return true;
        }
        return false;
    }

public:

    LazySortingNetworkPropagator(z3::solver* s, const symbolicNetwork& network, const z3::expr_vector& inputs) : user_propagator_base(s), network(network) {

        this->register_fixed();

        for (unsigned i = 0; i < inputs.size(); i++) {
            nodes.emplace_back(s->ctx());
            nodes[i].push_back(inputs[i]);
            this->add(inputs[i]);

            astToPosition.emplace(inputs[i], encodePosition(i, 0));
            positionToAst.emplace(encodePosition(i, 0), inputs[i]);

            for (unsigned j = 0; j < network.getCurrentLineSize(i); j++) {
                z3::expr e = createNode(i, j + 1);
                nodes[i].push_back(e);
                astToPosition.emplace(e, encodePosition(i, j + 1));
                positionToAst.emplace(encodePosition(i, j + 1), e);
            }
        }
    }

    void push() override {
        prevFixedCnt.push(fixedPositions.size());
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
    }

    void fixed(const z3::expr& ast, const z3::expr& value) override {
        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        unsigned val = value.get_numeral_uint();
        uint64_t p = astToPosition.at(ast);
        fixedPositions.push_back(p);
        unsigned line, pos;
        decodePosition(p, line, pos);
        model.emplace(p, val);

        if (pos + 1 >= nodes[line].size()) {
            // node is already an output node
            return;
        }

        // get other input of next comparison
        destination destination = network.getDestination(line, pos);
        unsigned siblingVal;

    	if (getModelValue(destination.line, destination.position, siblingVal)) {
            // forward propagation
            z3::expr_vector empty(ctx());
            const auto& nextAst = positionToAst.at(encodePosition(line, pos + 1));
            const auto& siblingAst = positionToAst.at(encodePosition(destination.line, destination.position));
            const auto& siblingNextAst = positionToAst.at(encodePosition(destination.line, destination.position + 1));

            // we register them always in case it is not an output node. Z3 will anyway check if they have been registered already
            if (pos + 1 <= nodes[line].size())
                this->add(nextAst);
            if (destination.position + 1 <= nodes[destination.line].size())
                this->add(siblingNextAst);

            if (val == siblingVal || ((line < destination.line) == (val < siblingVal))) {
                // already ordered correctly
                // simply pass them through
                if (line <= destination.line) {
                    this->propagate(empty, z3::implies(z3::ule(ast, siblingAst), nextAst == ast && siblingNextAst == siblingAst));
                }
                else {
                    this->propagate(empty, z3::implies(z3::ule(siblingAst, ast), nextAst == ast && siblingNextAst == siblingAst));
                }
            }
            else {
                // not ordered correctly
                // add if-then-else
                if (line <= destination.line) {
                	this->propagate(empty, z3::ite(z3::ule(ast, siblingAst),
                        nextAst == ast && siblingNextAst == siblingAst,
                        nextAst == siblingAst && siblingNextAst == ast));
                }
                else {
                    this->propagate(empty, z3::ite(z3::ule(siblingAst, ast),
                        nextAst == ast && siblingNextAst == siblingAst,
                        nextAst == siblingAst && siblingNextAst == ast));
                }
            }
        }
    }

    user_propagator_base* fresh(z3::context& ctx) override { return this; }

    z3::expr_vector getOutputs() {
        z3::expr_vector output(ctx());
        for (unsigned i = 0; i < nodes.size(); i++) {
            output.push_back(nodes[i].back());
        }
        return output;
    }
};

int sorting8(unsigned size, sortingConstraints constraints) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    symbolicNetwork network(size);
    z3::expr_vector inputs(context);

    for (unsigned i = 0; i < size; i++) {
        inputs.push_back(context.bv_const(("in_" + std::to_string(i)).c_str(), BIT_CNT));
    }

    // odd-even sort: O(n*log(n)^2)
    for (unsigned p = 1; p < size; p <<= 1) {
        for (unsigned k = p; k >= 1; k >>= 1) {
            for (unsigned j = k % p; j < size - k; j += 2 * k) {
                for (unsigned i = 0; i < MIN(k, size - j - k); i++) {
                    if ((i + j) / (2 * p) == (i + j + k) / (2 * p)) {
                        network.addComparision(i + j, i + j + k);
                    }
                }
            }
        }
    }
    /*for (unsigned i = 0; i < cnt - 1; i++) {
        for (unsigned j = 0; j < cnt - i - 1; j++) {
            network.addComparision(j, j + 1);
        }
    }*/


    s.add(z3::distinct(inputs));

    z3::expr_vector counterOrder(context);
    for (int i = 0; i < size - 1; i++) {
        counterOrder.push_back(inputs[i] >= inputs[i + 1]);
    }
    s.add(z3::mk_and(counterOrder));

    LazySortingNetworkPropagator propagator(&s, network, inputs);

    s.check();
    z3::model m = s.get_model();
    checkSorting(m, inputs, propagator.getOutputs());
    return -1;
}
