#include "LazySortingNetworkPropagator.h"

class SortedPropagator5 : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    std::vector<uint64_t> fixedPositions;
    std::unordered_map<uint64_t, uint64_t> model;

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

    inline void decodePosition(uint64_t enc, unsigned &line, unsigned &pos) const {
        line = (unsigned)enc;
        pos = (unsigned)(enc >> (8 * sizeof(unsigned)));
    }

    inline void getPosition(const z3::expr &ast, unsigned &line, unsigned &pos) const {
        uint64_t p = astToPosition.at(ast);
        decodePosition(p, line, pos);
    }

    inline void getSibling(unsigned line, unsigned pos, unsigned &siblingLine, unsigned &siblingPos) {
        if (line < 0 || line >= nodes.size()) {
            // just invalid
            siblingLine = -1;
            return;
        }
        if (pos <= 0) {
            // inputs do not have siblings
            siblingLine = -1;
            return;
        }
        if (line == 0) {
            // first line is special
            siblingLine = line + 1;
            siblingPos = 2 * pos - 1;
            return;
        }
        if ((pos & 1) == 1) {
            // is connected to something further up (lower line)
            siblingLine = line - 1;
            if (line == 1) {
                // again: first line is special
                siblingPos = (pos + 1) / 2;
            }
            else {
                siblingPos = pos + 1;
            }
        }
        else {
            // is connected to something further down (higher line)
            siblingLine = line + 1;
            siblingPos = pos - 1;
        }
    }

    bool getModelValue(unsigned line, unsigned pos, unsigned &value) const {
        const auto it = model.find(encodePosition(line, pos));
        if (it != model.end()) {
            value = it->second;
            return true;
        }
        return false;
    }

public:

    SortedPropagator5(z3::solver *s, const z3::expr_vector &inputs) : user_propagator_base(s) {

        this->register_fixed();

        // first line is special (see illustration). The first (0^th) line has |inputs| nodes
        nodes.emplace_back(s->ctx());
        nodes[0].push_back(inputs[0]);
        astToPosition.emplace(inputs[0], encodePosition(0, 0));
        positionToAst.emplace(encodePosition(0, 0), inputs[0]);
        this->add(inputs[0]);
        for (unsigned j = 1; j < inputs.size(); j++) {
            z3::expr e = createNode(0, j);
            nodes[0].push_back(e);
            astToPosition.emplace(e, encodePosition(0, j));
            positionToAst.emplace(encodePosition(0, j), e);
        }

        // for the other lines: The i^th line has 2 * (|inputs| - i) nodes
        for (unsigned i = 1; i < inputs.size(); i++) {
            nodes.emplace_back(s->ctx());
            nodes.back().push_back(inputs[i]);
            astToPosition.emplace(inputs[i], encodePosition(i, 0));
            positionToAst.emplace(encodePosition(i, 0), inputs[i]);
            this->add(inputs[i]);
            for (unsigned j = 1; j < 2 * (inputs.size() - i); j++) {
                z3::expr e = createNode(i, j);
                nodes.back().push_back(e);
                astToPosition.emplace(e, encodePosition(i, j));
                positionToAst.emplace(encodePosition(i, j), e);
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

    void fixed(const z3::expr &ast, const z3::expr &value) override {
        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        //std::cout << "Fixed " + ast.to_string() + " to " + value.to_string() << std::endl;
        unsigned val = value.get_numeral_uint();
        uint64_t p = astToPosition.at(ast);
        fixedPositions.push_back(p);
        unsigned line, pos;
        decodePosition(p, line, pos);
        model.emplace(p, val);

        if (pos >= nodes[line].size()) {
            // node is already an output node
            return;
        }

        // get other input of next comparison
        unsigned siblingLine, siblingNextPos;
        getSibling(line, pos + 1, siblingLine, siblingNextPos);
        assert(siblingLine >= 0 && siblingNextPos > 0);
        unsigned siblingVal;
        if (getModelValue(siblingLine, siblingNextPos - 1, siblingVal)) {
            z3::expr_vector empty(ctx());
            const auto &nextAst = positionToAst.at(encodePosition(line, pos + 1));
            const auto &siblingAst = positionToAst.at(encodePosition(siblingLine, siblingNextPos - 1));
            const auto &siblingNextAst = positionToAst.at(encodePosition(siblingLine, siblingNextPos));

            // we register them always in case it is not an output node. Z3 will anyway check if they have been registered already
            if (pos + 2 < nodes[line].size())
                this->add(nextAst);
            if (siblingNextPos + 1 < nodes[siblingLine].size())
                this->add(siblingNextAst);

            if (val == siblingVal || ((line < siblingLine) == (val < siblingVal))) {
                // already ordered correctly
                // simply pass them through
                if (line <= siblingLine) {
                    this->propagate(empty, z3::implies(z3::ule(ast, siblingAst), nextAst == ast && siblingNextAst == siblingAst));
                }
                else {
                    this->propagate(empty, z3::implies(z3::ule(siblingAst, ast), nextAst == ast && siblingNextAst == siblingAst));
                }
            }
            else {
                // not ordered correctly
                // add if-then-else
                if (line <= siblingLine) {
//                    std::cout << "Propagating: " << z3::ite(z3::ule(ast, siblingAst),
//                                                            nextAst == ast && siblingNextAst == siblingAst,
//                                                            nextAst == siblingAst && siblingNextAst == ast).to_string() << std::endl;
                    this->propagate(empty, z3::ite(z3::ule(ast, siblingAst),
                                                   nextAst == ast && siblingNextAst == siblingAst,
                                                   nextAst == siblingAst && siblingNextAst == ast));
                }
                else {
//                    std::cout << "Propagating: " << z3::ite(z3::ule(siblingAst, ast),
//                                                            nextAst == ast && siblingNextAst == siblingAst,
//                                                            nextAst == siblingAst && siblingNextAst == ast).to_string() << std::endl;
                    this->propagate(empty, z3::ite(z3::ule(siblingAst, ast),
                                                   nextAst == ast && siblingNextAst == siblingAst,
                                                   nextAst == siblingAst && siblingNextAst == ast));
                }
            }
        }
    }

    user_propagator_base *fresh(z3::context &ctx) override { return this; }

    z3::expr_vector getOutputs() {
        z3::expr_vector output(ctx());
        for (unsigned i = 0; i < nodes.size(); i++) {
            output.push_back(nodes[i].back());
        }
        return output;
    }
};

int sorting5(unsigned size, sortingConstraints constraints, bool persistent) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    struct sort : multiSort {
        LazySortingNetworkPropagator* prop;
        sort(LazySortingNetworkPropagator* prop) : prop(prop) {}

        void add(z3::expr_vector& in, z3::expr_vector& out) override {
            symbolicNetwork network(in.size());
            // insertion sort: O(n^2)
            for (unsigned i = 0; i < in.size() - 1; i++) {
                for (unsigned j = 0; j < in.size() - i - 1; j++) {
                    network.addComparision(j, j + 1);
                }
            }
            prop->addInputOutput(network, in, out);
        }
    };

    LazySortingNetworkPropagator propagator(&s, BIT_CNT, persistent);
    sort sort(&propagator);

    applyConstraints(s, size, sort, constraints);

    z3::check_result result = s.check();
    printStatistics(s);
    if (constraints & outputReverse) {
        assert(result == z3::unsat);
    }
    else if (!(constraints & pseudoBoolean)) {
        z3::model m = s.get_model();
        checkSorting(m, propagator.getInputs(), propagator.getOutputs(), constraints);
    }
    else {
        assert(result == z3::sat);
    }
    return -1;
}
