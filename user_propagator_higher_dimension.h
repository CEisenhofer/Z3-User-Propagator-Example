#pragma once

#include "user_propagator.h"

class user_propagator_higher_dimension : public z3::user_propagator_base {

    simple_model currentModel;
    std::vector<unsigned> assignedComponents;
    std::vector<unsigned> fixedValues;
    std::stack<unsigned> fixedCnt;
    
    std::vector<std::vector<z3::expr>> createdInDecisionLevel;

    std::unordered_map<z3::expr, unsigned> astToId;
    std::unordered_map<unsigned, z3::expr> idToAst;
    const unsigned board, dim;
    unsigned queens;

    inline unsigned idToQueen(unsigned id) const {
        assert(id < queens * dim);
        return id / dim;
    }

    inline unsigned getId(unsigned queen, unsigned comp) {
        assert(queen < this->queens && comp < this->dim);
        return queen * dim + comp;
    }

    inline void conflictingQueens(unsigned queen1, unsigned queen2) {
        z3::expr_vector conflicting(ctx());
        for (unsigned i = 0; i < dim; i++) {
            const z3::expr &q1 = idToAst.at(getId(queen1, i));
            const z3::expr &q2 = idToAst.at(getId(queen2, i));
            conflicting.push_back(q1);
            conflicting.push_back(q2);
        }
        this->conflict(conflicting);
    }

    void increaseSize() {
        
        if (createdInDecisionLevel.empty())
            createdInDecisionLevel.emplace_back(); // top-level

        unsigned prevQueens = currentModel.size() / dim;
        const unsigned bits = log2i(board) + 1;

        for (unsigned i = prevQueens; i < queens; i++) {
            assignedComponents.push_back(0);
            for (unsigned j = 0; j < dim; j++) {
                z3::expr queen = ctx().bv_const(("q" + to_string(i) + "_" + std::to_string(j)).c_str(), bits);
                currentModel.push_back(-1);
                astToId.emplace(queen, i * dim + j);
                idToAst.emplace(i * dim + j, queen);
                createdInDecisionLevel.back().push_back(queen);
                this->add(queen);
            }
        }
    }

public:

    user_propagator_higher_dimension(z3::context &c, unsigned board, unsigned queens, unsigned dim)
            : z3::user_propagator_base(c), board(board), dim(dim), queens(queens) {
        this->register_fixed();
        this->register_final();
        increaseSize();
    }

    user_propagator_higher_dimension(z3::solver *s, unsigned board, unsigned queens, unsigned dim)
            : z3::user_propagator_base(s), board(board), dim(dim), queens(queens) {
        this->register_fixed();
        this->register_final();
        increaseSize();
    }

    unsigned getQueenCnt() const {
        return queens - 1;
    }

    void push() override {
        fixedCnt.push((unsigned)fixedValues.size());
        createdInDecisionLevel.emplace_back();
    }

    void pop(unsigned num_scopes) override {
        std::vector<z3::expr>& movedUp = createdInDecisionLevel[createdInDecisionLevel.size() - num_scopes - 1];
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned lastCnt = fixedCnt.top();
            fixedCnt.pop();
            // Remove fixed values from model
            for (unsigned j = fixedValues.size(); j > lastCnt; j--) {
                currentModel[fixedValues[j - 1]] = -1;
                assignedComponents[idToQueen(fixedValues[j - 1])]--;
            }
            fixedValues.resize(lastCnt);
            
            for (auto& q : createdInDecisionLevel.back()) {
                this->add(q);
                movedUp.push_back(q); // constant is now associated with a higher decision level
            }
            createdInDecisionLevel.pop_back();
        }
    }

    user_propagator_base *fresh(z3::context &) override {
        return this;
    }

    void final() override {
        // increment number of queens
        std::cout << "Queens #" << queens << " is sat" << std::endl;
        queens++;
        increaseSize();
    }

    void fixed(z3::expr const &ast, z3::expr const &value) override {
        // WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        unsigned v = value.get_numeral_uint();
        unsigned id = astToId.at(ast);
        fixedValues.push_back(id);
        currentModel[id] = v;
        unsigned queen = idToQueen(id);
        assignedComponents[queen]++;

        if (v >= board) {
            z3::expr_vector conflicting(ast.ctx());
            conflicting.push_back(ast);
            this->conflict(conflicting);
            return;
        }

        if (assignedComponents[queen] >= dim) {
            assert(assignedComponents[queen] == dim);

            for (unsigned i = 0; i < queens; i++) {
                if (i == queen || assignedComponents[i] < dim) {
                    continue;
                }
                unsigned char equalPositions = 0; // check if they are on the same "row"/"column" (conflict iff value is at most 1)
                unsigned char equalDiagonal = 0; // check if they are on the same diagonal (conflict iff value is exactly dim)
                signed coordinateDifference = abs((signed)currentModel[queen * dim] - (signed)currentModel[i * dim]);

                for (unsigned j = 0; j < dim; j++) {
                    if (currentModel[queen * dim + j] == currentModel[i * dim + j]) {
                        equalPositions++;
                    }
                    if (abs((signed)currentModel[queen * dim + j] - (signed)currentModel[i * dim + j]) == coordinateDifference) {
                        equalDiagonal++;
                    }
                }
                if (dim - equalPositions <= 1 || equalDiagonal == dim) {
                    conflictingQueens(queen, i);
                }
            }
        }
    }
};