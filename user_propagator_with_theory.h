#pragma once

#include "user_propagator.h"

class user_propagator_with_theory : public user_propagator {

    std::unordered_map<unsigned, z3::expr> idToExpr;
    unsigned bitCnt;

public:

    user_propagator_with_theory(z3::context &c, const z3::expr_vector& queens, unsigned board, bool allSat)
            : user_propagator(c, queens, board, allSat) {

    	for (unsigned i = 0; i < queens.size(); i++) {
            idToExpr.emplace(i, queens[i]);
        }
        bitCnt = queens[0].get_sort().bv_size();
    }

    user_propagator_with_theory(z3::solver *s, const z3::expr_vector& queens, unsigned board, bool allSat)
            : user_propagator(s, queens, board, allSat) {

        for (unsigned i = 0; i < queens.size(); i++) {
            idToExpr.emplace(i, queens[i]);
        }
        bitCnt = queens[0].get_sort().bv_size();
    }

    unsigned setTo = (unsigned)-1;

    void fixed(z3::expr const &ast, z3::expr const &value) override {
        unsigned queenId = exprToId[ast];
        unsigned queenPos = bvToInt(value);

        if (queenId >= board) {
            // just a single bit
            fixedVariables.push_back(ast);
            currentModel[exprToId[ast]] = queenPos;
            return;
        }

        setTo = (unsigned)-1;

        if (queenPos >= board) {
            z3::expr_vector conflicting(ast.ctx());
            conflicting.push_back(ast);
            this->conflict(conflicting);
            return;
        }

        for (const z3::expr &fixed: fixedVariables) {
            unsigned otherId = exprToId[fixed];
            unsigned otherPos = currentModel[exprToId[fixed]];

            if (queenPos == otherPos) {
                z3::expr_vector conflicting(ast.ctx());
                conflicting.push_back(ast);
                conflicting.push_back(fixed);
                this->conflict(conflicting);
                continue;
            }
            int diffY = abs((int) queenId - (int) otherId);
            int diffX = abs((int) queenPos - (int) otherPos);
            if (diffX == diffY) {
                z3::expr_vector conflicting(ast.ctx());
                conflicting.push_back(ast);
                conflicting.push_back(fixed);
                this->conflict(conflicting);
            }
        }

        fixedVariables.push_back(ast);
        currentModel[exprToId[ast]] = queenPos;
    }

    bool setLast(z3::expr& val, unsigned& bit, Z3_lbool& is_pos) {
        if (currentModel[setTo] == (unsigned)-1) {
            val = idToExpr.at(setTo);
            bit = 0;
        	is_pos = (rand() % 2 == 0) ? Z3_L_FALSE : Z3_L_TRUE;
            is_pos = Z3_L_UNDEF;
            return true;
        }
        return false;
    }

    void decide(z3::expr& val, unsigned& bit, Z3_lbool& is_pos) override {
        if (setTo == (unsigned)-1) {
            setTo = exprToId.at(val);
        }
        if (setTo >= board) {
            setTo = (setTo - board) / bitCnt;
        }
        setLast(val, bit, is_pos);
    }
};