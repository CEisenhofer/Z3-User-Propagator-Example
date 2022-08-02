#pragma once

#include "user_propagator.h"
#include <queue>

class user_propagator_with_theory2 : public user_propagator {

    std::unordered_map<unsigned, z3::expr> idToExpr;
    std::unordered_map<unsigned, z3::expr> idToNegExpr;
    std::vector<z3::expr_vector> lines;
    std::vector<z3::expr_vector> columns;

    std::vector<unsigned> assignedLine;
    std::vector<z3::expr> isAlreadyOccupiedLine;
    std::vector<unsigned> assignedColumn;
    std::vector<z3::expr> isAlreadyOccupiedColumn;

    std::vector<z3::expr> isAlreadyOccupiedDiagonal1; // left top to right bottom
    std::vector<z3::expr> isAlreadyOccupiedDiagonal2; // right top to left bottom
    const z3::expr_vector empty;

    bool theory;
    int withDecide;

    std::vector<std::pair<int, const z3::expr>> instantiations;

    std::pair<unsigned, unsigned> idToPosition(unsigned id) const {
        return { id % board, id / board };
    }

    unsigned positionToId(unsigned x, unsigned y) const {
        return x + board * y;
    }

    std::pair<unsigned, unsigned> exprToPosition(const z3::expr& ast) {
        return idToPosition(exprToId.at(ast));
    }

    z3::expr& positionToExpr(unsigned x, unsigned y) {
        return idToExpr.at(y * board + x);
    }

    z3::expr& positionToNegExpr(unsigned x, unsigned y) {
        return idToNegExpr.at(y * board + x);
    }

    unsigned getDiagonal1Index(unsigned x, unsigned y) const {
        return (x - y) + (board - 1);
    }

    unsigned getDiagonal2Index(unsigned x, unsigned y) const {
        return (((board - 1) - x) - y) + (board - 1);
    }

public:

    user_propagator_with_theory2(z3::solver* s, const z3::expr_vector& queens, unsigned board, bool allSat, bool theory, int withDecide, int sol)
        : user_propagator(s, queens, board, allSat, sol), empty(ctx()), impl(ctx()), theory(theory), withDecide(withDecide) {

        if (withDecide)
            this->register_decide();

        for (unsigned i = 0; i < queens.size(); i++) {
            idToExpr.emplace(i, queens[i]);
            idToNegExpr.emplace(i, !queens[i]);
        }

        const z3::expr null(ctx());

        for (unsigned i = 0; i < board; i++) {
            z3::expr_vector line(s->ctx());
            z3::expr_vector column(s->ctx());
            for (unsigned j = 0; j < board; j++) {
                line.push_back(queens[i * board + j]);
                column.push_back(queens[j * board + i]);
            }
            lines.push_back(line);
            columns.push_back(column);

            isAlreadyOccupiedColumn.push_back(null);
            isAlreadyOccupiedLine.push_back(null);
            assignedColumn.push_back(0);
            assignedLine.push_back(0);
        }

        for (unsigned i = 0; i < 2 * board - 1; i++) {
            isAlreadyOccupiedDiagonal1.push_back(null);
            isAlreadyOccupiedDiagonal2.push_back(null);
        }
    }

    void unset(const z3::expr& ast) override {
        //std::cout << "Pop " << ast.to_string() << std::endl;
        unsigned id = exprToId.at(ast);
        const std::pair<unsigned, unsigned> position = exprToPosition(ast);
        const bool assignment = currentModel[id];

        assignedLine[position.second]--;
        assert(assignedLine[position.second] >= 0);

        assignedColumn[position.first]--;
        assert(assignedColumn[position.first] >= 0);

        if (assignment) {
            const z3::expr null(ctx());
            const unsigned diagonal1Idx = getDiagonal1Index(position.first, position.second);
            const unsigned diagonal2Idx = getDiagonal2Index(position.first, position.second);
            isAlreadyOccupiedLine[position.second] = null;
            isAlreadyOccupiedColumn[position.first] = null;
            isAlreadyOccupiedDiagonal1[diagonal1Idx] = null;
            isAlreadyOccupiedDiagonal2[diagonal2Idx] = null;
        }
    }

    void unsetLast(bool any) override {

        /*for (auto& inst : instantiations) {
            if (inst.first > decisionLevel) {
                inst.first = decisionLevel;
                this->propagate(empty, inst.second);
            }
        }*/
    }

    z3::expr_vector impl;

    void prop(int x, int y, bool fixed) {
        const unsigned assignedLines = assignedLine[y];
        const unsigned assignedColumns = assignedColumn[x];
        if (assignedLines == board - 1 && !(z3::ast)isAlreadyOccupiedLine[y]) {
            int c = -1;
            impl.resize(0);
            z3::expr_vector& line = lines[y];
            for (unsigned i = 0; i < board; i++) {
                const z3::expr& e = line[i];
                if (currentModel[positionToId(i, y)] == -1) {
                    assert(c == -1);
                    c = i;
                }
                else {
                    impl.push_back(e);
                }
            }
            assert(c != -1);
            this->propagate(impl, line[c]);
            //instantiations.emplace_back(decisionLevel, z3::mk_or(impl) || c);
        }
        if (assignedColumns == board - 1 && !(z3::ast)isAlreadyOccupiedColumn[x]) {
            int c = -1;
            impl.resize(0);
            z3::expr_vector& column = columns[x];
            for (unsigned i = 0; i < board; i++) {
                const z3::expr& e = column[i];
                if (currentModel[positionToId(x, i)] == -1) {
                    assert(c == -1);
                    c = i;
                }
                else {
                    impl.push_back(e);
                }
            }
            assert(c != -1);
            this->propagate(impl, column[c]);
            //instantiations.emplace_back(decisionLevel, z3::mk_or(impl) || c);
        }
    }

    void fixed(z3::expr const& ast, z3::expr const& value) override {
        //std::cout << "Fixed " << ast.to_string() << " to " << value.to_string() << std::endl;
        const bool assignment = value.is_true() ? true : false;
        const unsigned id = exprToId.at(ast);
        const std::pair<unsigned, unsigned> position = idToPosition(id);
        assert(currentModel[id] == (unsigned)-1);
        fixedVariables.push_back(ast);
        currentModel[id] = assignment;
        ++assignedLine[position.second];
        ++assignedColumn[position.first];

        if (assignment) {
            const unsigned diagonal1Idx = getDiagonal1Index(position.first, position.second);
            const unsigned diagonal2Idx = getDiagonal2Index(position.first, position.second);
            /*z3::expr line = isAlreadyOccupiedLine[position.second];
            z3::expr column = isAlreadyOccupiedColumn[position.first];
            z3::expr diagonal1 = isAlreadyOccupiedDiagonal1[diagonal1Idx];
            z3::expr diagonal2 = isAlreadyOccupiedDiagonal2[diagonal2Idx];

            if ((z3::ast)line) {
                z3::expr_vector conflicting(ctx());
                conflicting.push_back(ast);
                conflicting.push_back(line);
                assert(currentModel[exprToId.at(line)] == 1);
                this->conflict(conflicting);
            }
            if ((z3::ast)column) {
                z3::expr_vector conflicting(ctx());
                conflicting.push_back(ast);
                conflicting.push_back(column);
                assert(currentModel[exprToId.at(column)] == 1);
                this->conflict(conflicting);
            }
            if ((z3::ast)diagonal1) {
                z3::expr_vector conflicting(ctx());
                conflicting.push_back(ast);
                conflicting.push_back(diagonal1);
                assert(currentModel[exprToId.at(diagonal1)] == 1);
                this->conflict(conflicting);
            }
            if ((z3::ast)diagonal2) {
                z3::expr_vector conflicting(ctx());
                conflicting.push_back(ast);
                conflicting.push_back(diagonal2);
                assert(currentModel[exprToId.at(diagonal2)] == 1);
                this->conflict(conflicting);
            }*/

            isAlreadyOccupiedLine[position.second] = ast;
            isAlreadyOccupiedColumn[position.first] = ast;
            isAlreadyOccupiedDiagonal1[diagonal1Idx] = ast;
            isAlreadyOccupiedDiagonal2[diagonal2Idx] = ast;

            if (!theory)
                return;

            for (int i = -1; i <= 1; i++) {
                for (int j = -1; j <= 1; j++) {
                    if (i == 0 && j == 0)
                        continue;

                    for (int x = position.first + i, y = position.second + j; x >= 0 && x < board && y >= 0 && y < board; x += i, y += j) {
                        impl.resize(0);
                        impl.push_back(ast);
                        this->propagate(impl, positionToNegExpr(x, y));
                        //!ast || positionToNegExpr(x, y);
                        //this->propagate(empty, !ast || positionToNegExpr(x, y));
                        //instantiations.emplace_back(decisionLevel, !ast || positionToNegExpr(x, y));
                        //std::cout << "Propagating: " << ast.to_string() << " => " << positionToNegExpr(x, y).to_string() << std::endl;
                    }
                }
            }
        }
        else {
            if (!theory)
                return;
            /*if (assignedLines == board && !(z3::ast)isAlreadyOccupiedLine[position.second]) {
                this->conflict(lines[position.second]);
            }
            if (assignedColumns == board && !(z3::ast)isAlreadyOccupiedColumn[position.first]) {
                this->conflict(columns[position.first]);
            }*/
            prop(position.first, position.second, true);
        }
    }

    bool isNotAttacked(int x, int y) {
        const unsigned diagonal1Idx = getDiagonal1Index(x, y);
        const unsigned diagonal2Idx = getDiagonal2Index(x, y);
        return
            (z3::ast)isAlreadyOccupiedLine[y] &&
            (z3::ast)isAlreadyOccupiedColumn[x] &&
            (z3::ast)isAlreadyOccupiedDiagonal1[diagonal1Idx] &&
            (z3::ast)isAlreadyOccupiedDiagonal2[diagonal2Idx];
    }

    void decide(z3::expr& ast, unsigned&, Z3_lbool& phase) override {

        assert(withDecide == 1 || withDecide == 2);

        phase = Z3_L_TRUE;
        unsigned best = withDecide == 1 ? 0 : UINT_MAX;

        for (unsigned x = 0; x < board; x++) {
            for (unsigned y = 0; y < board; y++) {

                if (currentModel[positionToId(x, y)] != -1)
                    continue; // already assigned

                unsigned attacksUnattacked = 0; // number of currently unattacked tiles that would be attacked

                for (int i = -1; i <= 1; i++) {
                    for (int j = -1; j <= 1; j++) {
                        if (i == 0 && j == 0)
                            continue;

                        for (int x2 = x + i, y2 = y + j; attacksUnattacked < best && x2 >= 0 && x2 < board && y2 >= 0 && y2 < board; x2 += i, y2 += j) {
                            int v = currentModel[positionToId(x2, y2)];
                            assert(v != 1);
                            attacksUnattacked += isNotAttacked(x2, y2);
                        }
                    }
                }

                if ((withDecide == 1 && attacksUnattacked > best) || (withDecide == 2 && attacksUnattacked < best)) {
                    best = attacksUnattacked;
                    ast = positionToExpr(x, y);
                }

            }
        }
    }
};