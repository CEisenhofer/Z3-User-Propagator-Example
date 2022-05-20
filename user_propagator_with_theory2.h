#pragma once

#include "user_propagator.h"

class user_propagator_with_theory2 : public user_propagator {

    std::unordered_map<unsigned, z3::expr> idToExpr;
    std::vector<z3::expr_vector> lines;
    std::vector<z3::expr_vector> columns;

    std::vector<unsigned> assignedLine;
    std::vector<z3::expr> isAlreadyOccupiedLine;
    std::vector<unsigned> assignedColumn;
    std::vector<z3::expr> isAlreadyOccupiedColumn;

	std::vector<z3::expr> isAlreadyOccupiedDiagonal1; // left top to right bottom
	std::vector<z3::expr> isAlreadyOccupiedDiagonal2; // right top to left bottom

    std::pair<unsigned, unsigned> idToPosition(unsigned id) const {
        return { id % board, id / board };
    }

    std::pair<unsigned, unsigned> exprToPosition(const z3::expr& ast) {
        return idToPosition(exprToId.at(ast));
    }

    z3::expr& positionToExpr(unsigned x, unsigned y) {
        return idToExpr.at(y * board + x);
    }

    unsigned getDiagonal1Index(unsigned x, unsigned y) const {
        return (x - y) + (board - 1);
    }

    unsigned getDiagonal2Index(unsigned x, unsigned y) const {
        return (((board - 1) - x) - y) + (board - 1);
    }

public:

    user_propagator_with_theory2(z3::solver *s, const z3::expr_vector& queens, unsigned board, bool allSat)
            : user_propagator(s, queens, board, allSat) {

        for (unsigned i = 0; i < queens.size(); i++) {
            idToExpr.emplace(i, queens[i]);
        }

    	const z3::expr empty(ctx());

        for (unsigned i = 0; i < board; i++) {
            z3::expr_vector line(s->ctx());
            z3::expr_vector column(s->ctx());
	        for (unsigned j = 0; j < board; j++) {
                line.push_back(queens[i * board + j]);
                column.push_back(queens[j * board + i]);
	        }
            lines.push_back(line);
            columns.push_back(column);

            isAlreadyOccupiedColumn.push_back(empty);
            isAlreadyOccupiedLine.push_back(empty);
            assignedColumn.push_back(0);
            assignedLine.push_back(0);
        }

        for (unsigned i = 0; i < 2 * board - 1; i++) {
            isAlreadyOccupiedDiagonal1.push_back(empty);
            isAlreadyOccupiedDiagonal2.push_back(empty);
        }
    }

    void unset(const z3::expr& ast) override {
        unsigned id = exprToId.at(ast);
        const std::pair<unsigned, unsigned> position = exprToPosition(ast);
        const bool assignment = (bool)currentModel[id];
        std::cout << "Unset " << ast.to_string() << " from " << assignment << std::endl;

    	assignedLine[position.second]--;
        assert(assignedLine[position.second] >= 0);

        assignedColumn[position.first]--;
        assert(assignedColumn[position.first] >= 0);

        if (assignment) {
            if (!addedInConflict) {
                const z3::expr empty(ctx());
                const unsigned diagonal1Idx = getDiagonal1Index(position.first, position.second);
                const unsigned diagonal2Idx = getDiagonal2Index(position.first, position.second);
                std::cout << "Removed diagonal1: " << diagonal1Idx << std::endl;
                std::cout << "Removed diagonal2: " << diagonal2Idx << std::endl;
                isAlreadyOccupiedLine[position.second] = empty;
                isAlreadyOccupiedColumn[position.first] = empty;
                isAlreadyOccupiedDiagonal1[diagonal1Idx] = empty;
                isAlreadyOccupiedDiagonal2[diagonal2Idx] = empty;
            }
            else {
                std::cout << "Added in conflict1" << std::endl;
            }
        }
        addedInConflict = false;
    }

    // only if previous the most recent assignment was to true and produced a conflict
    bool addedInConflict = false;

    void fixed(z3::expr const &ast, z3::expr const &value) override {
        if (addedInConflict) {
            std::cout << "Added in conflict2" << std::endl;
            return;
        }
        std::cout << "Fixed: " << ast.to_string() << " to " << value.to_string() << std::endl;
        const bool assigned = value.is_true() ? true : false;
        const unsigned id = exprToId.at(ast);
        const std::pair<unsigned, unsigned> position = idToPosition(id);
        assert(currentModel[id] == (unsigned)-1);
        fixedVariables.push_back(ast);
    	currentModel[id] = assigned;
        const unsigned assignedLines = ++assignedLine[position.second];
        const unsigned assignedColumns = ++assignedColumn[position.first];
        addedInConflict = false;

        if (assigned) {
            const unsigned diagonal1Idx = getDiagonal1Index(position.first, position.second);
            const unsigned diagonal2Idx = getDiagonal2Index(position.first, position.second);
            z3::expr line = isAlreadyOccupiedLine[position.second];
            z3::expr column = isAlreadyOccupiedColumn[position.first];
            z3::expr diagonal1 = isAlreadyOccupiedDiagonal1[diagonal1Idx];
            z3::expr diagonal2 = isAlreadyOccupiedDiagonal1[diagonal2Idx];

            if ((z3::ast)isAlreadyOccupiedLine[position.second]) {
                z3::expr_vector conflicting(ctx());
                conflicting.push_back(ast);
                conflicting.push_back(isAlreadyOccupiedLine[position.second]);
                assert(currentModel[exprToId.at(isAlreadyOccupiedLine[position.second])] != -1);
                std::cout << "Conflicting1: " << conflicting.to_string() << std::endl;
                outputModel();
            	this->conflict(conflicting);
                addedInConflict = true;
            }
            else {
                line = ast;
            }
            if ((z3::ast)isAlreadyOccupiedColumn[position.first]) {
                z3::expr_vector conflicting(ctx());
                conflicting.push_back(ast);
                conflicting.push_back(isAlreadyOccupiedColumn[position.first]);
                assert(currentModel[exprToId.at(isAlreadyOccupiedColumn[position.first])] != -1);
                std::cout << "Conflicting2: " << conflicting.to_string() << std::endl;
                outputModel();
            	this->conflict(conflicting);
                addedInConflict = true;
            }
            else {
                column = ast;
            }
            if ((z3::ast)isAlreadyOccupiedDiagonal1[diagonal1Idx]) {
                z3::expr_vector conflicting(ctx());
                conflicting.push_back(ast);
                conflicting.push_back(isAlreadyOccupiedDiagonal1[diagonal1Idx]);
                std::cout << "Conflicting3: " << conflicting.to_string() << std::endl;
                std::cout << "Index " << diagonal1Idx << std::endl;
                std::cout << "X = " << position.first << " Y = " << position.second << std::endl;
                outputModel();
            	this->conflict(conflicting);
                addedInConflict = true;
            }
            else {
                diagonal1 = ast;
            }
            if ((z3::ast)isAlreadyOccupiedDiagonal2[diagonal2Idx]) {
                z3::expr_vector conflicting(ctx());
                conflicting.push_back(ast);
                conflicting.push_back(isAlreadyOccupiedDiagonal2[diagonal2Idx]);
                std::cout << "Conflicting4: " << conflicting.to_string() << std::endl;
                std::cout << "Index " << diagonal2Idx << std::endl;
                outputModel();
            	this->conflict(conflicting);
                addedInConflict = true;
            }
            else {
                diagonal2 = ast;
            }

            if (!addedInConflict) {
                isAlreadyOccupiedLine[position.second] = line;
                isAlreadyOccupiedColumn[position.first] = column;
                isAlreadyOccupiedDiagonal1[diagonal1Idx] = diagonal1;
                isAlreadyOccupiedDiagonal1[diagonal2Idx] = diagonal2;
            }
        }
        else {
            if (assignedLines == board && !(z3::ast)isAlreadyOccupiedLine[position.second]) {
                this->conflict(lines[position.second]);
                std::cout << "Conflicting5: " << lines[position.second].to_string() << std::endl;
                outputModel();
            }
            if (assignedColumns == board && !(z3::ast)isAlreadyOccupiedColumn[position.first]) {
                this->conflict(columns[position.first]);
                std::cout << "Conflicting6: " << columns[position.first].to_string() << std::endl;
                outputModel();
            }
        }
    }

    void outputModel() {
        std::cout << "Current model:" << std::endl;
        for (unsigned i = 0; i < currentModel.size(); i++) {
            if (currentModel[i] != -1)
                std::cout << idToExpr.at(i).to_string() << " = " << currentModel[i] << std::endl;
        }
    }
};