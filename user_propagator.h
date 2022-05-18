#pragma once

#include "common.h"

class user_propagator : public z3::user_propagator_base {

protected:

    std::unordered_map<z3::expr, unsigned> exprToId;
    simple_model currentModel;
    std::unordered_set<simple_model> modelSet;
    z3::expr_vector fixedVariables;
    std::stack<unsigned> fixedCnt;

    const unsigned board;
    const bool allSat;

    int solutionNr = 1;

public:

    int getModelCount() const {
        return solutionNr - 1;
    }

    void final() override {
        if (!allSat)
            return;
        this->conflict(fixedVariables);
        if (modelSet.find(currentModel) != modelSet.end()) {
            WriteLine("Got already computed model");
            return;
        }
        Write("Model #" << solutionNr << ":\n");
#ifdef VERBOSE
        for (unsigned i = 0; i < fixedVariables.size(); i++) {
            z3::expr fixed = fixedVariables[i];
            WriteLine("q" + to_string(exprToId[fixed]) + " = " + to_string(currentModel[exprToId[fixed]]));
        }
#endif
        modelSet.insert(currentModel);
        WriteEmptyLine;
        solutionNr++;
    }

    static unsigned bvToInt(z3::expr const &e) {
        return e.is_true() ? 1 : e.is_false() ? 0 : e.get_numeral_uint();
    }

    void fixed(z3::expr const &ast, z3::expr const &value) override {
        fixedVariables.push_back(ast);
        unsigned valueBv = bvToInt(value);
        currentModel[exprToId[ast]] = valueBv;
    }

    user_propagator(z3::context &c, const z3::expr_vector& queens, unsigned board, bool allSat)
            : user_propagator_base(c), currentModel(queens.size(), (unsigned)-1), fixedVariables(c), board(board), allSat(allSat) {

        this->register_fixed();
        this->register_final();

        for (unsigned i = 0; i < queens.size(); i++) {
            this->add(queens[i]);
            exprToId.emplace(queens[i], i);
        }
    }

    user_propagator(z3::solver *s, const z3::expr_vector& queens, unsigned board, bool allSat)
            : user_propagator_base(s), currentModel(queens.size(), (unsigned)-1), fixedVariables(s->ctx()), board(board), allSat(allSat) {

        this->register_fixed();
        this->register_final();

        for (unsigned i = 0; i < queens.size(); i++) {
            this->add(queens[i]);
            exprToId.emplace(queens[i], i);
        }
    }

    ~user_propagator() override = default;

    void push() override {
        fixedCnt.push((unsigned)fixedVariables.size());
    }

    void pop(unsigned num_scopes) override {
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned lastCnt = fixedCnt.top();
            fixedCnt.pop();
            // Remove fixed values from model
            for (unsigned j = fixedVariables.size(); j > lastCnt; j--) {
                currentModel[exprToId[fixedVariables[j - 1]]] = (unsigned)-1;
            }
            fixedVariables.resize(lastCnt);
        }
    }

    user_propagator_base *fresh(z3::context &) override {
        return this;
    }
};