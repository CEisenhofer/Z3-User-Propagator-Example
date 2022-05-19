#include "common.h"

class distinct_propagator : public z3::user_propagator_base {

protected:

    std::unordered_map<unsigned, z3::expr> bvToExpr; // maps bv to constant id to which it was assigned
    std::vector<unsigned> alreadyAssignedBvValue; // bitvector values that were already assigned
    std::stack<unsigned> fixedCnt;

public:

    void final() override {}

    void eq(const z3::expr &expr, const z3::expr &expr1) override {
        // std::cout << "Equal: " << expr.to_string() << " = " << expr1.to_string() << std::endl;
        z3::expr_vector conflict(ctx());
        conflict.push_back(expr);
        conflict.push_back(expr1);
        this->conflict(conflict);
    }

    void fixed(z3::expr const &ast, z3::expr const &value) override {
        return;
        unsigned v = value.get_numeral_uint();
        auto iter = bvToExpr.find(v);
        if (iter == bvToExpr.end()) {
            // value has not been assigned to any constant so far
            bvToExpr.emplace(v, ast);
            alreadyAssignedBvValue.push_back(v);
        }
        else {
            z3::expr_vector conflict(ctx());
            conflict.push_back(ast);
            conflict.push_back(iter->second);
            this->conflict(conflict);
            /*z3::expr_vector conflict(ctx());
            conflict.push_back(ast);
            conflict.push_back(iter->second);
            this->propagate(conflict, ast != iter->second);*/
        }
    }

    distinct_propagator(z3::solver *s)
            : user_propagator_base(s) {

        this->register_fixed();
        this->register_final();
        this->register_eq();
    }

    ~distinct_propagator() = default;

    void push() override {
        fixedCnt.push((unsigned)alreadyAssignedBvValue.size());
    }

    void pop(unsigned num_scopes) override {
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned lastCnt = fixedCnt.top();
            fixedCnt.pop();
            // Remove information that some particular bitvector value has been assigned already to a constant
            for (unsigned j = alreadyAssignedBvValue.size(); j > lastCnt; j--) {
                bvToExpr.erase(alreadyAssignedBvValue[j - 1]);
            }
            alreadyAssignedBvValue.resize(lastCnt);
        }
    }

    user_propagator_base *fresh(z3::context &) override {
        return this;
    }
};

class distinct_propagator2 : public z3::user_propagator_base {

    const z3::expr_vector &distinct;
    const z3::expr_vector &bijected;
    const z3::expr_vector &fromTo;
    const z3::expr_vector &toFrom;

    std::unordered_map<z3::expr, unsigned> distinctMapping;
    std::unordered_map<z3::expr, unsigned> bijectedMapping;
    std::unordered_map<z3::expr, unsigned> fromToMapping;
    std::unordered_map<z3::expr, unsigned> toFromMapping;

    z3::expr_vector fixedValues;
    std::unordered_map<z3::expr, uint64_t> model;
    std::stack<unsigned> fixedCnt;

public:

    void final() override {}

    void fixed(z3::expr const &ast, z3::expr const &value) override {
        unsigned v = value.get_numeral_uint();
        model.emplace(ast, v);
        if (fromToMapping.contains(ast)) {
            z3::expr_vector fixed(ctx());
            fixed.push_back(ast);
            this->propagate(fixed,
                            z3::implies(ast == (int)v,
                                        distinct[fromToMapping[ast]] == bijected[v]
                            )
            );
            this->propagate(fixed,
                            z3::implies(ast == (int)v,
                                        toFrom[v] == (int)fromToMapping[ast]
                            )
            );
        }
    }

    distinct_propagator2(z3::solver *s, const z3::expr_vector &distinct, const z3::expr_vector &bijected, const z3::expr_vector &fromTo, const z3::expr_vector &toFrom)
            : user_propagator_base(s), distinct(distinct), bijected(bijected), fromTo(fromTo), toFrom(toFrom), fixedValues(ctx()) {
        this->register_fixed();
        this->register_final();

        assert(distinct.size() == bijected.size());
        assert(distinct.size() == fromTo.size());
        assert(distinct.size() == toFrom.size());

        for (unsigned i = 0; i < distinct.size(); i++) {
            this->add(distinct[i]);
            this->add(bijected[i]);
            this->add(fromTo[i]);
            this->add(toFrom[i]);
            this->distinctMapping.emplace(distinct[i], i);
            this->bijectedMapping.emplace(bijected[i], i);
            this->fromToMapping.emplace(fromTo[i], i);
            this->toFromMapping.emplace(toFrom[i], i);
        }
    }

    ~distinct_propagator2() = default;

    void push() override {
        fixedCnt.push(fixedValues.size());
    }

    void pop(unsigned int num_scopes) override {
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned prevFixed = fixedCnt.top();
            fixedCnt.pop();
            for (unsigned j = fixedValues.size(); j > prevFixed; j--) {
                model.erase(fixedValues[j - 1]);
                fixedValues.pop_back();
            }
        }
    }

    user_propagator_base *fresh(z3::context &) override {
        return this;
    }
};

int distinct1(unsigned num, unsigned bits) {

    z3::context context;
    z3::solver s(context, z3::solver::simple());

    z3::expr_vector distinct(context);

    for (unsigned i = 0; i < num; i++) {
        distinct.push_back(context.bv_const(("x" + to_string(i)).c_str(), bits));
    }

    s.add(z3::distinct(distinct));

    // without this having only distinct would be simply by checking if |vars| <= 2^bits
    // not all bv are equal; some are more constrained than others
    for (unsigned i = 0; i < (3 * num) / 4; i++) {
        s.add(distinct[i].extract(0, 0) == 0);
    }

    z3::check_result result = s.check();
    return (int)result;
}

int distinct2(unsigned num, unsigned bits) {

    z3::context context;
    z3::solver s(context, z3::solver::simple());

    z3::expr_vector distinct(context);
    z3::expr_vector bijected(context);
    z3::expr_vector fromTo(context);
    z3::expr_vector toFrom(context);

    for (unsigned i = 0; i < num; i++) {
        distinct.push_back(context.bv_const(("x" + to_string(i)).c_str(), bits));
        bijected.push_back(context.bv_const(("y" + to_string(i)).c_str(), bits));
        fromTo.push_back(context.bv_const(("a" + to_string(i)).c_str(), bits));
        toFrom.push_back(context.bv_const(("b" + to_string(i)).c_str(), bits));
        s.add(z3::ule(fromTo[i], num - 1));
        s.add(z3::ule(toFrom[i], num - 1));
    }

    for (unsigned i = 0; i < num; i++) {
        for (unsigned k = 0; k < num; k++) {
            s.add(z3::implies(fromTo[k] == (int)i, bijected[k] == distinct[i] && toFrom[i] == (int)k));
        }
    }

    for (unsigned i = 1; i < num; i++) {
        s.add(bijected[i - 1] < bijected[i]);
    }

    for (unsigned i = 0; i < (3 * num) / 4; i++) {
        s.add(distinct[i].extract(0, 0) == 0);
    }

    z3::check_result result = s.check();
    return (int)result;
}

int distinct3(unsigned num, unsigned bits) {
    
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    z3::expr_vector distinct(context);
    distinct_propagator propagator(&s);

    for (unsigned i = 0; i < num; i++) {
        z3::expr expr = context.bv_const(("x" + to_string(i)).c_str(), bits);
        propagator.add(expr);
        distinct.push_back(expr);
    }

    for (unsigned i = 0; i < (3 * num) / 4; i++) {
        s.add(distinct[i].extract(0, 0) == 0);
    }

    z3::check_result result = s.check();
    return (int)result;
}

int distinct4(unsigned num, unsigned bits) {

    z3::context context;
    z3::solver s(context, z3::solver::simple());

    z3::expr_vector distinct(context);
    z3::expr_vector bijected(context);
    z3::expr_vector fromTo(context);
    z3::expr_vector toFrom(context);

    for (unsigned i = 0; i < num; i++) {
        distinct.push_back(context.bv_const(("x" + to_string(i)).c_str(), bits));
        bijected.push_back(context.bv_const(("y" + to_string(i)).c_str(), bits));
        fromTo.push_back(context.bv_const(("a" + to_string(i)).c_str(), bits));
        toFrom.push_back(context.bv_const(("b" + to_string(i)).c_str(), bits));
        s.add(z3::ule(fromTo[i], num - 1));
        s.add(z3::ule(toFrom[i], num - 1));
    }

    distinct_propagator2 propagator(&s, distinct, bijected, fromTo, toFrom);

    for (unsigned i = 1; i < num; i++) {
        s.add(bijected[i - 1] < bijected[i]);
    }

    for (unsigned i = 0; i < (3 * num) / 4; i++) {
        s.add(distinct[i].extract(0, 0) == 0);
    }

    z3::check_result result = s.check();
    return (int)result;
}