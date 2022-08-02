#include "LazySortingNetworkPropagator.h"

class DecompositionPropagator : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    std::vector<unsigned> fixedPositions;
    std::unordered_map<unsigned, unsigned> model;

    int decisionLevel = 0;

    std::vector<std::pair<int, const z3::expr>> instantiations;
    std::vector<bool> fullAssigned;
    z3::expr_vector& intervals;

    std::unordered_map<z3::expr, unsigned> astToPos;
    std::unordered_map<unsigned, z3::expr> posToAst;

public:

    DecompositionPropagator(z3::solver* s, z3::expr_vector& intervals)
        : user_propagator_base(s), intervals(intervals) {

        this->register_fixed();
        this->register_final();

        for (unsigned i = 0; i < intervals.size(); i++) {
            z3::expr e = intervals[i];
            /*z3::expr addr = e.extract(BIT_CNT - 1, BIT_CNT / 2);
            z3::expr size = e.extract(BIT_CNT / 2 - 1, 0);*/
            this->add(e);
            /*this->add(addr);
            this->add(size);*/

            unsigned p = i << 2;
            astToPos.emplace(e, p);
            posToAst.emplace(p, e);

            /*p++;
            astToPos.emplace(addr, p);
            posToAst.emplace(p, addr);

            p++;
            astToPos.emplace(size, p);
            posToAst.emplace(p, size);*/
        }
        //fullAssigned.push_back(false);
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
        for (auto& inst : instantiations) {
            if (inst.first > decisionLevel) {
                z3::expr_vector empty(ctx());
                inst.first = decisionLevel;
                this->propagate(empty, inst.second);
            }
        }
    }

    void fixed(const z3::expr& ast, const z3::expr& value) override {
        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        unsigned val = value.is_true() ? 1 : (value.is_false() ? 0 : value.get_numeral_uint());
        unsigned p = astToPos.at(ast);
        fixedPositions.push_back(p);
        model.emplace(p, val);
    }

    void final() override {
        std::vector<bool> intersecting;
        intersecting.reserve(intervals.size());
        constexpr unsigned bits = BIT_CNT;
        unsigned mask = (unsigned)-1;
        mask >>= ((sizeof(unsigned) * 8) - (bits / 2));
        unsigned lines = 0;

        for (unsigned i = 0; i < intervals.size(); i++) {
            unsigned p1 = i << 2;
            unsigned v1 = model.at(p1);

            intersecting.push_back(false);

            unsigned size1 = v1 & mask;
            unsigned addr1 = (v1 >> (bits / 2)) & mask;

            for (unsigned j = i - 1; j != UINT32_MAX; j--) {
                unsigned p2 = j << 2;
                unsigned v2 = model.at(p2);

                unsigned size2 = v2 & mask;
                unsigned addr2 = (v2 >> (bits / 2)) & mask;
                if (!(addr1 + size1 <= addr2 || addr2 + size2 <= addr1)) {
                    lines += !intersecting[i] + !intersecting[j];
                    intersecting[i] = true;
                    intersecting[j] = true;
                }
            }
        }

        exprNetwork n(ctx(), lines);
        unsigned currentLine = 0;

        for (unsigned i = 0; i < intersecting.size(); i++) {
            if (intersecting[i])
                n.add(currentLine++, intervals[i]);
        }

        assert(lines == currentLine);

        // odd-even sort: O(n*log(n)^2)
        for (unsigned p = 1; p < n.size(); p <<= 1) {
            for (unsigned k = p; k >= 1; k >>= 1) {
                for (unsigned j = k % p; j < n.size() - k; j += 2 * k) {
                    for (unsigned i = 0; i < MIN(k, n.size() - j - k); i++) {
                        if ((i + j) / (2 * p) == (i + j + k) / (2 * p)) {
                            n.addComparision(i + j, i + j + k);
                        }
                    }
                }
            }
        }

        assert(lines != 1);
        if (lines == 0)
            return;

        z3::expr_vector empty(ctx());
        z3::expr_vector prop(ctx());

        for (unsigned i = 0; i < lines - 1; i++) {
            const z3::expr current = n.getCurrentLineValue(i);
            const z3::expr next = n.getCurrentLineValue(i + 1);

            const z3::expr curSize = current.extract(bits / 2 - 1, 0);
            const z3::expr curAddr = current.extract(bits - 1, bits / 2);

            const z3::expr nextAddr = next.extract(bits - 1, bits / 2);

            prop.push_back(z3::ule(z3::zext(curAddr, 1) + z3::zext(curSize, 1), z3::zext(nextAddr, 1)));
        }

        const z3::expr p = z3::mk_and(prop);
        this->propagate(empty, p);
        instantiations.emplace_back(decisionLevel, p);
    }

    user_propagator_base* fresh(z3::context& ctx) override {
        assert(false);
        return nullptr;
    }
};

int sorting9(unsigned size) {
    z3::context context;
    z3::solver s(context, z3::solver::simple());

    z3::expr_vector in(context);
    
    for (unsigned i = 0; i < size; i++) {
        in.push_back(context.bv_const(("in_" + std::to_string(i)).c_str(), BIT_CNT));
    }


    DecompositionPropagator propagator(&s, in);

    s.check();
    z3::model m = s.get_model();
    printStatistics(s);

    std::vector<unsigned> v;
    for (unsigned i = 0; i< in.size(); i++ ) {
        v.push_back(m.eval(in[i]).get_numeral_uint());
    }
    unsigned mask = (unsigned)-1;
    mask >>= ((sizeof(unsigned) * 8) - (BIT_CNT / 2));
    
    for (unsigned i = 0; i < v.size(); i++) {
        const unsigned size1 = v[i] & mask;
        const unsigned addr1 = (v[i] >> (BIT_CNT / 2)) & mask;

        for (unsigned j = i + 1; j < v.size(); j++) {

            const unsigned size2 = v[j] & mask;
            const unsigned addr2 = (v[j] >> (BIT_CNT / 2)) & mask;
            if (!(addr1 + size1 <= addr2 || addr2 + size2 <= addr1)) {
                exit(15);
            }
        }
    }

    return -1;
}
