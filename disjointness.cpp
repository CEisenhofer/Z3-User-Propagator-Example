#include "common.h"
#include "interval_tree.hpp"

#define INTERVAL_CNT 6
#define BIT_SIZES 64

struct Interval {
    // [start; end)
    // start and end are constants

    using value_type = uint64_t;

    value_type start;
    value_type end;
    unsigned id;

    Interval() {
        assert(false); // just here to avoid std::vector<Interval>::resize complaining. The size won't increase!
    }

    Interval(const Interval &o) = default;

    Interval(const value_type &start, const value_type &end) : start(start), end(end) {}

    bool intersect(const Interval &o) const {
        return start >= o.end || o.start >= end;
    }

    std::string to_string() {
        return "[" + std::to_string(start) + ", " + std::to_string(end) + ")";
    }

    friend bool operator==(Interval const &lhs, Interval const &rhs) {
        return lhs.start == rhs.start && lhs.start == rhs.start && lhs.id == rhs.id;
    }

    friend inline bool operator!=(Interval const &lhs, Interval const &rhs) {
        return !(lhs == rhs);
    }

    value_type low() const { return start; }

    value_type high() const { return end; }

    bool overlaps(value_type l, value_type h) const;

    bool overlaps_exclusive(value_type l, value_type h) const;

    bool overlaps(Interval const &other) const {
        return overlaps(other.start, other.end);
    }

    bool overlaps_exclusive(Interval const &other) const {
        return overlaps_exclusive(other.start, other.end);
    }

    bool within(value_type value) const;

    bool within(Interval const &other) const;

    value_type operator-(Interval const &other) const;

    value_type size() const { return end - start; }

    Interval join(Interval const &other) const;
};

bool Interval::overlaps(Interval::value_type l, Interval::value_type h) const {
    return start <= h && l <= end;
}

bool Interval::overlaps_exclusive(Interval::value_type l, Interval::value_type h) const {
    return start < h && l < end;
}

bool Interval::within(Interval::value_type value) const {
    return value >= start && value <= end;
}

bool Interval::within(const Interval &other) const {
    return start <= other.start && end >= other.end;
}

Interval::value_type Interval::operator-(const Interval &other) const {
    if (overlaps(other))
        return value_type((uint64_t)0);
    if (end < other.start)
        return other.start - end;
    else
        return start - other.end;
}

Interval Interval::join(const Interval &other) const {
    auto &min = start < other.start ? start : other.start;
    auto &max = end > other.end ? end : other.end;
    return Interval(min, max);
}

class EquivalenceClass : private std::vector<unsigned>, private std::unordered_set<unsigned> {
public:

    inline unsigned size() const {
        return ((std::vector<unsigned> *)this)->size();
    }

    inline void add(unsigned i) {
        ((std::vector<unsigned> *)this)->push_back(i);
        ((std::unordered_set<unsigned> *)this)->insert(i);
    }

    inline bool contains(unsigned i) const {
        return ((std::unordered_set<unsigned> *)this)->contains(i);
    }

    bool equivalent(const std::vector<unsigned> &other) const {
        if (size() != other.size())
            return false;
        for (unsigned i = 0; i < size(); i++) {
            if (!contains(other[i]))
                return false;
        }
        return true;
    }

    inline unsigned operator[](unsigned idx) const {
        return ((std::vector<unsigned> *)this)->operator[](idx);
    }
};

static std::vector<std::pair<unsigned, EquivalenceClass>> extractEquivalenceClasses(const std::vector<unsigned> &p1, const std::vector<unsigned> &p2, unsigned threshold) {
    if (p1.size() != p2.size())
        return {};

    unsigned lastFixPoint = (unsigned)-1;
    std::vector<std::pair<unsigned, EquivalenceClass>> ret;
    unsigned i = 0;

    const auto extract = [&]() {
        if (i - lastFixPoint - 1 < 2 || i - lastFixPoint - 1 > threshold)
            return;
        EquivalenceClass ec1;
        std::vector<unsigned> ec2;
        for (unsigned j = lastFixPoint + 1; j < i; j++) {
            ec1.add(p1[j]);
            ec2.push_back(p2[j]);
        }
        if (ec1.equivalent(ec2))
            ret.push_back(std::make_pair(lastFixPoint, ec1));
    };

    for (; i < p1.size(); i++) {
        if (p1[i] == p2[i]) {
            extract();
            lastFixPoint = i;
        }
    }
    extract();
    return ret;
}

static inline z3::expr pDisj(const z3::expr &address1, const z3::expr &size1, const z3::expr &address2, const z3::expr &size2) {
    return z3::ule(address1 + size1, address2) || z3::ule(address2 + size2, address1);
}

static z3::expr pDisj(const z3::expr_vector &addresses, const z3::expr_vector &sizes) {
    z3::expr_vector conjunction(addresses.ctx());
    for (unsigned i = 0; i < addresses.size(); i++) {
        for (unsigned j = i + 1; j < addresses.size(); j++) {
            conjunction.push_back(pDisj(addresses[i], sizes[i], addresses[j], sizes[j]));
        }
    }
    return z3::mk_and(conjunction);
}

static z3::expr pDisj(const EquivalenceClass &ec, const z3::expr_vector &addresses, const z3::expr_vector &sizes) {
    if (ec.size() <= 1)
        return addresses.ctx().bool_val(true);

    z3::expr_vector conjunction(addresses.ctx());
    for (unsigned i = 0; i < ec.size(); i++) {
        for (unsigned j = i + 1; j < ec.size(); j++) {
            conjunction.push_back(pDisj(addresses[ec[i]], sizes[ec[i]], addresses[ec[j]], sizes[ec[j]]));
        }
    }
    return z3::mk_and(conjunction);
}

static z3::expr totalOrder(const std::vector<unsigned> &permutation, unsigned from, unsigned to, const z3::expr_vector &addresses, const z3::expr_vector &sizes) {
    if (to - from <= 0 || to == (unsigned)-1)
        return addresses.ctx().bool_val(true);

    z3::expr_vector conjunction(addresses.ctx());
    for (unsigned i = from + 1; i <= to; i++) {
        conjunction.push_back(z3::ule(addresses[permutation[i - 1]] + sizes[permutation[i - 1]], addresses[permutation[i]]));
    }
    return z3::mk_and(conjunction);
}

static z3::expr orderEquivalenceClass(const EquivalenceClass &ec, unsigned greater, const z3::expr_vector &addresses, const z3::expr_vector &sizes) {
    if (ec.size() <= 0 || greater >= addresses.size())
        return addresses.ctx().bool_val(true);

    z3::expr_vector conjunction(addresses.ctx());
    for (unsigned i = 0; i < ec.size(); i++) {
        conjunction.push_back(z3::ule(addresses[ec[i]] + sizes[ec[i]], addresses[greater]));
    }
    return z3::mk_and(conjunction);
}

static z3::expr orderEquivalenceClass(unsigned less, const EquivalenceClass &ec, const z3::expr_vector &addresses, const z3::expr_vector &sizes) {
    if (ec.size() <= 0 || less < 0)
        return addresses.ctx().bool_val(true);

    z3::expr_vector conjunction(addresses.ctx());
    for (unsigned i = 0; i < ec.size(); i++) {
        conjunction.push_back(z3::ule(addresses[less] + sizes[less], addresses[ec[i]]));
    }
    return z3::mk_and(conjunction);
}

class Propagator : public z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    std::stack<unsigned> prevFixedIntervals;
    z3::expr_vector fixedValues;
    std::vector<Interval> fixedIntervals;
    std::unordered_map<z3::expr, uint64_t> model;
    util::interval_tree<Interval> intervalTree;

    const z3::expr_vector &addresses;
    const z3::expr_vector &sizes;

    std::vector<std::vector<unsigned>> previousPermutations;

    std::unordered_map<z3::expr, unsigned> astToIndex;

    unsigned maxInterval = 100;

public:

    Propagator(z3::solver *s, const z3::expr_vector &addresses, const z3::expr_vector &sizes) :
            user_propagator_base(s), fixedValues(addresses.ctx()), addresses(addresses), sizes(sizes) {

        for (unsigned i = 0; i < addresses.size(); i++) {
            this->add(addresses[i]);
            this->add(sizes[i]);

            astToIndex.emplace(addresses[i], i);
            astToIndex.emplace(sizes[i], i);
        }
        this->register_fixed();
    }

    void push() override {
        prevFixedCnt.push(fixedValues.size());
        prevFixedIntervals.push(fixedIntervals.size());
    }

    void pop(unsigned int num_scopes) override {
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned prevFixed = prevFixedCnt.top();
            prevFixedCnt.pop();
            for (unsigned j = fixedValues.size(); j > prevFixed; j--) {
                model.erase(fixedValues[j - 1]);
                fixedValues.pop_back();
            }
            prevFixed = prevFixedIntervals.top();
            prevFixedIntervals.pop();
            for (unsigned j = fixedIntervals.size(); j > prevFixed; j--) {
                auto it = intervalTree.find(fixedIntervals[j - 1]);
                assert(it != intervalTree.end());
                intervalTree.erase(it);
                // std::cout << "Removed interval " << fixedIntervals.back().id + 1 << std::endl;
                fixedIntervals.pop_back();
            }
        }
    }

    void fixed(const z3::expr &ast, const z3::expr &value) override {
        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        uint64_t v = value.get_numeral_uint64();
        fixedValues.push_back(ast);
        model.emplace(ast, v);

        unsigned index = astToIndex.at(ast);

        const z3::expr &addr = addresses[index];
        const z3::expr &size = sizes[index];

        if (model.contains(addr) && model.contains(size)) {
            Interval interval(model.at(addr), model.at(addr) + model.at(size));
            interval.id = index;
            fixedIntervals.push_back(interval);
            intervalTree.insert(interval);
            WriteLine("Added interval " + std::to_string(index + 1) + ": " + interval.to_string());
        }

        if (fixedIntervals.size() != addresses.size())
            // Not everything assigned so far
            return;

        std::vector<unsigned> permutation;
        permutation.reserve(addresses.size());

        std::cout << "Ordering: ";
        for (const auto &interval: intervalTree) {
            permutation.push_back(interval.id);
            std::cout << " <= " + std::to_string(interval.id);
        }
        std::cout << std::endl;

        bool foundOverestimation = false;
        if (true) {
            for (unsigned i = 0; i < previousPermutations.size(); i++) {
                const auto equivalenceClasses = extractEquivalenceClasses(permutation, previousPermutations[i], maxInterval);
                if (equivalenceClasses.empty())
                    continue;
                foundOverestimation = true;
                z3::expr_vector conjunction(ctx());
                unsigned lastRelevantIndex = 0;
                for (unsigned j = 0; j < equivalenceClasses.size(); j++) {
                    std::cout << "Added: " << totalOrder(permutation, lastRelevantIndex, equivalenceClasses[j].first, addresses, sizes).to_string() << std::endl;
                    conjunction.push_back(totalOrder(permutation, lastRelevantIndex, equivalenceClasses[j].first, addresses, sizes));
                    lastRelevantIndex = equivalenceClasses[j].first;
                    if (lastRelevantIndex != (unsigned)-1) {
                        std::cout << "Added: " << orderEquivalenceClass(permutation[lastRelevantIndex], equivalenceClasses[j].second, addresses, sizes).to_string() << std::endl;
                        conjunction.push_back(orderEquivalenceClass(permutation[lastRelevantIndex], equivalenceClasses[j].second, addresses, sizes));
                    }
                    else { ;
                    }
                    std::cout << "Added: " << pDisj(equivalenceClasses[j].second, addresses, sizes).to_string() << std::endl;
                    conjunction.push_back(pDisj(equivalenceClasses[j].second, addresses, sizes));
                    lastRelevantIndex += equivalenceClasses[j].second.size() + 1;
                    std::cout << "Added: " << orderEquivalenceClass(equivalenceClasses[j].second, permutation[lastRelevantIndex], addresses, sizes).to_string() << std::endl;
                    conjunction.push_back(orderEquivalenceClass(equivalenceClasses[j].second, permutation[lastRelevantIndex], addresses, sizes));
                }
                std::cout << "Added: " << totalOrder(permutation, lastRelevantIndex, permutation.size() - 1, addresses, sizes).to_string() << std::endl;
                conjunction.push_back(totalOrder(permutation, lastRelevantIndex, permutation.size() - 1, addresses, sizes));

                std::cout << "Propagating: " << z3::implies(z3::mk_and(conjunction), ctx().bool_val(false)).to_string() << std::endl;
                this->propagate(z3::expr_vector(ctx()), z3::implies(z3::mk_and(conjunction), ctx().bool_val(false)));
            }
        }


        if (!foundOverestimation) {
            std::cout << "Propagating: " << z3::implies(totalOrder(permutation, 0, permutation.size() - 1, addresses, sizes), ctx().bool_val(false)).to_string() << std::endl;
            this->propagate(z3::expr_vector(ctx()), z3::implies(totalOrder(permutation, 0, permutation.size() - 1, addresses, sizes), ctx().bool_val(false)));
            previousPermutations.push_back(permutation);
        }
    }

    user_propagator_base *fresh(z3::context &ctx) override { return this; }

};

void disjointness() {

    z3::context context;
    z3::solver s(context, z3::solver::simple());

    z3::expr_vector addresses(context);
    z3::expr_vector sizes(context);

    for (unsigned i = 0; i < INTERVAL_CNT; i++) {
        addresses.push_back(context.bv_const((std::string("addr_") + std::to_string(i)).c_str(), BIT_SIZES));
        sizes.push_back(context.bv_const((std::string("size_") + std::to_string(i)).c_str(), BIT_SIZES));
        s.add(z3::bvadd_no_overflow(addresses.back(), sizes.back(), false));
        s.add(sizes.back() > 0);
    }

    // Ordinary disjointness
    s.add(pDisj(addresses, sizes));

    Propagator prop(&s, addresses, sizes);

    std::cout << "Problem:\n" << s.assertions().to_string() << std::endl;

    auto result = s.check();
    if (result == z3::unsat) {
        std::cout << "Unsat" << std::endl;
    }
    else {
        std::cout << "Sat" << std::endl;
        z3::model m = s.get_model();
        //std::cout << "Model:\n" << m.to_string() << std::endl;
        std::vector<std::pair<uint64_t, uint64_t>> intervals;

        for (unsigned i = 0; i < addresses.size(); i++) {
            uint64_t low = m.eval(addresses[i]).get_numeral_uint64();
            uint64_t high = low + m.eval(sizes[i]).get_numeral_uint64();
            std::cout << "[" << low << "; " << high << "]" << std::endl;
            assert(low <= high);
            for (unsigned j = 0; j < intervals.size(); j++) {
                assert(low >= intervals[j].second || intervals[j].first >= high);
            }
            intervals.push_back(std::make_pair(low, high));
        }
    }
    exit(1);
}

