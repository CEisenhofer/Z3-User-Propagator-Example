#include <initializer_list>
#include "common.h"

class NetworkConstructor {

    z3::context& context;

protected:

    std::vector<std::pair<z3::expr, z3::expr>> decisionExpressions;

    unsigned lines;

public:

    NetworkConstructor(z3::context& context, unsigned lines) :
        context(context),
        lines(lines) { }

    virtual ~NetworkConstructor() = default;

    NetworkConstructor(z3::solver& s, unsigned lines, unsigned depth, bool usesQuantifiers) :
        NetworkConstructor(s.ctx(), lines) {

        z3::expr_vector in(s.ctx()), out(s.ctx());

        for (unsigned i = 0; i < lines; i++) {
            in.push_back(context.bv_const(("in" + std::to_string(i)).c_str(), 1));
            out.push_back(context.bv_const(("out" + std::to_string(i)).c_str(), 1));
        }

        s.add(buildAbstractNetwork(in, out, depth, usesQuantifiers ? CompleteQuantified : OnlyPreconditions));
    }

    z3::expr sorted(const z3::expr_vector& v) const {
        z3::expr_vector s(context);
        for (unsigned i = 1; i < lines; i++) {
            s.push_back(z3::ule(v[i - 1], v[i]));
        }
        return z3::mk_and(s);
    }

    enum NetworkType {
        CompleteQuantified,
        OnlyPreconditions,
        BodyUnquantified,
        Ordering,
    };

    std::pair<z3::expr, z3::expr> addMultiComparator(z3::context& ctx, z3::expr_vector assertions, z3::expr_vector& premisses,
        const z3::expr_vector& in, z3::expr_vector& out, const unsigned id, NetworkType type) const {

        unsigned cnt = in.size();

        assert(in.size() == out.size());
        
        //unsigned bits = log2i((cnt * cnt - cnt) / 2);
        unsigned bits = log2i(cnt);
        z3::expr from = type < BodyUnquantified ? ctx.bv_const(("from" + std::to_string(id)).c_str(), bits) : decisionExpressions[id].first;
        z3::expr to = type < BodyUnquantified ? ctx.bv_const(("to" + std::to_string(id)).c_str(), bits) : decisionExpressions[id].second;

        if (type != OnlyPreconditions) {
            for (unsigned i = 0; i < cnt; i++) {
                for (unsigned j = i + 1; j < cnt; j++) {

                    z3::expr_vector assignment(ctx);

                    // copy all except two
                    for (unsigned k = 0; k < cnt; k++) {
                        if (k == i || k == j) continue;
                        assignment.push_back(in[k] == out[k]);
                    }
                    assignment.push_back(
                        out[i] == (in[i] & in[j]));
                    assignment.push_back(
                        out[j] == (in[i] | in[j]));
                    premisses.push_back(z3::implies(from == (signed)i && to == (signed)j, z3::mk_and(assignment)));
                }
            }
        }
        if (type < BodyUnquantified) {
            assertions.push_back(z3::ult(from, to));
            assertions.push_back(z3::ule(to, cnt - 1));
        }
        return { from, to };
    }

    z3::expr buildAbstractNetwork(std::vector<z3::expr_vector>& layers, NetworkType type) {

        assert(layers[0].size() == lines);
        assert(layers.size() > 2);

        z3::expr_vector in2(context);
        z3::expr_vector premisses(context), bound(context);
        z3::expr_vector assertions(context);

        if (type == CompleteQuantified) {
            for (unsigned i = 0; i < layers.size(); i++) {
                for (unsigned j = 0; j < layers[i].size(); j++) {
                    bound.push_back(layers[i][j]);
                }
            }
        }

        for (unsigned i = 0; i < layers.size() - 1; i++) {
            auto decision = addMultiComparator(context, assertions, premisses, layers[i], layers[i + 1], i, type);

            if (type < BodyUnquantified) {
                decisionExpressions.push_back(decision);
            }
        }

        switch (type) {
            case CompleteQuantified:
                assertions.push_back(z3::forall(bound, z3::implies(mk_and(premisses), sorted(layers.back()))));
                break;
            case BodyUnquantified:
                assertions.push_back(!mk_and(premisses));
                break;
            case Ordering:
                assertions.push_back(mk_and(premisses));
                break;
            case OnlyPreconditions:
            default:
                // do this check in the final callback
                break;
        }

        return mk_and(assertions);
    }

    z3::expr buildAbstractNetwork(const z3::expr_vector& in, const z3::expr_vector& out, unsigned depth, NetworkType type) {

        std::vector<z3::expr_vector> layers;
        layers.push_back(in);

        for (unsigned i = 0; i < depth - 1; i++) {
            z3::expr_vector layer(context);
            for (unsigned j = 0; j < in.size(); j++) {
            	layer.push_back(context.constant(("x_" + std::to_string(i) + "_" + std::to_string(j)).c_str(), in[j].get_sort()));
            }
        	layers.push_back(layer);
        }

        layers.push_back(out);

        return buildAbstractNetwork(layers, type);
    }

    // creates a concrete network without preconditions and negated
    void buildConcreteNetwork(z3::solver& solver, const z3::expr_vector& in, const std::vector<unsigned>& connections) const {

        assert((connections.size() & 1) == 0);

    	std::vector<z3::expr_vector> intermediates;

        for (unsigned i = 0; i < in.size(); i++) {
            intermediates.emplace_back(solver.ctx());
            intermediates.back().push_back(in[i]);
        }

        z3::expr_vector assertions(solver.ctx());

        for (unsigned i = 0; i < connections.size(); i += 2) {
            unsigned i1 = connections[i];
            unsigned i2 = connections[i + 1];
            z3::expr x = solver.ctx().constant(("x_" + std::to_string(i >> 1)).c_str(), in[0].get_sort());
            z3::expr y = solver.ctx().constant(("y_" + std::to_string(i >> 1)).c_str(), in[0].get_sort());

            assertions.push_back(
                z3::ite(
                    z3::ule(intermediates[i1].back(), intermediates[i2].back()),
                    intermediates[i1].back() == x && intermediates[i2].back() == y,
                    intermediates[i1].back() == y && intermediates[i2].back() == x)
            );
            intermediates[i1].push_back(x);
            intermediates[i2].push_back(y);
        }

        z3::expr_vector s(solver.ctx());

        for (unsigned i = 0; i < intermediates.size(); i++) {
            s.push_back(intermediates[i].back());
        }

        const z3::expr assertion = z3::mk_and(assertions) && !sorted(s);
        solver.add(assertion);
    }


    const std::vector<std::pair<z3::expr, z3::expr>>& getDecisionVariables() const {
        return decisionExpressions;
    }
};

class SubPropagator : public z3::user_propagator_base {

    //std::stack<unsigned> prevFixedCnt;
    //std::vector<unsigned> fixedIndexes;
    simple_model model;
    std::unordered_map<z3::expr, unsigned> exprToId;

public:

    z3::expr_vector in;

    SubPropagator(z3::context& ctx) : user_propagator_base(ctx), in(ctx) {}

    SubPropagator(z3::solver& s, int length) : user_propagator_base(&s), in(s.ctx()) {
        this->register_fixed();

        for (unsigned i = 0; i < length; i++) {
            z3::expr e = s.ctx().bv_const(("in_" + std::to_string(i + 1)).c_str(), 1);
            in.push_back(e);
            exprToId.emplace(e, i);
            this->add(e);
            model.push_back((unsigned)-1);
        }
    }

    std::vector<unsigned>& getModel() {
        return model;
    }

    void push() override {
        //prevFixedCnt.push((unsigned)fixedIndexes.size());
    }

    void pop(unsigned int num_scopes) override {
        /*for (unsigned i = 0; i < num_scopes; i++) {
            unsigned prevFixed = prevFixedCnt.top();
            prevFixedCnt.pop();
            for (unsigned j = fixedIndexes.size(); j > prevFixed; j--) {
                model[fixedIndexes[j - 1]] = (unsigned)-1;
                fixedIndexes.pop_back();
            }
        }*/
    }

    user_propagator_base* fresh(z3::context& ctx) override {
        return nullptr;
    }

    void fixed(const z3::expr& ast, const z3::expr& value) override {
        if (!exprToId.contains(ast))
            return;
        model[exprToId.at(ast)] = value.get_numeral_uint();
    }

};

class OptSortedPropagator2 : public NetworkConstructor, z3::user_propagator_base {

    std::stack<unsigned> prevFixedCnt;
    std::vector<unsigned> fixedIndexes;
    simple_model model;

    std::unordered_map<z3::expr, unsigned> exprToId; // first bit: from (0) or to (1). remaining bits: index
    std::unordered_map<unsigned, z3::expr> idToExpr; // --||--

    std::vector<unsigned> occurrences; // number
    std::unordered_map<z3::expr, z3::expr_vector> bitvectorToBit;

    const z3::expr zero;
    const z3::expr one;
    const z3::expr_vector empty;

    z3::solver* const subSolver;
    SubPropagator* const subPropagator;

    const unsigned depth;
    const unsigned lines;
    const unsigned bitCnt;
    int decisionLevel = 0;

    std::vector<std::pair<int, const z3::expr>> instantiations;

    const Params params;

    unsigned getOtherIndex(unsigned x) const {
        return x ^ 1;
    }

    bool getNext(unsigned x, unsigned& next) const {
        next = x + 2;
        return next < (depth << 1);
    }

    bool getPrev(unsigned x, unsigned& prev) const {
        if (x < 2)
            return false;
        prev = x - 2;
        return true;
    }

    bool has(unsigned idx, unsigned& v) const {
        v = model[idx];
        return v != -1;
    }

    void conflicting(std::initializer_list<unsigned> args) {
        conflicting(std::vector(args.begin(), args.end()));
    }

    void conflicting(std::vector<unsigned> args) {
        z3::expr_vector conflicting(ctx());
        for (const auto& arg : args) {
            z3::expr e = idToExpr.at(arg);
            conflicting.push_back(e);
        }
        this->conflict(conflicting);
    }

    std::string draw() const {
        const std::string sep = "--";
        std::string s;
        const unsigned lineSize = sep.size() * (depth + 1) /*sep*/ + depth /*|+?*/ + 1 /*\n*/;
        s.reserve(lineSize * lines);

        for (unsigned i = 0; i < lines; i++) {
            for (unsigned j = 0; j < depth; j++) {
                s += sep + "-";
            }
            s += sep + "\n";
            assert(s.length() == (i + 1) * lineSize);
        }

        for (unsigned i = 0; i < depth; i++) {
            unsigned v1, v2;
            if (has(i << 1, v1) & has(getOtherIndex(i << 1), v2)) {
                for (unsigned j = 0; j < lines; j++) {
                    if (j == v1 || j == v2)
                        s[j * lineSize + sep.size() * (i + 1) + i] = '+';
                    else if (j > MIN(v1, v2) && j < MAX(v1, v2))
                        s[j * lineSize + sep.size() * (i + 1) + i] = '|';
                }
            }
            else {
                for (unsigned j = 0; j < lines; j++) {
                    if (j == v1 || j == v2)
                        s[j * lineSize + sep.size() * (i + 1) + i] = '+';
                    else
                        s[j * lineSize + sep.size() * (i + 1) + i] = '?';
                }
            }
        }
        return s;
    }

    void checkNext(unsigned idx1, unsigned idx2, unsigned v1, unsigned v2) {
        if (!params.adjacent)
            return;
        unsigned idx3;
        unsigned v3, v4;
        if (getNext(idx1, idx3) && has(idx3, v3) && has(getOtherIndex(idx3), v4)) {
            if (v1 == v3 && v2 == v4) {
                // std::cout << "Exit early (1)" << std::endl;
                conflicting({ idx1, idx2, idx3, getOtherIndex(idx3) });
            }
        }
    }

    void checkPrev(unsigned idx1, unsigned idx2, unsigned v1, unsigned v2) {
        if (!params.adjacent)
            return;
        unsigned idx3;
        unsigned v3, v4;
        if (getPrev(idx1, idx3) && has(idx3, v3) && has(getOtherIndex(idx3), v4)) {
            if (v1 == v3 && v2 == v4) {
                // std::cout << "Exit early (2)" << std::endl;
                conflicting({ idx1, idx2, idx3, getOtherIndex(idx3) });
            }
        }
    }

    unsigned singleBitIndexStart() const {
        return 2 * decisionExpressions.size();
    }

    std::vector<std::vector<unsigned>> distance;

    unsigned maxDistanceIndex() const {
        return (depth + 1) * lines; // input & output inclusive
    }

    std::pair<unsigned, unsigned> decompose(unsigned index) const {
        assert(index < maxDistanceIndex());
        unsigned line = index % lines;
        unsigned dep = index / lines;
        return std::make_pair(dep, line);
    }

    std::string distanceMatrixToString() const {
        auto indexToString = [this](unsigned idx) -> std::string {
            const auto d = decompose(idx);
            if (d.first == 0) {
                return "in" + std::to_string(d.second);
            }
            return "decision line " + std::to_string(d.second) + " node " + std::to_string(d.first - 1);
        };

        std::string s;
        for (unsigned i = 0; i < distance.size(); i++) {
            std::string node1 = indexToString(i);
            s += "Reachable from " + node1 + ":\n";
            for (unsigned j = 0; j < distance.size(); j++) {
                std::string node2 = indexToString(j);
                s += "\t" + node2 + ": " +
                    (distance[i][j] == (unsigned)-1 ? "unreachable" : std::to_string(distance[i][j])) + "\n";
            }
        }
        return s;
    }

    void floydWarshall() {

        const unsigned mi = maxDistanceIndex();
        distance.clear();
        distance.reserve(mi);
        // build first distance matrix
        for (unsigned i = 0; i < mi /*the last node does not lead anywhere*/; i++) {
            distance.emplace_back();
            distance.reserve(mi);
            std::pair<unsigned, unsigned> p1 = decompose(i);
            for (unsigned j = 0; j < mi; j++) {
                std::pair<unsigned, unsigned> p2 = decompose(j);
                unsigned v1, v2;
                if (p1.second == p2.second) { // same line
                    if (p1.first == p2.first) {
                        distance.back().push_back(0); // same element
                    }
                    else if (p1.first < p2.first) {
                        distance.back().push_back(p2.first - p1.first); // same element
                    }
                    else {
                        distance.back().push_back((unsigned)-1); // element before the other
                    }
                }
                else if (p1.first == p2.first) {
                    // two elements on different lines but same position cannot be connected
                    // ==> optimization: We rather connect diagonal than vertical (does not change anything
                    // but we avoid 0-length jumps to another line in case they are connected)
                    distance.back().push_back((unsigned)-1);
                    // So we have
                    // -----------
                    //       /
                    //      1
                    //     /
                    // -----------
                    // instead of 
                    // -----------
                    //     |
                    //     0
                    //     |
                    // -----------
                    // as each depth has at most one connection
                    // (so we cannot move over multiple connections at once anyway)
                }
                else if (p1.first < p2.first &&
                    p2.first - p1.first == 1 &&
                    has(p1.first << 1, v1) &&
                    has(getOtherIndex(p1.first << 1), v2) && (
                        (v1 == p1.second && v2 == p2.second) ||
                        (v1 == p2.second && v2 == p1.second)
                        )) { // same depth
                    distance.back().push_back(1); // connected lines
                }
                else {
                    distance.back().push_back((unsigned)-1); // don't know
                }
            }
        }

        for (unsigned i = 0; i < mi; i++) {
            for (unsigned j = 0; j < mi; j++) {
                for (unsigned k = 0; k < mi; k++) {
                    if (distance[j][i] != (unsigned)-1 &&
                        distance[i][k] != (unsigned)-1 &&
                        distance[j][k] > distance[j][i] + distance[i][k]) {

                        distance[j][k] = distance[j][i] + distance[i][k];
                    }
                }
            }
        }
    }

    void checkReachability() {

        if (!params.connected || fixedIndexes.size() < 2 * depth) {
            return;
        }

        if (distance.empty())
            floydWarshall();

        // std::cout << draw() << std::endl;
        // std::cout << distanceMatrixToString() << std::endl;

        for (unsigned i = 0; i < lines; i++) {
            for (unsigned j = 0; j < lines; j++) {
                if (distance[i][lines * depth + j] == (unsigned)-1) {
                    // std::cout << "Cannot reach " << j << " from " << i << std::endl;
                    // assert that at least one element k that is reachable from i is connected to j
                    z3::expr_vector correction(ctx());

                    for (unsigned k = 0; k < depth * lines; k++) {
                        if (distance[i][k] != (unsigned)-1) {
                            auto d = decompose(k);
                            if (d.second < j) {
                                correction.push_back(
                                    decisionExpressions[d.first].first == (signed)d.second &&
                                    decisionExpressions[d.first].second == (signed)j
                                );
                            }
                            else {
                                correction.push_back(
                                    decisionExpressions[d.first].first == (signed)j &&
                                    decisionExpressions[d.first].second == (signed)d.second
                                );
                            }
                        }
                    }

                    z3::expr conseq = z3::mk_or(correction);
                    // std::cout << "Propagated: " << conseq.to_string() << std::endl;
                    this->propagate(empty, conseq);
                    if (!params.connected_all)
                        return;
                }
            }
        }
    }

    static std::random_device rd;
    static std::mt19937 rng;
    static std::bernoulli_distribution dist;
    static std::uniform_int_distribution<int> idist;
    user_propagator_base* child = nullptr;

public:

    unsigned finals = 0;
    unsigned random = 0;

    OptSortedPropagator2(z3::solver& s, unsigned lines, unsigned depth, Params params) :
        NetworkConstructor(s, lines, depth, !((params.strategy & CompleteModel) || (params.strategy & MinimalModel) || (params.strategy & NearlyCompleteModel))),
        user_propagator_base(&s),
        zero(ctx().bv_val(0, 1)),
        one(ctx().bv_val(1, 1)),
        empty(ctx()),
        subSolver((params.strategy & CompleteModel || params.strategy & MinimalModel || params.strategy & NearlyCompleteModel) ? new z3::solver(ctx(), z3::solver::simple()) : nullptr),
        subPropagator((params.strategy & CompleteModel || params.strategy & MinimalModel || params.strategy & NearlyCompleteModel) ? new SubPropagator(*subSolver, lines) : nullptr),
        depth(depth),
        lines(lines),
        bitCnt(decisionExpressions[0].first.get_sort().bv_size()),
        params(params) {

        this->register_fixed();
        //if (params.simulate_quantifier)
        this->register_final();
        if (params.decide)
            this->register_decide();

        for (unsigned i = 0; i < depth; i++) {
            this->add(decisionExpressions[i].first);
            exprToId.emplace(decisionExpressions[i].first, i << 1);
            idToExpr.emplace(i << 1, decisionExpressions[i].first);

            this->add(decisionExpressions[i].second);
            exprToId.emplace(decisionExpressions[i].second, (i << 1) | 1);
            idToExpr.emplace((i << 1) | 1, decisionExpressions[i].second);

            model.push_back((unsigned)-1);
            model.push_back((unsigned)-1);
        }

        if (params.decide_occurences) {

            for (unsigned i = 0; i < lines; i++) {
                occurrences.push_back(0);
            }

            // model must contain the individual bits
            for (unsigned i = 0; i < depth; i++) {
                z3::expr_vector bits1(ctx()), bits2(ctx());
                for (unsigned j = 0; j < bitCnt; j++) {
                    z3::expr e1 = decisionExpressions[i].first.bit2bool(j);
                    z3::expr e2 = decisionExpressions[i].second.bit2bool(j);
                    unsigned id = decisionExpressions.size() + i * bitCnt + j;
                    this->add(e1);
                    this->add(e2);
                    bits1.push_back(e1);
                    bits2.push_back(e2);
                    model.push_back((unsigned)-1);
                    model.push_back((unsigned)-1);
                    exprToId.emplace(e1, (id << 1) | 0);
                    idToExpr.emplace((id << 1) | 0, e1);
                    exprToId.emplace(e2, (id << 1) | 1);
                    idToExpr.emplace((id << 1) | 1, e2);
                }
                bitvectorToBit.emplace(decisionExpressions[i].first, bits1);
                bitvectorToBit.emplace(decisionExpressions[i].second, bits2);
            }
        }
    }

    ~OptSortedPropagator2() override {
        delete subPropagator;
        delete subSolver;
        delete child;
    }

    void push() override {
        prevFixedCnt.push(fixedIndexes.size());
        decisionLevel++;
    }

    void pop(unsigned int num_scopes) override {
        // std::cout << "Popped " << num_scopes << " levels" << std::endl;
        for (unsigned i = 0; i < num_scopes; i++) {
            unsigned prevFixed = prevFixedCnt.top();
            prevFixedCnt.pop();
            for (unsigned j = fixedIndexes.size(); j > prevFixed; j--) {
                if (params.decide_occurences && fixedIndexes[j - 1] < singleBitIndexStart())
                    occurrences[model[fixedIndexes[j - 1]]]--;

                model[fixedIndexes[j - 1]] = (unsigned)-1;
                // std::cout << "Popped: " << idToExpr.at(fixedIndexes[j - 1]).to_string() << std::endl;
                fixedIndexes.pop_back();
            }
        }
        decisionLevel -= (int)num_scopes;
        assert(decisionLevel >= 0);
        if (params.strategy & Repropagate) {
            for (auto& inst : instantiations) {
                if (inst.first > decisionLevel) {
                    inst.first = decisionLevel;
                    this->propagate(empty, inst.second);
                }
            }
        }
    }

    unsigned lastIndex = (unsigned)-1;

    void fixed(const z3::expr& ast, const z3::expr& value) override {
        WriteLine("Fixed " + ast.to_string() + " to " + value.to_string());
        // std::cout << "Fixed " + ast.to_string() + " to " + value.to_string() << std::endl;
        if (!exprToId.contains(ast))
            return;
        distance.clear();
        unsigned v1 = value.is_true() ? 1 : value.is_false() ? 0 : value.get_numeral_uint();
        unsigned v2;
        unsigned idx1 = exprToId.at(ast);
        unsigned idx2 = getOtherIndex(idx1);
        
        fixedIndexes.push_back(idx1);
        model[idx1] = v1;

        z3::expr next(ctx());
        if (params.decide && lastIndex != -1 && setLast(lastIndex, next))
            this->next_split(next, 0, Z3_L_UNDEF);
        else
            lastIndex = -1;
        
        if (idx1 >= singleBitIndexStart())
            return;

        if (params.decide_occurences)
            occurrences[v1]++;

        if (!has(idx2, v2)) {
            return;
        }

        checkNext(idx1, idx2, v1, v2);
        checkPrev(idx1, idx2, v1, v2);
        checkReachability();
    }

    static std::vector<std::vector<unsigned>> eval(std::vector<unsigned>& input, const std::vector<unsigned>& connections) {
        std::vector<std::vector<unsigned>> result;
        result.push_back(input);
        for (unsigned j = 0; j < connections.size(); j += 2) {
            unsigned swpIdx1 = connections[j];
            unsigned swpIdx2 = connections[j + 1];
            if (input[swpIdx1] > input[swpIdx2]) {
                unsigned tmp = input[swpIdx1];
                input[swpIdx1] = input[swpIdx2];
                input[swpIdx2] = tmp;
            }
            result.push_back(input);
        }
        return result;
    }

    void initialize(const std::vector<unsigned>& connections, std::vector<unsigned> m) {
        bool propagated = false;
    	std::vector<z3::expr_vector> layers;
        int r = idist(rng);
        if (params.strategy & CompleteModel || ((params.strategy & NearlyCompleteModel) && r != 0) || ((params.strategy & Randomized) && !(params.strategy & MinimalModel))) {
            auto results = eval(m, connections);
            for (unsigned i = 0; i < results.size(); i++) {
                z3::expr_vector layer(ctx());
                for (unsigned j = 0; j < results[i].size(); j++) {
                    layer.push_back(results[i][j] ? one : zero);
                }
                layers.push_back(layer);
            }
            const z3::expr prop = buildAbstractNetwork(layers, BodyUnquantified);
            this->propagate(empty, prop);
            instantiations.emplace_back(decisionLevel, prop);
            layers.clear();
        }
        if (params.strategy & MinimalModel || ((params.strategy & NearlyCompleteModel) && r == 0))  {
            z3::expr_vector layer_in(ctx());
            for (unsigned i = 0; i < m.size(); i++) {
                layer_in.push_back(m[i] ? one : zero);
            }
            layers.push_back(layer_in);
            
            for (unsigned i = 0; i < depth - 1; i++) {
                z3::expr_vector layer(ctx());
                for (unsigned j = 0; j < lines; j++) {
                    const z3::expr e = z3::expr(ctx(),
                        Z3_mk_fresh_const(ctx(),
                            ("x_" + std::to_string(i + 1) + "_" + std::to_string(j + 1)).c_str(),
                            ctx().bv_sort(1)));
                    layer.push_back(e);
                }
                layers.push_back(layer);
            }
            std::ranges::sort(m);
            z3::expr_vector layer_out(ctx());
            for (unsigned i = 0; i < m.size(); i++) {
                layer_out.push_back(m[i] ? one : zero);
            }
            layers.push_back(layer_out);
            const z3::expr prop = buildAbstractNetwork(layers, Ordering);
            this->propagate(empty, prop);
            instantiations.emplace_back(decisionLevel, prop);
            layers.clear();
        }

        if (propagated && (params.strategy & Restart))
            this->restart();
    }

    static std::vector<unsigned> randomTest(unsigned lines, const std::vector<unsigned>& connections) {
        std::vector<unsigned> counterexample;
        counterexample.resize(lines);
        for (unsigned i = 0; i < 10; i++) {
            for (unsigned j = 0; j < lines; j++) {
                counterexample[j] = dist(rng);
            }

            auto sorted = eval(counterexample, connections);
            unsigned prev = sorted.back()[0];
            for (unsigned j = 1; j < sorted.back().size(); j++) {
                if (prev > sorted.back()[j])
                    return sorted[0];
                prev = sorted.back()[j];
            }
        }
        counterexample.clear();
        return counterexample;
    }

    void final() override {
        finals++;
        if (params.strategy == None)
            return;

        simple_model m;
        m.reserve(singleBitIndexStart());
        for (unsigned i = 0; i < singleBitIndexStart(); i++) {
            m.push_back(model[i]);
        }

        if (params.strategy & Randomized) {
            std::vector<unsigned> counterexample = randomTest(lines, m);

            if (!counterexample.empty()) {
                random++;
                initialize(m, counterexample);
                return;
            }
        }

        if (!((params.strategy & CompleteModel) || (params.strategy & MinimalModel) || (params.strategy & NearlyCompleteModel)))
            return;

        subSolver->push();
        buildConcreteNetwork(*subSolver, subPropagator->in, m);

        z3::check_result result = subSolver->check();
        if (result == z3::check_result::unknown) {
            throw z3::exception("Unknown");
        }
        if (result == z3::check_result::sat) {
            initialize(m, subPropagator->getModel());
        }
        subSolver->pop();
    }

    bool setLast(unsigned i, z3::expr& val) {
        if (model[i] == (unsigned)-1) {
            lastIndex = i;
            val = idToExpr.at(lastIndex);
            return true;
        }
        if (model[getOtherIndex(i)] == (unsigned)-1) {
            lastIndex = getOtherIndex(i);
            val = idToExpr.at(lastIndex);
            return true;
        }
        return false;
    }

    bool canSetTo(unsigned idx, unsigned value) {
        unsigned j =
            (singleBitIndexStart() + (((idx >> 1) * bitCnt) << 1)) | (idx & 1);

        for (unsigned i = 0; i < bitCnt; i++) {
            unsigned v = model[j + 2 * i];
            if (v != -1 && ((value >> i) & 1) != v) {
                return false;
            }
        }
        return true;
    }

    void setToLeastOccurring(unsigned idx, unsigned& bit, Z3_lbool& is_pos) {

        unsigned other = model[getOtherIndex(lastIndex)];

        unsigned setTo = (unsigned)-1;
        for (unsigned i = 0; i < occurrences.size(); i++) {
            if ((setTo == -1 ||
                (i != other && // not the same as the other one
                    occurrences[setTo] > occurrences[i])) && // minimal
                canSetTo(idx, i)
                )
                setTo = i;
        }

        if (setTo == -1)
            return;

        unsigned j =
            (singleBitIndexStart() + (((idx >> 1) * bitCnt) << 1)) | (idx & 1);

        for (unsigned i = 0; i < bitCnt; i++) {
            if (model[j + 2 * i] == -1) {
                bit = i;
                is_pos = ((setTo >> i) & 1) ? Z3_L_TRUE : Z3_L_FALSE;
                return;
            }
        }
        assert(false);

    }

    void decide(z3::expr& val, unsigned& bit, Z3_lbool& is_pos) override {
        WriteLine("Decide: " + val.to_string() + " bit: " + std::to_string(bit) + " = " + (is_pos == Z3_L_FALSE ? "false" : "true"));
        bit = 0;
        if (lastIndex == (unsigned)-1 || !setLast(lastIndex, val)) {
            lastIndex = exprToId.at(val);
            if (lastIndex >= singleBitIndexStart()) {
                lastIndex = (((lastIndex - singleBitIndexStart()) >> 1) / bitCnt) << 1 | (lastIndex & 1);
            }
        }
        else {
            is_pos = Z3_L_UNDEF;
        }

        if (params.decide_occurences)
            setToLeastOccurring(lastIndex, bit, is_pos);
    }

    user_propagator_base* fresh(z3::context& ctx) override {
        child = new SubPropagator(ctx);
        child->register_final();
        child->register_decide();
        return child;
    }

};

std::random_device OptSortedPropagator2::rd;
std::mt19937 OptSortedPropagator2::rng = std::mt19937(rd());
std::bernoulli_distribution OptSortedPropagator2::dist;
std::uniform_int_distribution<int> OptSortedPropagator2::idist(0, 100);

int opt_sorting(unsigned* args, Params params) {

    unsigned start = args[1];
    bool down = args[2];

    if (start == 0)
        return -1;

    z3::context context;

    unsigned depth = start;
    while (depth > 0) {
        z3::solver s(context, params.propagator ? Z3_mk_simple_solver(context) : Z3_mk_solver(context));

        NetworkConstructor* constructor;
        if (params.propagator) {
            constructor = new OptSortedPropagator2(s, args[0], depth, params);
        }
        else {
            constructor = new NetworkConstructor(s, args[0], depth, true);
        }


        std::cout << "Checking if solvable with depth: " << depth << std::endl;
        // std::cout << "F: " << s.assertions().to_string() << std::endl;

        z3::check_result result = s.check();

        std::cout << (result == z3::check_result::sat ? "SAT" : (result == z3::check_result::unsat ? "UNSAT" : "UNKNOWN")) << std::endl;

        auto var = constructor->getDecisionVariables();

        if (params.all_sat && result == z3::check_result::sat) {
            do {
                const z3::model m = s.get_model();
                z3::expr_vector blocking(context);
                std::cout << "{" << std::endl;
                for (unsigned i = 0; i < var.size(); i++) {
                    z3::expr& e1 = var[i].first;
                    z3::expr& e2 = var[i].second;
                    z3::expr v1 = m.eval(e1, false);
                    z3::expr v2 = m.eval(e2, false);
                    blocking.push_back(e1 != v1);
                    blocking.push_back(e2 != v2);
                    std::cout << "\t{" << v1.get_numeral_int() << ", " << v2.get_numeral_int() << "}";
                    if (i + 1 < var.size()) {
                        std::cout << ", ";
                    }
                    std::cout << std::endl;
                }
                std::cout << "}," << std::endl;
                s.add(z3::mk_or(blocking));
                result = s.check();
            } while (result == z3::check_result::sat);
            delete constructor;
            return (signed)(depth + down);
        }
        std::cout << "Finals: " <<
            (dynamic_cast<OptSortedPropagator2*>(constructor) == nullptr
                ? 0
                : ((OptSortedPropagator2*)constructor)->finals) << std::endl;
        if (params.strategy & Randomized) {
            std::cout << "Random hits: " <<
                (dynamic_cast<OptSortedPropagator2*>(constructor) == nullptr
                    ? 0
                    : ((OptSortedPropagator2*)constructor)->random) << std::endl;
        }
        delete constructor;

        if (result == z3::sat) {
#ifndef NDEBUG
            z3::model m = s.get_model();
            std::vector<unsigned> connections;
            for (unsigned i = 0; i < var.size(); i++) {
                connections.push_back(m.eval(var[i].first).get_numeral_uint());
                connections.push_back(m.eval(var[i].second).get_numeral_uint());
            }

            assert(OptSortedPropagator2::randomTest(args[0], connections).empty());
#endif
            if (!down)
                break;
        }
        else if (result == z3::unsat) {
            if (down)
                break;
        }
        else {
            std::cout << s.reason_unknown() << std::endl;
            return -1;
        }

        if (down)
            depth--;
        else
            depth++;
    }

    return (signed)(depth + down);
}