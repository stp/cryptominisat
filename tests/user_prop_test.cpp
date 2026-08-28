/******************************************
Copyright (C) 2009-2020 Authors of CryptoMiniSat, see AUTHORS file

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in
all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
THE SOFTWARE.
***********************************************/

#include "gtest/gtest.h"

#include <cstdio>
#include <vector>

#include "cryptominisat5/cryptominisat.h"
#include "cryptominisat5/user_prop.h"
#include "src/solver.h"
#include "src/solverconf.h"
#include "test_helper.h"

using namespace CMSat;
using std::vector;

namespace {

// A propagator that does nothing at all: the solver must behave exactly as if
// no propagator were connected.
class NoopPropagator : public ExternalPropagator
{
public:
    uint32_t num_assignment_notifications = 0;
    uint32_t num_new_level_notifications = 0;
    uint32_t num_backtrack_notifications = 0;
    uint32_t num_model_checks = 0;

    void notify_assignment(const vector<Lit>&) override {
        num_assignment_notifications++;
    }
    void notify_new_decision_level() override { num_new_level_notifications++; }
    void notify_backtrack(size_t) override { num_backtrack_notifications++; }
    bool cb_check_found_model(const vector<Lit>&) override {
        num_model_checks++;
        return true;
    }
    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = false;
        return false;
    }
    Lit cb_add_external_clause_lit() override { return lit_Undef; }
};

// Rebuilds the trail from notifications alone and compares it, at every point
// where the two are required to agree, with what the solver actually has.
// This is the whole of the notification contract in one object.
class MirrorPropagator : public ExternalPropagator
{
public:
    Solver* s = nullptr;
    vector<vector<Lit>> stack;   // stack[i] holds the observed literals of level i
    vector<char> assigned;       // indexed by outer var
    vector<lbool> value_of;      // indexed by outer var, from notifications alone
    uint32_t num_comparisons = 0;
    uint32_t num_backtracks = 0;
    uint32_t max_level_seen = 0;

    void start(Solver* _s, uint32_t nvars) {
        s = _s;
        stack.assign(1, {});
        assigned.assign(nvars, 0);
        value_of.assign(nvars, l_Undef);
    }

    /// The truth value of an outer literal, as the propagator sees it.
    lbool val(const Lit l) const {
        const lbool v = value_of[l.var()];
        if (v == l_Undef) return l_Undef;
        return l.sign() ? (v == l_True ? l_False : l_True) : v;
    }

    void notify_assignment(const vector<Lit>& lits) override {
        EXPECT_FALSE(lits.empty());
        for(const Lit l: lits) {
            EXPECT_TRUE(s->is_observed_var(l.var()))
                << "notified about unobserved var " << l.var()+1;
            EXPECT_FALSE(assigned[l.var()])
                << "var " << l.var()+1 << " assigned twice without a backtrack";
            assigned[l.var()] = 1;
            value_of[l.var()] = l.sign() ? l_False : l_True;
            stack.back().push_back(l);
        }
    }

    void notify_new_decision_level() override {
        stack.push_back({});
        max_level_seen = std::max<uint32_t>(max_level_seen, stack.size()-1);
        compare();
    }

    void notify_backtrack(size_t new_level) override {
        // must always pop at least one level
        ASSERT_LT(new_level + 1, stack.size());
        for(size_t i = new_level+1; i < stack.size(); i++) {
            for(const Lit l: stack[i]) {
                assigned[l.var()] = 0;
                value_of[l.var()] = l_Undef;
            }
        }
        stack.resize(new_level + 1);
        num_backtracks++;
        compare();
    }

    bool cb_check_found_model(const vector<Lit>&) override { compare(); return true; }
    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = false;
        return false;
    }
    Lit cb_add_external_clause_lit() override { return lit_Undef; }

    void compare() {
        vector<vector<Lit>> expected;
        // false: notifications are still owed, the two are allowed to differ
        if (!s->ext_get_observed_trail(expected)) return;
        num_comparisons++;

        vector<vector<Lit>> mine = stack;
        // the order within the root prefix carries no meaning
        std::sort(mine[0].begin(), mine[0].end());
        ASSERT_EQ(mine, expected);
    }
};

// Holds a set of clauses and hands them to the solver during the search, one
// at a time, instead of adding them up front. The answer must not change.
// Inherits the mirror's checks, so the notification contract is still tested
// while clauses are being woven into the trail.
class OraclePropagator : public MirrorPropagator
{
public:
    vector<vector<Lit>> to_hand_over;   // OUTER numbering
    bool forgettable = false;
    size_t next_clause = 0;
    size_t next_lit = 0;
    size_t num_handed_over = 0;

    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = forgettable;
        return next_clause < to_hand_over.size();
    }

    Lit cb_add_external_clause_lit() override {
        assert(next_clause < to_hand_over.size());
        const vector<Lit>& cl = to_hand_over[next_clause];
        if (next_lit == cl.size()) {
            next_lit = 0;
            next_clause++;
            num_handed_over++;
            return lit_Undef;
        }
        return cl[next_lit++];
    }
};

// Owns a set of clauses that the solver never sees, and acts as a complete
// unit propagation engine over them: cb_propagate() hands back an implied
// literal and cb_add_reason_clause_lit() explains it. Reasoning is done purely
// over the trail the mirror has reconstructed from notifications.
class UnitPropagator : public MirrorPropagator
{
public:
    vector<vector<Lit>> theory;      // OUTER numbering
    // The clause that implied each literal, recorded when the propagation is
    // made rather than when it is asked about: with lazy reasons the question
    // comes much later, during conflict analysis.
    vector<size_t> reason_for_lit;   // indexed by Lit::toInt()
    size_t cur_clause = 0;
    size_t cur_lit = 0;
    size_t num_propagations = 0;
    size_t num_explanations = 0;

    void start_theory(Solver* _s, uint32_t nvars) {
        start(_s, nvars);
        reason_for_lit.assign(2*nvars, 0);
    }

    Lit cb_propagate() override {
        for(size_t i = 0; i < theory.size(); i++) {
            Lit implied = lit_Undef;
            bool satisfied = false;
            uint32_t num_free = 0;
            for(const Lit l: theory[i]) {
                const lbool v = val(l);
                if (v == l_True) { satisfied = true; break; }
                if (v == l_Undef) { num_free++; implied = l; }
            }
            if (satisfied) continue;
            // Unit, or already falsified: in the latter case hand back one of
            // its literals -- the solver will see the clause is conflicting.
            if (num_free == 1 || num_free == 0) {
                const Lit ret = (num_free == 1) ? implied : theory[i][0];
                reason_for_lit[ret.toInt()] = i;
                num_propagations++;
                return ret;
            }
        }
        return lit_Undef;
    }

    Lit cb_add_reason_clause_lit(Lit propagated_lit) override {
        if (cur_lit == 0) {
            cur_clause = reason_for_lit[propagated_lit.toInt()];
            num_explanations++;
        }
        const vector<Lit>& cl = theory[cur_clause];
        if (cur_lit == cl.size()) { cur_lit = 0; return lit_Undef; }
        return cl[cur_lit++];
    }
};

// Overrides the solver's branching completely: always decides the lowest
// unassigned observed variable, with a fixed polarity.
class DecidingPropagator : public MirrorPropagator
{
public:
    uint32_t nvars = 0;
    bool sign = false;
    uint32_t num_decisions = 0;
    bool check_is_decision = false;

    Lit cb_decide() override {
        for(uint32_t v = 0; v < nvars; v++) {
            if (val(Lit(v, false)) != l_Undef) continue;
            num_decisions++;
            return Lit(v, sign);
        }
        return lit_Undef;
    }

    bool cb_check_found_model(const vector<Lit>& model) override {
        compare();
        if (check_is_decision) {
            // Every literal we decided is reported as a decision; propagated
            // ones are not.
            for(const Lit l: model) {
                if (s->ext_is_decision(l)) { EXPECT_EQ(l.sign(), sign); }
            }
        }
        return true;
    }
};

// Enumerates models: rejects each complete assignment and blocks it with its
// own negation, until the problem becomes unsatisfiable.
class EnumeratingPropagator : public MirrorPropagator
{
public:
    vector<vector<Lit>> models;      // one literal per observed var
    vector<vector<Lit>> blocking;
    size_t next_clause = 0;
    size_t next_lit = 0;

    bool cb_check_found_model(const vector<Lit>& model) override {
        compare();
        models.push_back(model);
        vector<Lit> block;
        block.reserve(model.size());
        for(const Lit l: model) block.push_back(~l);
        blocking.push_back(block);
        return false;
    }

    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = false;
        return next_clause < blocking.size();
    }

    Lit cb_add_external_clause_lit() override {
        const vector<Lit>& cl = blocking[next_clause];
        if (next_lit == cl.size()) { next_lit = 0; next_clause++; return lit_Undef; }
        return cl[next_lit++];
    }
};

// Everything at once, driven by a deterministic pseudo-random stream: observes
// variables late, propagates sometimes, hands over clauses sometimes, forces
// backtracking sometimes, and rejects any model that violates the theory it
// holds. The answer must still be the one you get by simply adding all the
// clauses up front.
class AdversarialPropagator : public MirrorPropagator
{
public:
    Solver* raw = nullptr;
    vector<vector<Lit>> theory;      // sound clauses the solver never sees
    vector<size_t> reason_for_lit;   // indexed by Lit::toInt()
    vector<size_t> queued;           // theory clauses waiting to be handed over
    size_t cur_clause = 0;
    size_t cur_lit = 0;
    uint32_t backtrack_budget = 0;
    uint64_t rnd_state = 1;
    size_t num_propagations = 0;
    size_t num_clauses_given = 0;
    size_t num_forced_backtracks = 0;
    size_t num_late_observes = 0;
    size_t num_rejected_models = 0;

    uint32_t next() {
        rnd_state = rnd_state * 6364136223846793005ULL + 1442695040888963407ULL;
        return (uint32_t)(rnd_state >> 33);
    }
    bool chance(uint32_t percent) { return (next() % 100) < percent; }

    void start_adversary(Solver* _s, uint32_t nvars, uint32_t seed) {
        raw = _s;
        start(_s, nvars);
        reason_for_lit.assign(2*nvars, 0);
        rnd_state = seed * 2862933555777941757ULL + 3037000493ULL;
    }

    bool all_observed(const vector<Lit>& cl) const {
        for(const Lit l: cl) if (!raw->is_observed_var(l.var())) return false;
        return true;
    }

    // Satisfied / falsified / unit under the propagator's own view.
    bool is_satisfied(const vector<Lit>& cl) const {
        for(const Lit l: cl) if (val(l) == l_True) return true;
        return false;
    }

    Lit cb_propagate() override {
        if (!chance(60)) return lit_Undef;
        for(size_t i = 0; i < theory.size(); i++) {
            if (!all_observed(theory[i])) continue;
            Lit implied = lit_Undef;
            bool satisfied = false;
            uint32_t num_free = 0;
            for(const Lit l: theory[i]) {
                const lbool v = val(l);
                if (v == l_True) { satisfied = true; break; }
                if (v == l_Undef) { num_free++; implied = l; }
            }
            if (satisfied || num_free > 1) continue;
            const Lit ret = (num_free == 1) ? implied : theory[i][0];
            reason_for_lit[ret.toInt()] = i;
            num_propagations++;
            return ret;
        }
        return lit_Undef;
    }

    Lit cb_add_reason_clause_lit(Lit propagated_lit) override {
        if (cur_lit == 0) cur_clause = reason_for_lit[propagated_lit.toInt()];
        const vector<Lit>& cl = theory[cur_clause];
        if (cur_lit == cl.size()) { cur_lit = 0; return lit_Undef; }
        return cl[cur_lit++];
    }

    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = chance(50);
        if (!queued.empty()) return true;
        // occasionally volunteer a clause nobody asked for
        if (!chance(10)) return false;
        for(uint32_t tries = 0; tries < 4; tries++) {
            const size_t i = next() % theory.size();
            if (all_observed(theory[i])) { queued.push_back(i); return true; }
        }
        return false;
    }

    Lit cb_add_external_clause_lit() override {
        const vector<Lit>& cl = theory[queued.front()];
        if (cur_lit == cl.size()) {
            cur_lit = 0;
            queued.erase(queued.begin());
            num_clauses_given++;
            return lit_Undef;
        }
        return cl[cur_lit++];
    }

    Lit cb_decide() override {
        if (backtrack_budget > 0 && stack.size() > 3 && chance(20)) {
            backtrack_budget--;
            num_forced_backtracks++;
            raw->ext_force_backtrack((uint32_t)(next() % (stack.size()-1)));
        }
        return lit_Undef;
    }

    bool cb_check_found_model(const vector<Lit>& model) override {
        compare();
        (void)model;

        // The whole theory has to be expressible before it can be checked, so
        // observe whatever is still missing. That backtracks, and the solver
        // notices and carries on searching.
        bool observed_something = false;
        for(const auto& cl: theory) {
            for(const Lit l: cl) {
                if (!raw->is_observed_var(l.var())) {
                    raw->add_observed_var(l.var());
                    num_late_observes++;
                    observed_something = true;
                }
            }
        }
        if (observed_something) return false;

        for(size_t i = 0; i < theory.size(); i++) {
            if (is_satisfied(theory[i])) continue;
            queued.push_back(i);
            num_rejected_models++;
            return false;
        }
        return true;
    }
};

// Forces the solver back to the root every time the trail gets deep, a fixed
// number of times, and then gets out of the way.
class BacktrackingPropagator : public MirrorPropagator
{
public:
    SATSolver* api = nullptr;
    Solver* raw = nullptr;
    uint32_t budget = 0;
    uint32_t num_forced = 0;

    Lit cb_decide() override {
        if (budget > 0 && stack.size() > 4) {
            budget--;
            num_forced++;
            raw->ext_force_backtrack(1);
        }
        return lit_Undef;
    }
};

}

TEST(user_prop_connect, connect_and_disconnect)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(4);
    s.add_clause(str_to_cl("1, 2"));
    s.add_clause(str_to_cl("-1, 3"));

    s.connect_external_propagator(&p);
    EXPECT_EQ(s.solve(), l_True);
    s.disconnect_external_propagator();

    // and the solver is still usable afterwards
    EXPECT_EQ(s.solve(), l_True);
}

TEST(user_prop_connect, multi_threading_is_refused)
{
    // Connecting first, before any variable exists, used to slip past the
    // check: set_num_threads() would then be accepted, and the next call that
    // flushed the pending variables would hand them to thread 0 alone.
    {
        SATSolver s;
        NoopPropagator p;
        s.connect_external_propagator(&p);
        EXPECT_THROW(s.set_num_threads(4), std::runtime_error);
    }

    // ...and the other way round. phase() and unphase() are the only calls of
    // this family that work without a propagator, so they are the ones that
    // can reach a multi-threaded solver at all.
    {
        SATSolver s;
        NoopPropagator p;
        s.set_num_threads(4);
        EXPECT_THROW(s.connect_external_propagator(&p), std::runtime_error);
        s.new_vars(4);
        EXPECT_THROW(s.phase(Lit(0, false)), std::runtime_error);
        EXPECT_THROW(s.unphase(0), std::runtime_error);

        // the variables are still pending, so the solver itself is unharmed
        s.add_clause(str_to_cl("1, 2"));
        EXPECT_EQ(s.solve(), l_True);
    }
}

TEST(user_prop_connect, model_changing_simplification_is_refused)
{
    // Adding blocked clauses keeps the formula satisfiable but drops the models
    // that do not satisfy them, and the propagator's own constraints had no say
    // in which ones those are.
    SATSolver s;
    NoopPropagator p;
    s.new_vars(4);
    s.add_clause(str_to_cl("1, 2"));
    s.connect_external_propagator(&p);
    s.add_observed_var(0);
    EXPECT_THROW(s.reverse_bce(), std::runtime_error);

    // ...and it is fine again once the propagator is gone
    s.disconnect_external_propagator();
    EXPECT_EQ(s.solve(), l_True);
}

TEST(user_prop_connect, no_propagator_no_change)
{
    // The exact same problem with and without a no-op propagator must give the
    // same answer.
    for(int with_prop = 0; with_prop < 2; with_prop++) {
        SATSolver s;
        NoopPropagator p;
        s.new_vars(5);
        s.add_clause(str_to_cl("1, 2, 3"));
        s.add_clause(str_to_cl("-1, -2"));
        s.add_clause(str_to_cl("-2, -3"));
        s.add_clause(str_to_cl("-1, -3"));
        if (with_prop) s.connect_external_propagator(&p);
        EXPECT_EQ(s.solve(), l_True);
    }
}

TEST(user_prop_observe, observe_and_unobserve)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(6);
    s.connect_external_propagator(&p);

    EXPECT_FALSE(s.is_observed_var(0));
    s.add_observed_var(0);
    s.add_observed_var(3);
    EXPECT_TRUE(s.is_observed_var(0));
    EXPECT_TRUE(s.is_observed_var(3));
    EXPECT_FALSE(s.is_observed_var(1));

    // observing twice is idempotent
    s.add_observed_var(0);
    EXPECT_TRUE(s.is_observed_var(0));

    s.remove_observed_var(0);
    EXPECT_FALSE(s.is_observed_var(0));
    EXPECT_TRUE(s.is_observed_var(3));

    s.reset_observed_vars();
    EXPECT_FALSE(s.is_observed_var(3));
}

TEST(user_prop_observe, disconnect_resets_observed)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(6);
    s.connect_external_propagator(&p);
    s.add_observed_var(2);
    EXPECT_TRUE(s.is_observed_var(2));

    s.disconnect_external_propagator();
    EXPECT_FALSE(s.is_observed_var(2));
}

TEST(user_prop_observe, observe_var_added_after_connect)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(2);
    s.connect_external_propagator(&p);
    s.new_vars(3);
    s.add_observed_var(4);
    EXPECT_TRUE(s.is_observed_var(4));
    EXPECT_EQ(s.solve(), l_True);
}

TEST(user_prop_phase, forced_phase_shows_in_model)
{
    // With no constraints at all, every variable is decided, so a forced phase
    // fully determines the model.
    for(int polarity = 0; polarity < 2; polarity++) {
        SATSolver s;
        NoopPropagator p;
        s.new_vars(8);
        s.connect_external_propagator(&p);
        for(uint32_t i = 0; i < 8; i++) s.phase(Lit(i, polarity == 0));

        EXPECT_EQ(s.solve(), l_True);
        const auto& model = s.get_model();
        for(uint32_t i = 0; i < 8; i++) {
            EXPECT_EQ(model[i], polarity == 0 ? l_False : l_True);
        }
    }
}

TEST(user_prop_phase, unphase_gives_control_back)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(4);
    s.connect_external_propagator(&p);
    s.phase(Lit(0, false));
    s.unphase(0);
    // Nothing to assert about the polarity now, but it must still solve.
    EXPECT_EQ(s.solve(), l_True);
}

// Observing v while the solver is opening the level for z backtracks over the
// earlier x -> v assignment. The pending z decision belongs to that discarded
// trail and must not be installed at the root. If it is, the valid external
// unit -z is mistaken for a root conflict and the satisfiable problem is
// reported UNSAT.
class ObservesDuringNewLevelPropagator : public NoopPropagator
{
public:
    SATSolver* raw = nullptr;
    uint32_t levels_opened = 0;
    size_t next_reason_lit = 0;
    bool chose_x = false;
    bool observed_v = false;
    bool propagated_not_z = false;

    void notify_new_decision_level() override {
        levels_opened++;
        if (levels_opened == 2) {
            raw->add_observed_var(1);
            observed_v = true;
        }
    }

    Lit cb_decide() override {
        if (chose_x) return lit_Undef;
        chose_x = true;
        return Lit(0, false);
    }

    Lit cb_propagate() override {
        if (!observed_v || propagated_not_z) return lit_Undef;
        propagated_not_z = true;
        return Lit(2, true);
    }

    Lit cb_add_reason_clause_lit(Lit propagated_lit) override {
        EXPECT_EQ(propagated_lit, Lit(2, true));
        if (next_reason_lit++ == 0) return propagated_lit;
        next_reason_lit = 0;
        return lit_Undef;
    }
};

TEST(user_prop_observe, observing_during_new_level_discards_pending_decision)
{
    SATSolver s;
    ObservesDuringNewLevelPropagator p;
    p.raw = &s;
    s.set_no_simplify();
    s.new_vars(3); // x, v, z
    s.add_clause(vector<Lit>{Lit(0, true), Lit(1, false)}); // x -> v
    s.connect_external_propagator(&p);
    s.add_observed_var(0);
    s.add_observed_var(2);
    s.phase(Lit(2, false)); // make the discarded internal decision z, not -z

    ASSERT_EQ(s.solve(), l_True);
    EXPECT_TRUE(p.observed_v);
    EXPECT_TRUE(p.propagated_not_z);
    EXPECT_EQ(s.get_model()[2], l_False);
}

TEST(user_prop_is_decision, unassigned_is_not_a_decision)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(3);
    s.connect_external_propagator(&p);
    s.add_observed_var(0);
    EXPECT_FALSE(s.is_decision(Lit(0, false)));
}

TEST(user_prop_is_decision, root_level_unit_is_not_a_decision)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(3);
    s.connect_external_propagator(&p);
    s.add_observed_var(0);
    s.add_clause(str_to_cl("1"));
    EXPECT_EQ(s.solve(), l_True);
    EXPECT_FALSE(s.is_decision(Lit(0, false)));
}

////////////////////////////
// WP1: observed variables are frozen
////////////////////////////

TEST(user_prop_freeze, observed_var_survives_bve)
{
    // Variable 3 occurs only in the two clauses below, so BVE would resolve it
    // away. Observing it must keep it.
    for(int observe = 0; observe < 2; observe++) {
        SATSolver s;
        NoopPropagator p;
        s.new_vars(10);
        s.connect_external_propagator(&p);
        if (observe) s.add_observed_var(2);

        s.add_clause(str_to_cl("1, 3"));
        s.add_clause(str_to_cl("2, -3"));
        s.add_clause(str_to_cl("4, 5"));
        s.add_clause(str_to_cl("-4, 6"));
        std::string strategy = "occ-bve";
        EXPECT_EQ(s.simplify(nullptr, &strategy), l_Undef);

        if (observe) { EXPECT_FALSE(s.removed_var(2)); }
        else { EXPECT_TRUE(s.removed_var(2)); }
    }
}

TEST(user_prop_freeze, observed_var_not_replaced)
{
    // 1 <-> 2, so SCC-based equivalent literal replacement would merge them,
    // and one of the two would stop existing in the search.
    for(int observe = 0; observe < 2; observe++) {
        SATSolver s;
        NoopPropagator p;
        s.new_vars(6);
        s.connect_external_propagator(&p);
        if (observe) {
            s.add_observed_var(0);
            s.add_observed_var(1);
        }

        s.add_clause(str_to_cl("1, -2"));
        s.add_clause(str_to_cl("-1, 2"));
        s.add_clause(str_to_cl("1, 3, 4"));
        s.add_clause(str_to_cl("-3, 5"));
        std::string strategy = "must-scc-vrepl";
        EXPECT_EQ(s.simplify(nullptr, &strategy), l_Undef);

        const bool merged = s.removed_var(0) || s.removed_var(1);
        EXPECT_EQ(merged, observe == 0);
    }
}

TEST(user_prop_freeze, eliminated_var_is_uneliminated_when_observed)
{
    SATSolver s;
    NoopPropagator p;
    s.new_vars(10);
    s.add_clause(str_to_cl("1, 3"));
    s.add_clause(str_to_cl("2, -3"));
    s.add_clause(str_to_cl("4, 5"));
    std::string strategy = "occ-bve";
    EXPECT_EQ(s.simplify(nullptr, &strategy), l_Undef);
    ASSERT_TRUE(s.removed_var(2));

    s.connect_external_propagator(&p);
    s.add_observed_var(2);
    EXPECT_FALSE(s.removed_var(2));
    EXPECT_TRUE(s.is_observed_var(2));
    EXPECT_EQ(s.solve(), l_True);
}

// A random-ish 3-SAT instance, deterministic across runs.
static void add_random_3sat(Solver* s, uint32_t nvars, uint32_t ncls, uint32_t seed)
{
    uint64_t st = seed * 6364136223846793005ULL + 1442695040888963407ULL;
    auto next = [&st]() {
        st = st * 6364136223846793005ULL + 1442695040888963407ULL;
        return (uint32_t)(st >> 33);
    };
    s->new_vars(nvars);
    for(uint32_t i = 0; i < ncls; i++) {
        vector<Lit> cl;
        while(cl.size() < 3) {
            const uint32_t v = next() % nvars;
            bool dup = false;
            for(const Lit l: cl) if (l.var() == v) dup = true;
            if (!dup) cl.push_back(Lit(v, next() & 1));
        }
        s->add_clause_outside(cl);
        if (!s->okay()) return;
    }
}

namespace CMSat {

struct UserPropFreezeTest : public ::testing::Test {
    UserPropFreezeTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropFreezeTest() { delete s; }

    SolverConf conf;
    Solver* s = nullptr;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropFreezeTest, no_chrono_backtracking_with_propagator)
{
    NoopPropagator p;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    add_random_3sat(s, 120, 520, 42);
    must_inter.store(false, std::memory_order_relaxed);
    s->solve_with_assumptions();
    EXPECT_EQ(s->chrono_backtrack, 0U);
    EXPECT_GT(s->non_chrono_backtrack, 0U);
}

TEST_F(UserPropFreezeTest, no_gauss_jordan_matrices_with_propagator)
{
    NoopPropagator p;
    s = new Solver(&conf, &must_inter);
    s->conf.doFindXors = true;
    s->connect_external_propagator(&p);
    s->new_vars(30);
    // A set of XORs over the same variables: normally a Gauss-Jordan matrix.
    for(uint32_t i = 0; i + 3 < 24; i += 2) {
        vector<uint32_t> vars = {i, i+1, i+2, i+3};
        s->add_xor_clause_outside(vars, (i/2) % 2 == 0);
    }
    s->solve_with_assumptions();
    EXPECT_TRUE(s->gmatrices.empty());
}

TEST_F(UserPropFreezeTest, matrices_come_back_after_disconnecting)
{
    // Switching matrices off must not be permanent: once the propagator is
    // gone there is nothing stopping Gauss-Jordan any more.
    NoopPropagator p;
    s = new Solver(&conf, &must_inter);
    s->conf.doFindXors = true;
    s->connect_external_propagator(&p);
    s->new_vars(30);
    for(uint32_t i = 0; i + 3 < 24; i += 2) {
        vector<uint32_t> vars = {i, i+1, i+2, i+3};
        s->add_xor_clause_outside(vars, (i/2) % 2 == 0);
    }
    must_inter.store(false, std::memory_order_relaxed);
    s->solve_with_assumptions();
    ASSERT_TRUE(s->gmatrices.empty());

    s->disconnect_external_propagator();
    must_inter.store(false, std::memory_order_relaxed);
    s->solve_with_assumptions();
    EXPECT_FALSE(s->gmatrices.empty()) << "Gauss-Jordan never came back";
}

}

////////////////////////////
// WP2: trail notifications
////////////////////////////

namespace CMSat {

struct UserPropNotifyTest : public ::testing::Test {
    UserPropNotifyTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropNotifyTest() { delete s; }

    // Observe every third variable, mirror the trail, and check it at every
    // point where the propagator and the solver must agree.
    void run_mirror(uint32_t nvars, uint32_t ncls, uint32_t seed, uint32_t observe_every)
    {
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        add_random_3sat(s, nvars, ncls, seed);
        for(uint32_t v = 0; v < nvars; v += observe_every) s->add_observed_var(v);
        p.start(s, nvars);

        // solve_with_assumptions() raises the interrupt flag on the way out
        must_inter.store(false, std::memory_order_relaxed);
        const lbool ret = s->solve_with_assumptions();
        EXPECT_NE(ret, l_Undef);
        EXPECT_GT(p.num_comparisons, 0U) << "the mirror never got to compare anything";
        delete s;
        s = nullptr;
    }

    SolverConf conf;
    Solver* s = nullptr;
    MirrorPropagator p;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropNotifyTest, mirror_small_sat)
{
    run_mirror(40, 130, 7, 3);
    EXPECT_GT(p.max_level_seen, 0U);
}

TEST_F(UserPropNotifyTest, mirror_larger_with_inprocessing)
{
    // Big enough to trigger restarts, clause cleaning, simplification and
    // renumbering -- all of which move the trail around behind the propagator.
    run_mirror(200, 860, 11, 2);
    EXPECT_GT(p.num_backtracks, 0U);
}

TEST_F(UserPropNotifyTest, mirror_unsat)
{
    run_mirror(30, 220, 23, 1);
}

TEST_F(UserPropNotifyTest, mirror_all_observed)
{
    run_mirror(120, 500, 5, 1);
}

TEST_F(UserPropNotifyTest, mirror_seeds)
{
    for(uint32_t seed = 1; seed <= 12; seed++) {
        run_mirror(60, 240, seed, 2);
    }
}

TEST_F(UserPropNotifyTest, mirror_survives_incremental_solving)
{
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    add_random_3sat(s, 60, 150, 3);
    for(uint32_t v = 0; v < 60; v += 2) s->add_observed_var(v);
    p.start(s, 60);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    const uint32_t after_first = p.num_comparisons;
    EXPECT_GT(after_first, 0U);

    // Solve again: the propagator keeps its level-0 view across the calls.
    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_GT(p.num_comparisons, after_first);
}

TEST_F(UserPropNotifyTest, observing_an_already_fixed_variable)
{
    // The units are on the trail before the variables become observed, so the
    // notification cursor has to hand them over exactly once.
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(8);
    s->add_clause_outside(str_to_cl("1"));
    s->add_clause_outside(str_to_cl("-2"));
    s->add_clause_outside(str_to_cl("3, 4"));
    for(uint32_t v = 0; v < 8; v++) s->add_observed_var(v);
    p.start(s, 8);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_GT(p.num_comparisons, 0U);
}

TEST_F(UserPropNotifyTest, observing_a_fixed_variable_after_a_solve)
{
    // By now renumbering has wiped the literals of the level-0 trail, so the
    // cursor cannot see this assignment at all and it has to be handed over
    // separately.
    s = new Solver(&conf, &must_inter);
    s->conf.simplify_at_startup = true;
    s->conf.full_simplify_at_startup = true;
    s->connect_external_propagator(&p);
    add_random_3sat(s, 60, 150, 3);
    s->add_clause_outside(str_to_cl("1"));
    p.start(s, 60);

    must_inter.store(false, std::memory_order_relaxed);
    ASSERT_EQ(s->solve_with_assumptions(), l_True);

    s->add_observed_var(0);
    for(uint32_t v = 1; v < 60; v += 3) s->add_observed_var(v);
    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_GT(p.num_comparisons, 0U);
}

TEST_F(UserPropNotifyTest, no_notifications_from_inprocessing)
{
    // Everything observed, heavy simplification: any assignment leaking out of
    // probing or distillation would break the mirror.
    s = new Solver(&conf, &must_inter);
    s->conf.simplify_at_startup = true;
    s->conf.full_simplify_at_startup = true;
    s->connect_external_propagator(&p);
    add_random_3sat(s, 150, 620, 31);
    for(uint32_t v = 0; v < 150; v++) s->add_observed_var(v);
    p.start(s, 150);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_NE(s->solve_with_assumptions(), l_Undef);
    EXPECT_GT(p.num_comparisons, 0U);
}

}

////////////////////////////
// WP3: external clause addition during the search
////////////////////////////

namespace CMSat {

// Deterministic random 3-SAT as a plain list of clauses in OUTER numbering.
static vector<vector<Lit>> gen_3sat(uint32_t nvars, uint32_t ncls, uint32_t seed)
{
    uint64_t st = seed * 6364136223846793005ULL + 1442695040888963407ULL;
    auto next = [&st]() {
        st = st * 6364136223846793005ULL + 1442695040888963407ULL;
        return (uint32_t)(st >> 33);
    };
    vector<vector<Lit>> out;
    for(uint32_t i = 0; i < ncls; i++) {
        vector<Lit> cl;
        while(cl.size() < 3) {
            const uint32_t v = next() % nvars;
            bool dup = false;
            for(const Lit l: cl) if (l.var() == v) dup = true;
            if (!dup) cl.push_back(Lit(v, next() & 1));
        }
        out.push_back(cl);
    }
    return out;
}

static bool model_satisfies(const vector<lbool>& model, const vector<vector<Lit>>& cls)
{
    for(const auto& cl: cls) {
        bool sat = false;
        for(const Lit l: cl) {
            if (l.var() >= model.size()) return false;
            if (model[l.var()] == (l.sign() ? l_False : l_True)) { sat = true; break; }
        }
        if (!sat) return false;
    }
    return true;
}

struct UserPropClauseTest : public ::testing::Test {
    UserPropClauseTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropClauseTest() { delete s; delete ref; }

    lbool solve_plain(const vector<vector<Lit>>& cls, uint32_t nvars) {
        ref = new Solver(&conf, &must_inter);
        ref->new_vars(nvars);
        for(const auto& cl: cls) {
            vector<Lit> tmp = cl;
            ref->add_clause_outside(tmp);
        }
        must_inter.store(false, std::memory_order_relaxed);
        return ref->solve_with_assumptions();
    }

    // 'split' clauses go in up front, the rest arrive through the propagator.
    lbool solve_split(const vector<vector<Lit>>& cls, uint32_t nvars, size_t split) {
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        s->new_vars(nvars);
        for(size_t i = 0; i < split; i++) {
            vector<Lit> tmp = cls[i];
            s->add_clause_outside(tmp);
        }
        for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
        for(size_t i = split; i < cls.size(); i++) p.to_hand_over.push_back(cls[i]);
        p.start(s, nvars);

        must_inter.store(false, std::memory_order_relaxed);
        return s->solve_with_assumptions();
    }

    SolverConf conf;
    Solver* s = nullptr;
    Solver* ref = nullptr;
    OraclePropagator p;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropClauseTest, same_answer_as_adding_up_front_sat)
{
    const uint32_t nvars = 60;
    auto cls = gen_3sat(nvars, 200, 17);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(expected, l_True);

    ASSERT_EQ(solve_split(cls, nvars, 140), l_True);
    EXPECT_EQ(p.num_handed_over, cls.size() - 140);
    EXPECT_TRUE(model_satisfies(s->get_model(), cls));
}

TEST_F(UserPropClauseTest, same_answer_as_adding_up_front_unsat)
{
    const uint32_t nvars = 24;
    auto cls = gen_3sat(nvars, 180, 5);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(expected, l_False);
    ASSERT_EQ(solve_split(cls, nvars, 90), l_False);
}

TEST_F(UserPropClauseTest, forgettable_clauses_give_the_same_answer)
{
    const uint32_t nvars = 60;
    auto cls = gen_3sat(nvars, 200, 17);
    p.forgettable = true;
    ASSERT_EQ(solve_split(cls, nvars, 140), l_True);
    EXPECT_TRUE(model_satisfies(s->get_model(), cls));
}

TEST_F(UserPropClauseTest, everything_through_the_propagator)
{
    const uint32_t nvars = 40;
    auto cls = gen_3sat(nvars, 120, 3);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(solve_split(cls, nvars, 0), expected);
    if (expected == l_True) { EXPECT_TRUE(model_satisfies(s->get_model(), cls)); }
}

TEST_F(UserPropClauseTest, many_seeds)
{
    for(uint32_t seed = 1; seed <= 15; seed++) {
        const uint32_t nvars = 30;
        auto cls = gen_3sat(nvars, 125, seed);
        const lbool expected = solve_plain(cls, nvars);
        ASSERT_EQ(solve_split(cls, nvars, cls.size()/2), expected) << "seed " << seed;
        if (expected == l_True) {
            EXPECT_TRUE(model_satisfies(s->get_model(), cls)) << "seed " << seed;
        }
        delete s; s = nullptr;
        delete ref; ref = nullptr;
        p = OraclePropagator();
    }
}

TEST_F(UserPropClauseTest, unit_and_empty_clauses_from_the_propagator)
{
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(8);
    s->add_clause_outside(str_to_cl("1, 2"));
    s->add_clause_outside(str_to_cl("-1, 3"));
    for(uint32_t v = 0; v < 8; v++) s->add_observed_var(v);

    // 1, then -1: the second makes the problem unsatisfiable
    p.to_hand_over.push_back(str_to_cl("1"));
    p.to_hand_over.push_back(str_to_cl("-1"));
    p.start(s, 8);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_False);
    EXPECT_FALSE(s->okay());
}

TEST_F(UserPropClauseTest, frat_proof_is_written_without_tripping_anything)
{
    // Full checking of the emitted proof needs the frat-xor / cake_xlrup
    // toolchain (see README_VERIFIER.md); what is checked here is that the
    // FRAT path runs, produces output, and still gives the right answer.
    const uint32_t nvars = 24;
    auto cls = gen_3sat(nvars, 180, 5);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(expected, l_False);

    const char* fname = "user_prop_test.frat";
    FILE* f = fopen(fname, "wb");
    ASSERT_NE(f, nullptr);

    s = new Solver(&conf, &must_inter);
    s->add_frat(f);
    s->connect_external_propagator(&p);
    s->new_vars(nvars);
    for(size_t i = 0; i < 90; i++) {
        vector<Lit> tmp = cls[i];
        s->add_clause_outside(tmp);
    }
    for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
    for(size_t i = 90; i < cls.size(); i++) p.to_hand_over.push_back(cls[i]);
    p.start(s, nvars);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_False);
    delete s; s = nullptr;
    fclose(f);

    FILE* check = fopen(fname, "rb");
    ASSERT_NE(check, nullptr);
    fseek(check, 0, SEEK_END);
    EXPECT_GT(ftell(check), 0);
    fclose(check);
    std::remove(fname);
}

TEST_F(UserPropClauseTest, forgettable_is_ignored_under_frat)
{
    // A redundant input clause cannot be represented in the proof, so a
    // forgettable clause is simply kept. Answer must not change.
    const uint32_t nvars = 30;
    auto cls = gen_3sat(nvars, 125, 4);
    const lbool expected = solve_plain(cls, nvars);

    const char* fname = "user_prop_test_forget.frat";
    FILE* f = fopen(fname, "wb");
    ASSERT_NE(f, nullptr);

    s = new Solver(&conf, &must_inter);
    s->add_frat(f);
    s->connect_external_propagator(&p);
    s->new_vars(nvars);
    for(size_t i = 0; i < 60; i++) {
        vector<Lit> tmp = cls[i];
        s->add_clause_outside(tmp);
    }
    for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
    p.forgettable = true;
    for(size_t i = 60; i < cls.size(); i++) p.to_hand_over.push_back(cls[i]);
    p.start(s, nvars);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), expected);
    delete s; s = nullptr;
    fclose(f);
    std::remove(fname);
}

TEST_F(UserPropClauseTest, propagator_forces_a_specific_model)
{
    // Pin every variable with a unit clause handed over during the search.
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(12);
    s->add_clause_outside(str_to_cl("1, 2, 3"));
    for(uint32_t v = 0; v < 12; v++) {
        s->add_observed_var(v);
        p.to_hand_over.push_back(vector<Lit>{Lit(v, v % 2 == 0)});
    }
    p.start(s, 12);

    must_inter.store(false, std::memory_order_relaxed);
    ASSERT_EQ(s->solve_with_assumptions(), l_True);
    for(uint32_t v = 0; v < 12; v++) {
        EXPECT_EQ(s->get_model()[v], v % 2 == 0 ? l_False : l_True) << "var " << v+1;
    }
}

// Drives the search down a known chain of decisions, then hands over one clause
// at a chosen depth and records what the trail did in response.
class DeepHandoverPropagator : public MirrorPropagator
{
public:
    uint32_t chain = 0;              // decide var 0..chain-1 true, one per level
    uint32_t hand_over_at = 0;       // ...and give the clause at this level
    vector<Lit> clause;              // OUTER numbering
    size_t next_lit = 0;
    bool handed = false;
    uint32_t backtracks_at_handover = 0;
    uint32_t level_at_handover = 0;
    uint32_t backtracks_after = 0;
    uint32_t level_after = 0;
    bool saw_after = false;

    Lit cb_decide() override {
        // The clause is handed over between two decisions, so the first
        // cb_decide() after it tells us what the hand-over did to the trail.
        if (handed && !saw_after) {
            saw_after = true;
            backtracks_after = num_backtracks;
            level_after = stack.size()-1;
        }
        for(uint32_t v = 0; v < chain; v++) {
            if (val(Lit(v, false)) == l_Undef) return Lit(v, false);
        }
        return lit_Undef;
    }

    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = false;
        if (handed || stack.size()-1 < hand_over_at) return false;
        backtracks_at_handover = num_backtracks;
        level_at_handover = stack.size()-1;
        return true;
    }

    Lit cb_add_external_clause_lit() override {
        if (next_lit == clause.size()) { next_lit = 0; handed = true; return lit_Undef; }
        return clause[next_lit++];
    }
};

// Every 'o' (original clause) line of a text FRAT proof, literals only.
static vector<vector<Lit>> read_frat_original_clauses(const char* fname)
{
    vector<vector<Lit>> ret;
    FILE* f = fopen(fname, "rb");
    if (f == nullptr) return ret;
    char line[8192];
    while (fgets(line, sizeof(line), f) != nullptr) {
        if (line[0] != 'o' || line[1] != ' ') continue;
        vector<Lit> cl;
        const char* at = line+2;
        bool first = true; // the ID
        while (true) {
            char* end = nullptr;
            const long v = strtol(at, &end, 10);
            if (end == at) break;
            at = end;
            if (first) { first = false; continue; }
            if (v == 0) break;
            cl.push_back(Lit((uint32_t)std::labs(v)-1, v < 0));
        }
        std::sort(cl.begin(), cl.end());
        ret.push_back(cl);
    }
    fclose(f);
    return ret;
}

TEST_F(UserPropClauseTest, external_clauses_are_original_clauses_in_the_proof)
{
    // An external clause enters the proof as an input clause (JAIR 81, 3.6), so
    // what comes out certifies the CNF *and* everything the propagator handed
    // over. Check it is written down, and written down over the right variables:
    // the proof writer renumbers what it is given, and this path hands it
    // literals that are already in the user's numbering.
    const char* fname = "user_prop_test_orig.frat";
    FILE* f = fopen(fname, "wb");
    ASSERT_NE(f, nullptr);

    DeepHandoverPropagator dp;
    dp.chain = 6;
    dp.hand_over_at = 6;
    dp.clause = str_to_cl("7, -8, 9");

    s = new Solver(&conf, &must_inter);
    s->add_frat(f);
    s->connect_external_propagator(&dp);
    s->new_vars(12);
    for(uint32_t v = 0; v < 12; v++) s->add_observed_var(v);
    dp.start(s, 12);

    must_inter.store(false, std::memory_order_relaxed);
    ASSERT_EQ(s->solve_with_assumptions(), l_True);
    ASSERT_TRUE(dp.handed);
    delete s; s = nullptr;
    fclose(f);

    vector<Lit> want = dp.clause;
    std::sort(want.begin(), want.end());
    const vector<vector<Lit>> got = read_frat_original_clauses(fname);
    EXPECT_NE(std::find(got.begin(), got.end(), want), got.end())
        << "the external clause is not in the proof as an original clause";
    std::remove(fname);
}

TEST_F(UserPropClauseTest, a_satisfied_clause_does_not_move_the_trail)
{
    // Decisions put var v on level v+1, all true. The clause is satisfied by
    // var 1 on level 1, and falsified elsewhere on levels 2 and 3 -- so the
    // literal that satisfies it can never be undone while the clause is still
    // watched on a falsified literal. There is nothing to repair, and the
    // solver must not throw away levels 4..6 to find that out.
    DeepHandoverPropagator dp;
    dp.chain = 6;
    dp.hand_over_at = 6;
    dp.clause = str_to_cl("1, -3, -2");

    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&dp);
    s->new_vars(12);
    for(uint32_t v = 0; v < 12; v++) s->add_observed_var(v);
    dp.start(s, 12);

    must_inter.store(false, std::memory_order_relaxed);
    ASSERT_EQ(s->solve_with_assumptions(), l_True);
    ASSERT_TRUE(dp.handed);
    ASSERT_TRUE(dp.saw_after);
    EXPECT_EQ(dp.level_at_handover, 6U);
    EXPECT_EQ(dp.level_after, dp.level_at_handover);
    EXPECT_EQ(dp.backtracks_after, dp.backtracks_at_handover);
}

TEST_F(UserPropClauseTest, a_clause_that_should_have_propagated_lower_backtracks)
{
    // The other side of the same coin: the clause is satisfied only by var 6 on
    // level 6, above both of its falsified literals. Backtracking to level 3 is
    // what re-derives var 6 on the level it actually belongs to, and keeps the
    // clause propagating rather than silently unit.
    DeepHandoverPropagator dp;
    dp.chain = 6;
    dp.hand_over_at = 6;
    dp.clause = str_to_cl("6, -3, -2");

    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&dp);
    s->new_vars(12);
    for(uint32_t v = 0; v < 12; v++) s->add_observed_var(v);
    dp.start(s, 12);

    must_inter.store(false, std::memory_order_relaxed);
    ASSERT_EQ(s->solve_with_assumptions(), l_True);
    ASSERT_TRUE(dp.handed);
    ASSERT_TRUE(dp.saw_after);
    EXPECT_EQ(dp.level_at_handover, 6U);
    EXPECT_EQ(dp.level_after, 3U);
    EXPECT_EQ(dp.backtracks_after, dp.backtracks_at_handover + 1);
}

}

////////////////////////////
// WP4: external propagation with eager reason clauses
////////////////////////////

namespace CMSat {

struct UserPropPropagateTest : public ::testing::Test {
    UserPropPropagateTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropPropagateTest() { delete s; delete ref; }

    lbool solve_plain(const vector<vector<Lit>>& cls, uint32_t nvars) {
        delete ref;
        ref = new Solver(&conf, &must_inter);
        ref->new_vars(nvars);
        for(const auto& cl: cls) {
            vector<Lit> tmp = cl;
            ref->add_clause_outside(tmp);
        }
        must_inter.store(false, std::memory_order_relaxed);
        return ref->solve_with_assumptions();
    }

    // The first 'split' clauses go to the solver; the rest exist only inside
    // the propagator, which propagates over them and explains itself.
    lbool solve_with_theory(const vector<vector<Lit>>& cls, uint32_t nvars, size_t split,
                            bool lazy_reasons = false) {
        delete s;
        conf.ext_lazy_reasons = lazy_reasons;
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        s->new_vars(nvars);
        for(size_t i = 0; i < split; i++) {
            vector<Lit> tmp = cls[i];
            s->add_clause_outside(tmp);
        }
        for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
        p.theory.clear();
        for(size_t i = split; i < cls.size(); i++) p.theory.push_back(cls[i]);
        p.start_theory(s, nvars);

        must_inter.store(false, std::memory_order_relaxed);
        return s->solve_with_assumptions();
    }

    SolverConf conf;
    Solver* s = nullptr;
    Solver* ref = nullptr;
    UnitPropagator p;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropPropagateTest, theory_propagation_matches_plain_solving_sat)
{
    const uint32_t nvars = 60;
    auto cls = gen_3sat(nvars, 200, 17);
    ASSERT_EQ(solve_plain(cls, nvars), l_True);
    ASSERT_EQ(solve_with_theory(cls, nvars, 140), l_True);
    EXPECT_GT(p.num_propagations, 0U);
    EXPECT_TRUE(model_satisfies(s->get_model(), cls));
}

TEST_F(UserPropPropagateTest, theory_propagation_matches_plain_solving_unsat)
{
    const uint32_t nvars = 24;
    auto cls = gen_3sat(nvars, 180, 5);
    ASSERT_EQ(solve_plain(cls, nvars), l_False);
    ASSERT_EQ(solve_with_theory(cls, nvars, 90), l_False);
    EXPECT_GT(p.num_propagations, 0U);
}

TEST_F(UserPropPropagateTest, whole_problem_in_the_propagator)
{
    // The solver gets no clauses at all: every implication and every conflict
    // comes out of the propagator, through reason clauses only.
    const uint32_t nvars = 25;
    auto cls = gen_3sat(nvars, 100, 9);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(solve_with_theory(cls, nvars, 0), expected);
    if (expected == l_True) { EXPECT_TRUE(model_satisfies(s->get_model(), cls)); }
}

TEST_F(UserPropPropagateTest, many_seeds)
{
    for(uint32_t seed = 1; seed <= 15; seed++) {
        const uint32_t nvars = 30;
        auto cls = gen_3sat(nvars, 125, seed);
        const lbool expected = solve_plain(cls, nvars);
        ASSERT_EQ(solve_with_theory(cls, nvars, cls.size()/2), expected)
            << "seed " << seed;
        if (expected == l_True) {
            EXPECT_TRUE(model_satisfies(s->get_model(), cls)) << "seed " << seed;
        }
        p = UnitPropagator();
    }
}

TEST_F(UserPropPropagateTest, forgettable_reason_clauses)
{
    const uint32_t nvars = 60;
    auto cls = gen_3sat(nvars, 200, 17);
    p.are_reasons_forgettable = true;
    ASSERT_EQ(solve_with_theory(cls, nvars, 140), l_True);
    EXPECT_TRUE(model_satisfies(s->get_model(), cls));
}

TEST_F(UserPropPropagateTest, lazy_propagator_is_never_asked)
{
    const uint32_t nvars = 40;
    auto cls = gen_3sat(nvars, 120, 3);
    p.is_lazy = true;
    solve_with_theory(cls, nvars, cls.size());   // nothing left for the theory
    EXPECT_EQ(p.num_propagations, 0U);

    // ...and never told anything either, so the mirror it inherits stays as it
    // was started: no levels, no literals, and nothing it could compare.
    EXPECT_EQ(p.num_backtracks, 0U);
    EXPECT_EQ(p.max_level_seen, 0U);
    EXPECT_EQ(p.num_comparisons, 0U);
    ASSERT_EQ(p.stack.size(), 1U);
    EXPECT_TRUE(p.stack[0].empty());
}

}

////////////////////////////
// WP5: decisions, forced backtracking and solution analysis
////////////////////////////

namespace CMSat {

// Brute-force model count over 'nvars' variables.
static uint32_t count_models(const vector<vector<Lit>>& cls, uint32_t nvars)
{
    uint32_t count = 0;
    for(uint32_t mask = 0; mask < (1U << nvars); mask++) {
        bool all_sat = true;
        for(const auto& cl: cls) {
            bool sat = false;
            for(const Lit l: cl) {
                const bool v = (mask >> l.var()) & 1;
                if (v != l.sign()) { sat = true; break; }
            }
            if (!sat) { all_sat = false; break; }
        }
        if (all_sat) count++;
    }
    return count;
}

struct UserPropDecideTest : public ::testing::Test {
    UserPropDecideTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropDecideTest() { delete s; }

    SolverConf conf;
    Solver* s = nullptr;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropDecideTest, cb_decide_drives_the_search)
{
    for(int sign = 0; sign < 2; sign++) {
        DecidingPropagator p;
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        s->new_vars(8);
        for(uint32_t v = 0; v < 8; v++) s->add_observed_var(v);
        p.nvars = 8;
        p.sign = (sign == 1);
        p.check_is_decision = true;
        p.start(s, 8);

        must_inter.store(false, std::memory_order_relaxed);
        ASSERT_EQ(s->solve_with_assumptions(), l_True);
        EXPECT_EQ(p.num_decisions, 8U);
        for(uint32_t v = 0; v < 8; v++) {
            EXPECT_EQ(s->get_model()[v], sign == 1 ? l_False : l_True) << "var " << v+1;
        }
        delete s; s = nullptr;
    }
}

TEST_F(UserPropDecideTest, cb_decide_is_ignored_for_assigned_literals)
{
    // The propagator keeps asking for variable 1, which unit propagation has
    // already fixed; the solver must fall back on its own heuristic.
    class Stubborn : public DecidingPropagator {
    public:
        Lit cb_decide() override { num_decisions++; return Lit(0, false); }
    } p;

    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(6);
    s->add_clause_outside(str_to_cl("1"));
    for(uint32_t v = 0; v < 6; v++) s->add_observed_var(v);
    p.nvars = 6;
    p.start(s, 6);

    must_inter.store(false, std::memory_order_relaxed);
    ASSERT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_GT(p.num_decisions, 0U);
    EXPECT_EQ(s->get_model()[0], l_True);
}

TEST_F(UserPropDecideTest, model_enumeration_through_cb_check_found_model)
{
    const uint32_t nvars = 8;
    auto cls = gen_3sat(nvars, 10, 21);
    const uint32_t expected = count_models(cls, nvars);
    ASSERT_GT(expected, 0U);

    EnumeratingPropagator p;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(nvars);
    for(const auto& cl: cls) { vector<Lit> tmp = cl; s->add_clause_outside(tmp); }
    for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
    p.start(s, nvars);

    must_inter.store(false, std::memory_order_relaxed);
    // Every model is rejected and blocked, so the search ends unsatisfiable.
    EXPECT_EQ(s->solve_with_assumptions(), l_False);
    EXPECT_EQ(p.models.size(), expected);

    // and no model was enumerated twice
    vector<vector<Lit>> seen = p.models;
    std::sort(seen.begin(), seen.end());
    EXPECT_EQ(std::unique(seen.begin(), seen.end()), seen.end());
}

TEST_F(UserPropDecideTest, a_lazy_propagator_is_still_asked_for_clauses)
{
    // Rejecting a model is the only thing a lazy propagator can do, and it is
    // useless unless it can then hand over the clause that says why. The same
    // enumeration as above, with the propagator declared lazy: same answer,
    // same models, and still nothing notified along the way.
    const uint32_t nvars = 8;
    auto cls = gen_3sat(nvars, 10, 21);
    const uint32_t expected = count_models(cls, nvars);
    ASSERT_GT(expected, 0U);

    EnumeratingPropagator p;
    p.is_lazy = true;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(nvars);
    for(const auto& cl: cls) { vector<Lit> tmp = cl; s->add_clause_outside(tmp); }
    for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
    p.start(s, nvars);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_False);
    EXPECT_EQ(p.models.size(), expected);
    EXPECT_EQ(p.max_level_seen, 0U);
    EXPECT_EQ(p.num_backtracks, 0U);
}

TEST_F(UserPropDecideTest, rejecting_without_a_clause_is_taken_as_acceptance)
{
    class AlwaysNo : public MirrorPropagator {
    public:
        uint32_t num_rejections = 0;
        bool cb_check_found_model(const vector<Lit>&) override {
            num_rejections++;
            return false;
        }
    } p;

    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(5);
    s->add_clause_outside(str_to_cl("1, 2"));
    for(uint32_t v = 0; v < 5; v++) s->add_observed_var(v);
    p.start(s, 5);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_EQ(p.num_rejections, 1U);
}

TEST_F(UserPropDecideTest, force_backtrack_from_cb_decide)
{
    BacktrackingPropagator p;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(40);
    auto cls = gen_3sat(40, 120, 13);
    for(const auto& cl: cls) { vector<Lit> tmp = cl; s->add_clause_outside(tmp); }
    for(uint32_t v = 0; v < 40; v++) s->add_observed_var(v);
    p.raw = s;
    p.budget = 25;
    p.start(s, 40);

    must_inter.store(false, std::memory_order_relaxed);
    const lbool ret = s->solve_with_assumptions();
    EXPECT_NE(ret, l_Undef);
    EXPECT_GT(p.num_forced, 0U);
    EXPECT_GT(p.num_backtracks, 0U);
}

TEST_F(UserPropDecideTest, force_backtrack_is_ignored_outside_the_callbacks)
{
    NoopPropagator p;
    SATSolver api;
    api.new_vars(5);
    api.add_clause(str_to_cl("1, 2"));
    api.connect_external_propagator(&p);
    api.add_observed_var(0);
    // Not inside cb_decide()/cb_check_found_model(): must be a no-op, not a crash
    api.force_backtrack(0);
    EXPECT_EQ(api.solve(), l_True);
}

}

////////////////////////////
// WP6: lazy reason clauses
////////////////////////////

namespace CMSat {

struct UserPropLazyTest : public UserPropPropagateTest {};

TEST_F(UserPropLazyTest, lazy_and_eager_agree_over_many_seeds)
{
    size_t eager_explanations = 0;
    size_t eager_propagations = 0;
    size_t lazy_explanations = 0;
    size_t lazy_propagations = 0;

    for(uint32_t seed = 1; seed <= 15; seed++) {
        const uint32_t nvars = 30;
        auto cls = gen_3sat(nvars, 125, seed);
        const lbool expected = solve_plain(cls, nvars);

        for(int lazy = 0; lazy < 2; lazy++) {
            p = UnitPropagator();
            ASSERT_EQ(solve_with_theory(cls, nvars, cls.size()/2, lazy == 1), expected)
                << "seed " << seed << " lazy " << lazy;
            if (expected == l_True) {
                EXPECT_TRUE(model_satisfies(s->get_model(), cls))
                    << "seed " << seed << " lazy " << lazy;
            }
            // an explanation is only ever asked for once per propagation
            EXPECT_LE(p.num_explanations, p.num_propagations);
            if (lazy) {
                lazy_explanations += p.num_explanations;
                lazy_propagations += p.num_propagations;
            } else {
                // eagerly, every propagation is explained straight away
                EXPECT_EQ(p.num_explanations, p.num_propagations);
                eager_explanations += p.num_explanations;
                eager_propagations += p.num_propagations;
            }
        }
    }

    EXPECT_GT(eager_explanations, 0U);
    EXPECT_GT(lazy_propagations, 0U);
    EXPECT_EQ(eager_explanations, eager_propagations);
    // The whole point: most propagations never have to be explained at all.
    EXPECT_LT(lazy_explanations, lazy_propagations);
    EXPECT_LT((double)lazy_explanations/(double)lazy_propagations, 0.9);
}

TEST_F(UserPropLazyTest, lazy_reasons_are_actually_used_in_conflict_analysis)
{
    const uint32_t nvars = 25;
    auto cls = gen_3sat(nvars, 100, 9);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(solve_with_theory(cls, nvars, 0, true), expected);
    // Everything comes from the propagator, so conflict analysis cannot avoid
    // asking for reasons.
    EXPECT_GT(p.num_explanations, 0U);
    EXPECT_LT(p.num_explanations, p.num_propagations);
}

TEST_F(UserPropLazyTest, lazy_is_ignored_under_frat)
{
    // Reason clauses have to be in the proof, so they are asked for eagerly.
    const uint32_t nvars = 24;
    auto cls = gen_3sat(nvars, 180, 5);
    const lbool expected = solve_plain(cls, nvars);
    ASSERT_EQ(expected, l_False);

    const char* fname = "user_prop_test_lazy.frat";
    FILE* f = fopen(fname, "wb");
    ASSERT_NE(f, nullptr);

    conf.ext_lazy_reasons = true;
    delete s;
    s = new Solver(&conf, &must_inter);
    s->add_frat(f);
    s->connect_external_propagator(&p);
    s->new_vars(nvars);
    for(size_t i = 0; i < 90; i++) {
        vector<Lit> tmp = cls[i];
        s->add_clause_outside(tmp);
    }
    for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
    for(size_t i = 90; i < cls.size(); i++) p.theory.push_back(cls[i]);
    p.start_theory(s, nvars);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_False);
    EXPECT_EQ(p.num_explanations, p.num_propagations);
    delete s; s = nullptr;
    fclose(f);
    std::remove(fname);
}

TEST_F(UserPropLazyTest, lazy_reason_in_a_failed_assumption_core)
{
    // Assume 1 and -2 while the propagator knows 1 -> 2. The propagator
    // propagates 2 lazily on the assumption level, so the second assumption is
    // contradicted by a literal whose reason has not been asked for yet, and
    // analyze_final_confl_with_assumptions() has to materialise it.
    conf.ext_lazy_reasons = true;
    delete s;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&p);
    s->new_vars(6);
    s->add_clause_outside(str_to_cl("3, 4"));
    for(uint32_t v = 0; v < 6; v++) s->add_observed_var(v);
    p.theory.push_back(str_to_cl("-1, 2"));
    p.start_theory(s, 6);

    vector<Lit> assumps = {Lit(0, false), Lit(1, true)};
    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(&assumps), l_False);
    EXPECT_GT(p.num_propagations, 0U);
    EXPECT_FALSE(s->conflict.empty());
    // the solver is still usable without those assumptions
    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
}

TEST_F(UserPropLazyTest, lazy_with_non_recursive_clause_minimisation)
{
    // The other minimisation path: normalClMinim() rather than
    // recursiveConfClauseMin(). It reads reasons too.
    conf.doRecursiveMinim = false;
    for(uint32_t seed = 1; seed <= 8; seed++) {
        const uint32_t nvars = 30;
        auto cls = gen_3sat(nvars, 125, seed);
        const lbool expected = solve_plain(cls, nvars);
        p = UnitPropagator();
        conf.doRecursiveMinim = false;
        ASSERT_EQ(solve_with_theory(cls, nvars, cls.size()/2, true), expected)
            << "seed " << seed;
        if (expected == l_True) {
            EXPECT_TRUE(model_satisfies(s->get_model(), cls)) << "seed " << seed;
        }
    }
}

TEST_F(UserPropLazyTest, lazy_with_the_whole_problem_in_the_propagator)
{
    for(uint32_t seed = 1; seed <= 8; seed++) {
        const uint32_t nvars = 22;
        auto cls = gen_3sat(nvars, 92, seed);
        const lbool expected = solve_plain(cls, nvars);
        p = UnitPropagator();
        ASSERT_EQ(solve_with_theory(cls, nvars, 0, true), expected) << "seed " << seed;
        if (expected == l_True) {
            EXPECT_TRUE(model_satisfies(s->get_model(), cls)) << "seed " << seed;
        }
    }
}

// Propagates one literal lazily and then stops observing a variable that is
// fixed at the root and still named by that propagation's reason. Tracks the
// trail itself rather than through MirrorPropagator, which would compare its
// own view against the solver's and rightly complain about the dropped
// variable still sitting in its level-0 prefix.
class DropsAFixedVarPropagator : public ExternalPropagator
{
public:
    Solver* raw = nullptr;
    vector<lbool> value_of;      // indexed by outer var
    vector<vector<Lit>> stack;   // so that backtracking undoes assignments
    vector<Lit> reason;          // OUTER, reason[0] is the literal it explains
    uint32_t drop_var = 0;
    size_t next_lit = 0;
    bool propagated = false;
    uint32_t num_explanations = 0;

    void start(Solver* _raw, uint32_t nvars) {
        raw = _raw;
        value_of.assign(nvars, l_Undef);
        stack.assign(1, {});
    }
    lbool val(const Lit l) const {
        const lbool v = value_of[l.var()];
        if (v == l_Undef) return l_Undef;
        return l.sign() ? (v == l_True ? l_False : l_True) : v;
    }

    void notify_assignment(const vector<Lit>& lits) override {
        for(const Lit l: lits) {
            value_of[l.var()] = l.sign() ? l_False : l_True;
            stack.back().push_back(l);
        }
    }
    void notify_new_decision_level() override { stack.push_back({}); }
    void notify_backtrack(size_t new_level) override {
        for(size_t i = new_level+1; i < stack.size(); i++) {
            for(const Lit l: stack[i]) value_of[l.var()] = l_Undef;
        }
        stack.resize(new_level+1);
    }
    bool cb_check_found_model(const vector<Lit>&) override { return true; }
    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = false;
        return false;
    }
    Lit cb_add_external_clause_lit() override { return lit_Undef; }

    Lit cb_propagate() override {
        if (propagated || val(reason[0]) != l_Undef) return lit_Undef;
        for(size_t i = 1; i < reason.size(); i++) {
            if (val(reason[i]) != l_False) return lit_Undef;
        }
        propagated = true;
        //...and from here on the propagator has no further use for it
        raw->remove_observed_var(drop_var);
        return reason[0];
    }
    Lit cb_add_reason_clause_lit(Lit) override {
        if (next_lit == 0) num_explanations++;
        if (next_lit == reason.size()) { next_lit = 0; return lit_Undef; }
        return reason[next_lit++];
    }
};

TEST_F(UserPropLazyTest, a_lazy_reason_may_name_a_dropped_root_fixed_variable)
{
    // 1 is fixed at the root, and the propagator knows 1 & 2 -> 3. It
    // propagates 3 on the assumption level and drops 1 in the same breath;
    // assuming -3 then forces the reason to be materialised, and it still names
    // the variable nobody observes any more. remove_observed_var() cannot have
    // backtracked over a root assignment, so the reason is not the propagator's
    // fault and must not be treated as one.
    conf.ext_lazy_reasons = true;
    DropsAFixedVarPropagator dp;
    dp.reason = str_to_cl("3, -1, -2", false); // unsorted: reason[0] is what it explains
    dp.drop_var = 0;

    delete s;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&dp);
    s->new_vars(6);
    s->add_clause_outside(str_to_cl("1"));
    s->add_clause_outside(str_to_cl("4, 5"));
    for(uint32_t v = 0; v < 6; v++) s->add_observed_var(v);
    dp.start(s, 6);

    vector<Lit> assumps = {Lit(1, false), Lit(2, true)};
    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(&assumps), l_False);
    EXPECT_TRUE(dp.propagated);
    EXPECT_GT(dp.num_explanations, 0U);
    EXPECT_FALSE(s->is_observed_var(0));
    EXPECT_FALSE(s->conflict.empty());
    // and the solver is still usable without those assumptions
    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
}

// Propagates a literal with a reason it has not checked against the trail --
// the mistake a propagator makes when it works out the reason at the moment it
// is asked instead of recording it when the propagation was made.
class SloppyReasonPropagator : public ExternalPropagator
{
public:
    vector<Lit> reason;      // OUTER, reason[0] is the literal it explains
    uint32_t propagate_at = 1;
    uint32_t level = 0;
    size_t next_lit = 0;
    bool propagated = false;

    void notify_assignment(const vector<Lit>&) override {}
    void notify_new_decision_level() override { level++; }
    void notify_backtrack(size_t new_level) override { level = (uint32_t)new_level; }
    bool cb_check_found_model(const vector<Lit>&) override { return true; }
    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = false;
        return false;
    }
    Lit cb_add_external_clause_lit() override { return lit_Undef; }

    Lit cb_propagate() override {
        if (propagated || level != propagate_at) return lit_Undef;
        propagated = true;
        return reason[0];
    }
    Lit cb_add_reason_clause_lit(Lit) override {
        if (next_lit == reason.size()) { next_lit = 0; return lit_Undef; }
        return reason[next_lit++];
    }
};

// The propagator claims 2 & 4 -> 3, but propagates 3 on the level of 2, before
// 4 has been assigned at all. By the time the reason is asked for, 4 is true --
// so every literal of the clause is falsified as it should be, and the only
// thing wrong with it is that it names an assignment made after the one it
// explains. Left alone, conflict analysis walks off the bottom of the trail.
static void solve_with_a_sloppy_reason(SolverConf& conf)
{
    SloppyReasonPropagator sp;
    sp.reason = str_to_cl("3, -2, -4", false);
    std::atomic<bool> inter;
    inter.store(false, std::memory_order_relaxed);
    Solver solver(&conf, &inter);
    solver.connect_external_propagator(&sp);
    solver.new_vars(6);
    solver.add_clause_outside(str_to_cl("5, 6"));
    for(uint32_t v = 0; v < 6; v++) solver.add_observed_var(v);
    vector<Lit> as = {Lit(1, false), Lit(3, false), Lit(2, true)};
    solver.solve_with_assumptions(&as);
}

TEST_F(UserPropLazyTest, a_reason_naming_a_later_assignment_is_caught)
{
    conf.ext_lazy_reasons = true;
    EXPECT_DEATH(solve_with_a_sloppy_reason(conf),
                 "assigned after the one it explains");
}

}

////////////////////////////
// WP7: everything at once
////////////////////////////

namespace CMSat {

struct UserPropAdversaryTest : public ::testing::Test {
    UserPropAdversaryTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropAdversaryTest() { delete s; delete ref; }

    lbool solve_plain(const vector<vector<Lit>>& cls, uint32_t nvars) {
        delete ref;
        ref = new Solver(&conf, &must_inter);
        ref->new_vars(nvars);
        for(const auto& cl: cls) { vector<Lit> tmp = cl; ref->add_clause_outside(tmp); }
        must_inter.store(false, std::memory_order_relaxed);
        return ref->solve_with_assumptions();
    }

    lbool solve_adversarially(const vector<vector<Lit>>& cls, uint32_t nvars,
                              size_t split, uint32_t seed, bool lazy)
    {
        delete s;
        conf.ext_lazy_reasons = lazy;
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        s->new_vars(nvars);
        for(size_t i = 0; i < split; i++) {
            vector<Lit> tmp = cls[i];
            s->add_clause_outside(tmp);
        }
        // Only some variables are observed to begin with; the propagator asks
        // for the rest while checking a model.
        for(uint32_t v = 0; v < nvars; v++) if ((v + seed) % 3 != 0) s->add_observed_var(v);

        p.theory.clear();
        for(size_t i = split; i < cls.size(); i++) p.theory.push_back(cls[i]);
        p.start_adversary(s, nvars, seed);
        p.backtrack_budget = 40;

        must_inter.store(false, std::memory_order_relaxed);
        return s->solve_with_assumptions();
    }

    SolverConf conf;
    Solver* s = nullptr;
    Solver* ref = nullptr;
    AdversarialPropagator p;
    std::atomic<bool> must_inter;
};

TEST_F(UserPropAdversaryTest, everything_at_once)
{
    size_t total_forced = 0, total_late = 0, total_rejected = 0, total_given = 0;
    for(uint32_t seed = 1; seed <= 25; seed++) {
        const uint32_t nvars = 26;
        auto cls = gen_3sat(nvars, 108, seed);
        const lbool expected = solve_plain(cls, nvars);

        for(int lazy = 0; lazy < 2; lazy++) {
            p = AdversarialPropagator();
            const lbool got = solve_adversarially(cls, nvars, cls.size()*2/3, seed, lazy == 1);
            ASSERT_EQ(got, expected) << "seed " << seed << " lazy " << lazy;
            if (expected == l_True) {
                EXPECT_TRUE(model_satisfies(s->get_model(), cls))
                    << "seed " << seed << " lazy " << lazy;
            }
            total_forced += p.num_forced_backtracks;
            total_late += p.num_late_observes;
            total_rejected += p.num_rejected_models;
            total_given += p.num_clauses_given;
        }
    }
    // make sure the interesting paths were actually taken
    EXPECT_GT(total_forced, 0U);
    EXPECT_GT(total_late, 0U);
    EXPECT_GT(total_given, 0U);
    EXPECT_GT(total_rejected, 0U);
}

TEST_F(UserPropAdversaryTest, everything_at_once_bigger)
{
    for(uint32_t seed = 100; seed <= 106; seed++) {
        const uint32_t nvars = 60;
        auto cls = gen_3sat(nvars, 245, seed);
        const lbool expected = solve_plain(cls, nvars);
        p = AdversarialPropagator();
        ASSERT_EQ(solve_adversarially(cls, nvars, cls.size()/2, seed, seed % 2 == 0), expected)
            << "seed " << seed;
        if (expected == l_True) {
            EXPECT_TRUE(model_satisfies(s->get_model(), cls)) << "seed " << seed;
        }
    }
}

TEST_F(UserPropAdversaryTest, everything_at_once_under_frat)
{
    for(uint32_t seed = 200; seed <= 204; seed++) {
        const uint32_t nvars = 26;
        auto cls = gen_3sat(nvars, 108, seed);
        const lbool expected = solve_plain(cls, nvars);

        const char* fname = "user_prop_adversary.frat";
        FILE* f = fopen(fname, "wb");
        ASSERT_NE(f, nullptr);

        delete s;
        s = new Solver(&conf, &must_inter);
        s->add_frat(f);
        s->connect_external_propagator(&p);
        s->new_vars(nvars);
        const size_t split = cls.size()*2/3;
        for(size_t i = 0; i < split; i++) { vector<Lit> tmp = cls[i]; s->add_clause_outside(tmp); }
        for(uint32_t v = 0; v < nvars; v++) if ((v + seed) % 3 != 0) s->add_observed_var(v);
        p = AdversarialPropagator();
        for(size_t i = split; i < cls.size(); i++) p.theory.push_back(cls[i]);
        p.start_adversary(s, nvars, seed);
        p.backtrack_budget = 40;

        must_inter.store(false, std::memory_order_relaxed);
        EXPECT_EQ(s->solve_with_assumptions(), expected) << "seed " << seed;
        delete s; s = nullptr;
        fclose(f);
        std::remove(fname);
    }
}

TEST_F(UserPropAdversaryTest, everything_at_once_with_assumptions)
{
    for(uint32_t seed = 300; seed <= 308; seed++) {
        // alternate eager and lazy: the failed-assumption path reads reasons
        // too, and with ext_t those have to be materialised there as well
        conf.ext_lazy_reasons = (seed % 2 == 0);
        const uint32_t nvars = 26;
        auto cls = gen_3sat(nvars, 100, seed);

        // A handful of assumptions, the same for both solves.
        vector<Lit> assumps;
        for(uint32_t i = 0; i < 3; i++) assumps.push_back(Lit((seed*7+i) % nvars, (i%2) == 0));

        delete ref;
        ref = new Solver(&conf, &must_inter);
        ref->new_vars(nvars);
        for(const auto& cl: cls) { vector<Lit> tmp = cl; ref->add_clause_outside(tmp); }
        must_inter.store(false, std::memory_order_relaxed);
        const lbool expected = ref->solve_with_assumptions(&assumps);

        delete s;
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        s->new_vars(nvars);
        const size_t split = cls.size()/2;
        for(size_t i = 0; i < split; i++) { vector<Lit> tmp = cls[i]; s->add_clause_outside(tmp); }
        for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
        p = AdversarialPropagator();
        for(size_t i = split; i < cls.size(); i++) p.theory.push_back(cls[i]);
        p.start_adversary(s, nvars, seed);
        p.backtrack_budget = 20;

        must_inter.store(false, std::memory_order_relaxed);
        ASSERT_EQ(s->solve_with_assumptions(&assumps), expected) << "seed " << seed;
    }
}

}

////////////////////////////
// Public API calls that touch the trail outside the search
////////////////////////////

namespace CMSat {

struct UserPropOtherApiTest : public ::testing::Test {
    UserPropOtherApiTest() { must_inter.store(false, std::memory_order_relaxed); }
    ~UserPropOtherApiTest() { delete s; }

    void setup(uint32_t nvars, uint32_t ncls, uint32_t seed) {
        s = new Solver(&conf, &must_inter);
        s->connect_external_propagator(&p);
        add_random_3sat(s, nvars, ncls, seed);
        for(uint32_t v = 0; v < nvars; v++) s->add_observed_var(v);
        p.start(s, nvars);
        must_inter.store(false, std::memory_order_relaxed);
        ASSERT_EQ(s->solve_with_assumptions(), l_True);
        // back at the root: the propagator's stack must be level 0 only
        ASSERT_EQ(p.stack.size(), 1U);
    }

    SolverConf conf;
    Solver* s = nullptr;
    MirrorPropagator p;
    std::atomic<bool> must_inter;
};

// implied_by(), minimize_clause() and probe() all open a decision level of
// their own, outside the search. None of that is the propagator's business.

// Un-observing a variable during the search has to backtrack below its
// assignment, so that no unexplained propagation over it is left behind.
class UnobservingPropagator : public MirrorPropagator
{
public:
    Solver* raw = nullptr;
    uint32_t budget = 0;
    uint32_t next_var = 0;
    uint32_t num_removed = 0;

    Lit cb_decide() override {
        if (budget > 0 && stack.size() > 2) {
            // pick something observed and assigned above the root
            for(uint32_t tries = 0; tries < 32; tries++) {
                const uint32_t v = next_var++ % assigned.size();
                if (!raw->is_observed_var(v) || !assigned[v]) continue;
                budget--;
                num_removed++;
                raw->remove_observed_var(v);
                break;
            }
        }
        return lit_Undef;
    }
};

TEST_F(UserPropOtherApiTest, remove_observed_var_during_solving)
{
    UnobservingPropagator up;
    delete s;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&up);
    add_random_3sat(s, 60, 240, 5);
    for(uint32_t v = 0; v < 60; v++) s->add_observed_var(v);
    up.raw = s;
    up.budget = 25;
    up.start(s, 60);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_NE(s->solve_with_assumptions(), l_Undef);
    EXPECT_GT(up.num_removed, 0U);
    EXPECT_GT(up.num_comparisons, 0U);
}

// Observes or un-observes one particular variable, once, from inside
// cb_decide(). Both calls backtrack when the variable is assigned, so the
// solver must not go on to make a decision on top of what is left.
class LateObservingPropagator : public MirrorPropagator
{
public:
    Solver* raw = nullptr;
    uint32_t var = 0;
    uint32_t at_level = 0;      // act once the search is this deep
    bool observe = true;        // observe, or un-observe
    bool done = false;
    uint32_t level_when_done = 0;

    Lit cb_decide() override {
        if (done || raw->decisionLevel() < at_level) return lit_Undef;
        done = true;
        level_when_done = raw->decisionLevel();
        if (observe) raw->add_observed_var(var);
        else raw->remove_observed_var(var);
        return lit_Undef;
    }
};

TEST_F(UserPropOtherApiTest, observing_a_fixed_variable_from_cb_decide)
{
    // The variable is fixed at the root, so it is handed over as part of the
    // level-0 prefix rather than through the notification cursor. Opening a
    // decision level before that happens would file a permanent assignment
    // under a level that is about to be backtracked over.
    LateObservingPropagator lp;
    delete s;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&lp);
    add_random_3sat(s, 40, 120, 17);
    s->add_clause_outside(str_to_cl("1"));
    for(uint32_t v = 1; v < 40; v++) s->add_observed_var(v);
    lp.raw = s;
    lp.var = 0;
    lp.start(s, 40);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_TRUE(lp.done);
    EXPECT_GT(lp.num_comparisons, 0U);
    // back at the root, and the fixed literal is part of the root prefix
    ASSERT_EQ(lp.stack.size(), 1U);
    EXPECT_NE(std::find(lp.stack[0].begin(), lp.stack[0].end(), Lit(0, false)),
              lp.stack[0].end()) << "the root assignment was notified at the wrong level";
}

// Observes one variable, once, from inside cb_check_found_model().
class ModelTimeObservingPropagator : public MirrorPropagator
{
public:
    Solver* raw = nullptr;
    uint32_t var = 0;
    bool done = false;
    uint32_t num_models = 0;
    bool seen_in_a_later_model = false;

    bool cb_check_found_model(const vector<Lit>& model) override {
        num_models++;
        compare();
        if (!done) {
            done = true;
            raw->add_observed_var(var);
            return true;
        }
        if (std::find(model.begin(), model.end(), Lit(var, false)) != model.end()) {
            seen_in_a_later_model = true;
        }
        return true;
    }
};

TEST_F(UserPropOtherApiTest, observing_a_fixed_variable_from_cb_check_found_model)
{
    // Every variable is forced by a unit clause, so the assignment is complete
    // at the root: observing one more moves neither the trail nor the decision
    // level, and nothing but ext_pending_fixed says a notification is owed. Take
    // the model as final here and the propagator is never told the value of the
    // variable it just asked about.
    ModelTimeObservingPropagator mp;
    delete s;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&mp);
    s->new_vars(8);
    for(uint32_t v = 0; v < 8; v++) {
        vector<Lit> unit = {Lit(v, false)};
        s->add_clause_outside(unit);
    }
    for(uint32_t v = 1; v < 8; v++) s->add_observed_var(v);
    mp.raw = s;
    mp.var = 0;
    mp.start(s, 8);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_TRUE(mp.done);
    EXPECT_GE(mp.num_models, 2U) << "the model was taken as final with a notification owed";
    EXPECT_TRUE(mp.seen_in_a_later_model);
    ASSERT_EQ(mp.stack.size(), 1U);
    EXPECT_NE(std::find(mp.stack[0].begin(), mp.stack[0].end(), Lit(0, false)),
              mp.stack[0].end()) << "the root assignment was never notified";
}

// Observes a variable in the middle of reading an external clause -- the one
// callback that hands over literals one at a time, so the mapping from outer to
// inter numbering can change while the clause is still being built.
class ObservesWhileReadingPropagator : public MirrorPropagator
{
public:
    Solver* raw = nullptr;
    vector<Lit> clause;      // OUTER numbering
    uint32_t observe_var = 0;
    size_t next_lit = 0;
    bool handed = false;
    bool observed_mid_clause = false;

    bool cb_has_external_clause(bool& is_forgettable) override {
        is_forgettable = false;
        return !handed && stack.size() > 2;
    }
    Lit cb_add_external_clause_lit() override {
        if (next_lit == clause.size()) { next_lit = 0; handed = true; return lit_Undef; }
        if (next_lit == 1 && !raw->is_observed_var(observe_var)) {
            raw->add_observed_var(observe_var);
            observed_mid_clause = true;
        }
        return clause[next_lit++];
    }
};

TEST_F(UserPropOtherApiTest, observing_a_variable_while_reading_an_external_clause)
{
    ObservesWhileReadingPropagator op;
    delete s;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&op);
    add_random_3sat(s, 40, 130, 23);
    for(uint32_t v = 0; v < 39; v++) s->add_observed_var(v);
    op.raw = s;
    op.clause = str_to_cl("1, -2, 3");
    op.observe_var = 39;
    op.start(s, 40);

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
    EXPECT_TRUE(op.handed);
    EXPECT_TRUE(op.observed_mid_clause);
    EXPECT_TRUE(s->is_observed_var(39));
    // the clause really did make it in
    const vector<lbool>& m = s->get_model();
    EXPECT_TRUE(m[0] == l_True || m[1] == l_False || m[2] == l_True);
}

// Observing or un-observing an assumption variable backtracks into the
// assumption prefix. new_decision() indexes assumptions[] by decision level,
// so deciding anything else there skips an assumption for good.
static void check_assumptions_survive_cb_decide(SolverConf& conf,
    std::atomic<bool>& must_inter, Solver*& s, bool observe)
{
    const uint32_t nvars = 20;
    const uint32_t num_assumps = 5;

    LateObservingPropagator lp;
    delete s;
    // Decide negatively, so that an assumption that never gets decided is left
    // falsified rather than accidentally satisfied.
    conf.polarity_mode = PolarityMode::polarmode_neg;
    conf.simplify_at_startup = false;
    conf.doVarElim = false;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&lp);
    s->new_vars(nvars);

    // The assumptions are over variables that appear in no clause, so each one
    // is decided, on exactly the level its position in the stack implies.
    // Everything else is satisfiable and deep enough to get past them.
    vector<Lit> assumps;
    for(uint32_t v = 0; v < num_assumps; v++) assumps.push_back(Lit(v, false));
    for(uint32_t i = num_assumps; i + 2 < nvars; i++) {
        s->add_clause_outside(vector<Lit>{Lit(i, false), Lit(i+1, false), Lit(i+2, true)});
        s->add_clause_outside(vector<Lit>{Lit(i, true), Lit(i+1, true), Lit(i+2, false)});
    }

    // Observe everything but the assumption we are about to pick up, or
    // everything including it if we are about to drop it again.
    const uint32_t target = 2;           // the middle assumption
    for(uint32_t v = 0; v < nvars; v++) {
        if (observe && v == target) continue;
        s->add_observed_var(v);
    }
    lp.raw = s;
    lp.var = target;
    lp.at_level = num_assumps + 1;       // past the prefix, so it is complete
    lp.observe = observe;
    lp.start(s, nvars);

    must_inter.store(false, std::memory_order_relaxed);
    ASSERT_EQ(s->solve_with_assumptions(&assumps), l_True);
    ASSERT_TRUE(lp.done) << "cb_decide() never got deep enough to act";
    for(const Lit a: assumps) {
        EXPECT_EQ(s->get_model()[a.var()], a.sign() ? l_False : l_True)
            << "assumption " << a << " is not satisfied by the model";
    }
}

TEST_F(UserPropOtherApiTest, observing_an_assumption_from_cb_decide)
{
    check_assumptions_survive_cb_decide(conf, must_inter, s, true);
}

TEST_F(UserPropOtherApiTest, un_observing_an_assumption_from_cb_decide)
{
    check_assumptions_survive_cb_decide(conf, must_inter, s, false);
}

TEST_F(UserPropOtherApiTest, statistics_are_collected)
{
    // Everything the propagator did should be visible afterwards.
    OraclePropagator op;
    delete s;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&op);
    auto cls = gen_3sat(30, 125, 4);
    s->new_vars(30);
    for(size_t i = 0; i < 60; i++) { vector<Lit> tmp = cls[i]; s->add_clause_outside(tmp); }
    for(uint32_t v = 0; v < 30; v++) s->add_observed_var(v);
    for(size_t i = 60; i < cls.size(); i++) op.to_hand_over.push_back(cls[i]);
    op.start(s, 30);

    EXPECT_TRUE(s->ext_stats.empty());
    must_inter.store(false, std::memory_order_relaxed);
    s->solve_with_assumptions();

    EXPECT_FALSE(s->ext_stats.empty());
    EXPECT_GT(s->ext_stats.cb_calls, 0U);
    EXPECT_GT(s->ext_stats.clause_calls, 0U);
    EXPECT_EQ(s->ext_stats.clauses, cls.size() - 60);
    EXPECT_GT(s->ext_stats.model_checks, 0U);
    // the report itself must run (and survive a zero denominator)
    testing::internal::CaptureStdout();
    s->print_ext_prop_stats();
    const std::string out = testing::internal::GetCapturedStdout();
    EXPECT_NE(out.find("user-prop callbacks"), std::string::npos);
    EXPECT_NE(out.find("user-prop clauses"), std::string::npos);

    // and reconnecting starts a fresh count -- with nothing to report
    s->disconnect_external_propagator();
    s->connect_external_propagator(&op);
    EXPECT_TRUE(s->ext_stats.empty());
    testing::internal::CaptureStdout();
    s->print_ext_prop_stats();
    EXPECT_TRUE(testing::internal::GetCapturedStdout().empty());
}

TEST_F(UserPropOtherApiTest, is_decision_agrees_with_the_trail_under_assumptions)
{
    // A propagator that checks, at every model, that is_decision() says yes for
    // exactly the literals the solver actually decided -- assumptions included,
    // since CaDiCaL counts those as decisions too (Internal::is_decision).
    class Checker : public MirrorPropagator {
    public:
        Solver* raw = nullptr;
        uint32_t num_decisions_seen = 0;
        uint32_t num_checked = 0;
        bool cb_check_found_model(const vector<Lit>& model) override {
            compare();
            num_checked++;
            vector<vector<Lit>> expected;
            if (!raw->ext_get_observed_trail(expected)) return true;
            // the first literal of each level above 0 is that level's decision
            for(size_t lev = 1; lev < expected.size(); lev++) {
                if (expected[lev].empty()) continue;
                EXPECT_TRUE(raw->ext_is_decision(expected[lev][0]))
                    << "level " << lev << " first literal not a decision";
                num_decisions_seen++;
            }
            for(const Lit l: model) {
                // a literal fixed at the root is never a decision
                if (raw->ext_is_decision(l)) {
                    EXPECT_GT(raw->varData[raw->map_outer_to_inter(l.var())].level, 0U);
                }
            }
            return true;
        }
    } chk;

    delete s;
    s = new Solver(&conf, &must_inter);
    s->connect_external_propagator(&chk);
    add_random_3sat(s, 40, 120, 19);
    for(uint32_t v = 0; v < 40; v++) s->add_observed_var(v);
    chk.raw = s;
    chk.start(s, 40);

    vector<Lit> assumps = {Lit(0, false), Lit(3, true), Lit(7, false)};
    must_inter.store(false, std::memory_order_relaxed);
    ASSERT_EQ(s->solve_with_assumptions(&assumps), l_True);
    EXPECT_GT(chk.num_checked, 0U);
    EXPECT_GT(chk.num_decisions_seen, 0U);
    // Once solve() has returned, the solver is back at the root, so nothing is
    // a decision any more -- is_decision() is only meaningful during solving.
    for(const Lit l: assumps) EXPECT_FALSE(s->ext_is_decision(l)) << "assumption " << l;
}

TEST_F(UserPropOtherApiTest, implied_by_does_not_reach_the_propagator)
{
    setup(40, 100, 7);
    vector<Lit> out;
    s->implied_by(str_to_cl("1, 2"), out);
    EXPECT_EQ(p.stack.size(), 1U) << "phantom decision level leaked from implied_by()";

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
}

TEST_F(UserPropOtherApiTest, minimize_clause_does_not_reach_the_propagator)
{
    setup(40, 100, 11);
    vector<Lit> cl = str_to_cl("1, 2, 3");
    s->minimize_clause(cl);
    EXPECT_EQ(p.stack.size(), 1U) << "phantom decision level leaked from minimize_clause()";

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
}

TEST_F(UserPropOtherApiTest, probe_does_not_reach_the_propagator)
{
    setup(40, 100, 13);
    uint32_t min_props = 0;
    for(uint32_t v = 0; v < 10; v++) s->probe_outside(Lit(v, false), min_props);
    EXPECT_EQ(p.stack.size(), 1U) << "phantom decision level leaked from probe()";

    must_inter.store(false, std::memory_order_relaxed);
    EXPECT_EQ(s->solve_with_assumptions(), l_True);
}

}

int main(int argc, char **argv)
{
    ::testing::InitGoogleTest(&argc, argv);
    return RUN_ALL_TESTS();
}
