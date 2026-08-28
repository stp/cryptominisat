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

/**
IPASIR-UP support: connecting an external (user) propagator to the CDCL loop.

See "Satisfiability Modulo User Propagators", Fazekas, Niemetz, Preiner,
Kirchweger, Szeider & Biere, JAIR 81 (2024) 989-1017, and user_prop.h for the
interface itself.

This file holds the solver side of that interface. Everything crossing the
boundary is in OUTER numbering (the numbering the public API uses); everything
inside is in INTER numbering.
*/

#include "solver.h"

#include <algorithm>

#include "constants.h"
#include "searcher.h"
#include "occsimplifier.h"
#include "varreplacer.h"

using namespace CMSat;

void Solver::connect_external_propagator(ExternalPropagator* p)
{
    release_assert(p != nullptr && "Use disconnect_external_propagator() to disconnect");
    release_assert(ext_prop == nullptr &&
        "At most one external propagator can be connected at a time");
    release_assert(decisionLevel() == 0 &&
        "An external propagator can only be connected outside of solving");

    release_assert(!fast_backw.fast_backw_on &&
        "An external propagator cannot be combined with fast backward subsumption");

    ext_prop = p;
    //A freshly connected propagator knows nothing, and observes nothing yet:
    //whatever is on the level-0 trail concerns variables it has not asked
    //about. Variables observed later that are already fixed go through
    //ext_pending_fixed.
    ext_notified = trail.size();
    ext_pending_fixed.clear();
    verb_print(1, "[user-prop] external propagator connected");
}

void Solver::disconnect_external_propagator()
{
    if (ext_prop == nullptr) return;
    release_assert(decisionLevel() == 0 &&
        "An external propagator can only be disconnected outside of solving");

    reset_observed_vars();
    ext_prop = nullptr;
    ext_prop_private_steps = false;
    verb_print(1, "[user-prop] external propagator disconnected");
}

void Solver::add_observed_var(const uint32_t outer_var)
{
    release_assert(ext_prop != nullptr &&
        "Cannot observe a variable without a connected external propagator");
    release_assert(outer_var < nVarsOuter() &&
        "Cannot observe a variable that does not exist yet -- call new_vars() first");

    //Renumbering may have moved the variable out of the range the search works
    //on -- Solver::save_on_var_memory() shrinks nVars() past everything that is
    //eliminated, replaced or fixed. Put it back, the same way
    //add_clause_helper() does when a clause mentions such a variable again.
    if (map_outer_to_inter(outer_var) >= nVars()) {
        release_assert(okay());
        cancelUntil(0);
        //An eliminated variable is put back into the branching heap by
        //uneliminate() below, so do not insert it twice.
        const bool insert_varorder =
            varData[map_outer_to_inter(outer_var)].removed == Removed::none;
        new_var(false, outer_var, insert_varorder);
    }

    const uint32_t inter_var = map_outer_to_inter(outer_var);
    release_assert(inter_var < nVars());
    if (varData[inter_var].observed) return;

    //The variable must exist in the search for the propagator to be able to
    //see it. Simplification may have removed it during an earlier solve().
    if (varData[inter_var].removed == Removed::elimed) {
        release_assert(decisionLevel() == 0 &&
            "Cannot un-eliminate a variable during solving -- observe it before solve()");
        release_assert(okay());
        release_assert(occsimplifier != nullptr);
        occsimplifier->uneliminate(inter_var);
    }
    if (varData[inter_var].removed == Removed::replaced) {
        cout << "ERROR: variable " << outer_var+1 << " has been replaced by "
            << varReplacer->get_lit_replaced_with_outer(Lit(outer_var, false))
            << " and can no longer be observed. Observe it before the first"
            " solve(), or call set_no_equivalent_lit_replacement()." << endl;
        release_assert(false);
    }
    release_assert(varData[inter_var].removed == Removed::none);

    varData[inter_var].observed = 1;
    ext_observed_vars.push_back(outer_var);

    //A variable that is already assigned cannot simply be announced: the
    //propagator sees the trail as a stack, and this assignment sits below the
    //top of it. Undo the assignment so that it is made -- and notified -- again
    //in the normal way. Assignments fixed at level 0 are never undone, so those
    //are handed over separately.
    if (value(inter_var) != l_Undef) {
        const uint32_t assigned_at = varData[inter_var].level;
        if (assigned_at > 0) {
            release_assert(assigned_at <= decisionLevel());
            cancelUntil(assigned_at - 1);
        } else {
            cancelUntil(0);
            //Fixed at the root, so it is never undone. If its trail entry is
            //still ahead of the notification cursor the normal pass will pick
            //it up; otherwise -- already passed over, or wiped by renumbering
            //-- it has to be handed over separately.
            const uint32_t sub = varData[inter_var].sublevel;
            const bool cursor_covers_it =
                sub >= ext_notified && sub < trail.size() &&
                trail[sub].lit.var() == inter_var;
            if (!cursor_covers_it) {
                ext_pending_fixed.push_back(Lit(outer_var, value(inter_var) == l_False));
            }
        }
    }
    verb_print(6, "[user-prop] observing outer var " << outer_var+1);
}

void Solver::remove_observed_var(const uint32_t outer_var)
{
    release_assert(outer_var < nVarsOuter());
    const uint32_t inter_var = map_outer_to_inter(outer_var);
    if (!varData[inter_var].observed) return;

    //Only an unassigned variable can be un-observed: otherwise the implication
    //graph may still hold an external propagation over it that we would no
    //longer be able to explain.
    if (value(inter_var) != l_Undef && varData[inter_var].level > 0) {
        cancelUntil(varData[inter_var].level - 1);
    }

    varData[inter_var].observed = 0;
    ext_observed_vars.erase(
        std::remove(ext_observed_vars.begin(), ext_observed_vars.end(), outer_var),
        ext_observed_vars.end());
    verb_print(6, "[user-prop] no longer observing outer var " << outer_var+1);
}

void Solver::reset_observed_vars()
{
    for(const uint32_t outer_var: ext_observed_vars) {
        varData[map_outer_to_inter(outer_var)].observed = 0;
    }
    ext_observed_vars.clear();
    ext_pending_fixed.clear();
}

bool Solver::is_observed_var(const uint32_t outer_var) const
{
    if (outer_var >= nVarsOuter()) return false;
    return varData[map_outer_to_inter(outer_var)].observed;
}

bool Solver::ext_get_observed_trail(vector<vector<Lit>>& out) const
{
    out.clear();
    out.resize(decisionLevel() + 1);

    //Level 0 is rebuilt from the assignments rather than from the trail:
    //PropEngine::updateVars() keeps only the *length* of the trail across
    //renumbering, and the order within the root prefix carries no meaning
    //anyway. Sorted, so that both sides can agree on a canonical order.
    for(const uint32_t outer_var: ext_observed_vars) {
        const uint32_t v = map_outer_to_inter(outer_var);
        if (value(v) == l_Undef || varData[v].level != 0) continue;
        out[0].push_back(Lit(outer_var, value(v) == l_False));
    }
    std::sort(out[0].begin(), out[0].end());

    for(const auto& t: trail) {
        if (t.lev == 0 || t.lit == lit_Undef) continue;
        if (!varData[t.lit.var()].observed) continue;
        assert(t.lev < out.size());
        out[t.lev].push_back(map_inter_to_outer(t.lit));
    }
    return ext_notified == trail.size() && ext_pending_fixed.empty();
}

bool Solver::ext_is_decision(const Lit outer_lit) const
{
    release_assert(outer_lit.var() < nVarsOuter());
    const uint32_t v = map_outer_to_inter(outer_lit.var());
    if (value(v) == l_Undef) return false;
    return varData[v].level > 0 && varData[v].reason == PropBy();
}

void Solver::ext_force_backtrack(const uint32_t new_level)
{
    if (!ext_forced_backtrack_allowed) {
        verb_print(2, "[user-prop] force_backtrack() outside of cb_decide()/"
            "cb_check_found_model(), ignoring");
        return;
    }
    if (new_level >= decisionLevel()) {
        verb_print(2, "[user-prop] force_backtrack(" << new_level << ") is not below the "
            "current decision level " << decisionLevel() << ", ignoring");
        return;
    }
    ext_forced_backtrack_set = true;
    ext_forced_backtrack_level = new_level;
}

void Solver::ext_phase(const Lit outer_lit)
{
    release_assert(outer_lit.var() < nVarsOuter());
    auto& vd = varData[map_outer_to_inter(outer_lit.var())];
    vd.forced_polarity_set = 1;
    vd.forced_polarity = !outer_lit.sign();
}

void Solver::ext_unphase(const uint32_t outer_var)
{
    release_assert(outer_var < nVarsOuter());
    varData[map_outer_to_inter(outer_var)].forced_polarity_set = 0;
}

////////////////////////////
// Adding external clauses during the CDCL loop
//
// Algorithm 3 of the paper. The solver may be at any decision level, so a
// clause that propagates or conflicts has to be woven into the trail. Rather
// than repairing assignment levels in place, as CaDiCaL does, we backtrack:
// once the two watch literals are picked, backtracking to the level of the
// second watch puts the clause in exactly one of three states -- satisfied,
// propagating, or conflicting -- and leaves the watch invariant intact.
////////////////////////////

namespace {
//Watch quality of a literal, higher is better: a satisfied clause is easiest,
//then a literal that is still free, and finally falsified ones -- of which the
//one falsified last (highest level) is the best watch.
inline uint64_t ext_watch_rank(const lbool val, const uint32_t level)
{
    if (val == l_True)  return (3ULL << 32);
    if (val == l_Undef) return (2ULL << 32);
    return (1ULL << 32) | level;
}
}

PropBy Searcher::ext_attach_clause(const int32_t ID, const bool red)
{
    assert(ext_cl.size() >= 2);
    if (ext_cl.size() == 2) {
        solver->attach_bin_clause(ext_cl[0], ext_cl[1], red, ID, false);
        return PropBy(ext_cl[1], red, ID);
    }

    Clause* cl = cl_alloc.Clause_new(ext_cl, sumConflicts, ID);
    cl->isRed = red;
    cl->stats.id = ID;
    cl->stats.glue = std::min<uint32_t>(ext_cl.size(), numeric_limits<uint32_t>::max());
    cl->stats.last_touched_any = sumConflicts;
    if (red) {
        //Forgettable: goes into the tier that clause database reduction looks
        //at, so the solver is free to throw it away again.
        cl->stats.which_red_array = 2;
        #if defined(STATS_NEEDED) || defined(FINAL_PREDICTOR)
        red_stats_extra.push_back(ClauseStatsExtra());
        cl->stats.extra_pos = red_stats_extra.size()-1;
        auto& ext_stats = red_stats_extra[cl->stats.extra_pos];
        ext_stats.introduced_at_conflict = sumConflicts;
        ext_stats.orig_glue = cl->stats.glue;
        ext_stats.orig_size = cl->size();
        #endif
    }

    const ClOffset offset = cl_alloc.get_offset(cl);
    if (red) longRedCls[2].push_back(offset);
    else longIrredCls.push_back(offset);
    solver->attachClause(*cl, false);
    return PropBy(offset);
}

PropBy Searcher::add_external_clause(const bool forgettable_in, const Lit reason_for)
{
    assert(ext_prop != nullptr);
    assert(okay());
    frat_func_start();

    //Forgettable clauses are redundant, and CryptoMiniSat cannot currently put
    //a redundant input clause into a FRAT proof (see Solver::add_clause_outer).
    //Keeping a clause is always sound, so fall back to that.
    const bool forgettable = forgettable_in && !frat->enabled();

    //////////
    // Read it, literal by literal
    //////////
    ext_cl_outer.clear();
    ext_cl.clear();
    bool saw_reason_lit = false;
    Lit l = (reason_for == lit_Undef)
        ? ext_prop->cb_add_external_clause_lit()
        : ext_prop->cb_add_reason_clause_lit(reason_for);
    while (l != lit_Undef) {
        release_assert(l.var() < nVarsOuter() &&
            "external clause over a variable that does not exist");
        const Lit inter = map_outer_to_inter(l);
        release_assert(varData[inter.var()].observed &&
            "external clauses must only mention observed variables");
        if (l == reason_for) saw_reason_lit = true;
        ext_cl_outer.push_back(l);
        ext_cl.push_back(inter);
        l = (reason_for == lit_Undef)
            ? ext_prop->cb_add_external_clause_lit()
            : ext_prop->cb_add_reason_clause_lit(reason_for);
    }
    release_assert((reason_for == lit_Undef || saw_reason_lit) &&
        "the reason clause of an external propagation must contain the propagated literal");

    //////////
    // Clean it. Only *root* assignments may be used: a literal falsified on the
    // current decision level is still part of the clause.
    //////////
    std::sort(ext_cl.begin(), ext_cl.end());
    Lit prev = lit_Undef;
    bool root_satisfied = false;
    uint32_t j = 0;
    for(uint32_t i = 0; i < ext_cl.size(); i++) {
        const Lit q = ext_cl[i];
        if (q == prev) continue;                              // duplicate
        if (q == ~prev) { root_satisfied = true; break; }     // tautology
        prev = q;
        if (value(q) != l_Undef && varData[q.var()].level == 0) {
            if (value(q) == l_True) { root_satisfied = true; break; }
            continue;                                         // root-falsified
        }
        ext_cl[j++] = q;
    }
    if (root_satisfied) {
        verb_print(6, "[user-prop] external clause is root-satisfied, ignoring");
        frat_func_end();
        return PropBy();
    }
    ext_cl.resize(j);

    //////////
    // Record it in the proof. An external clause is an input clause that
    // happens to arrive during the derivation (see JAIR 81, section 3.6).
    //////////
    int32_t ID = ++clauseID;
    if (frat->enabled()) {
        *frat << "external clause\n" << origcl << ID << ext_cl_outer << fin;
        const int32_t cleaned_ID = ++clauseID;
        *frat << add << cleaned_ID << ext_cl << fin;
        *frat << del << ID << ext_cl_outer << fin;
        ID = cleaned_ID;
    }

    //////////
    // The empty clause: we are done.
    //////////
    if (ext_cl.empty()) {
        verb_print(2, "[user-prop] external propagator gave the empty clause");
        set_unsat_cl_id(ID);
        ok = false;
        frat_func_end();
        return PropBy();
    }

    //////////
    // A unit: it holds at the root, so go back there and enqueue it.
    //////////
    if (ext_cl.size() == 1) {
        cancelUntil(0);
        //Cleaning above dropped every root-assigned literal, so after
        //backtracking to the root this one must be free.
        assert(value(ext_cl[0]) == l_Undef);
        enqueue<false>(ext_cl[0], 0, PropBy());
        if (frat->enabled()) *frat << del << ID << ext_cl[0] << fin;
        frat_func_end();
        return PropBy();
    }

    //////////
    // Pick the two watches, then backtrack so that the clause is either
    // satisfied, propagating, or conflicting -- and correctly watched.
    //////////
    std::sort(ext_cl.begin(), ext_cl.end(), [&](const Lit a, const Lit b) {
        return ext_watch_rank(value(a), varData[a.var()].level) >
               ext_watch_rank(value(b), varData[b.var()].level);
    });

    if (value(ext_cl[1]) == l_False) {
        //Every literal but the first is falsified, the last of them on level
        //'blevel'. Undoing everything above it makes the clause propagate on
        //the level where it should have propagated all along.
        const uint32_t blevel = varData[ext_cl[1].var()].level;
        if (blevel < decisionLevel()) cancelUntil(blevel);
        assert(value(ext_cl[1]) == l_False);
    }

    const PropBy by = ext_attach_clause(ID, forgettable);

    if (value(ext_cl[1]) != l_False) {
        //Two literals are still free (or one of them satisfies the clause):
        //nothing follows from it yet.
        frat_func_end();
        return PropBy();
    }
    if (value(ext_cl[0]) == l_Undef) {
        VERBOSE_PRINT("[user-prop] external clause propagates " << ext_cl[0]);
        enqueue<false>(ext_cl[0], decisionLevel(), by);
        frat_func_end();
        return PropBy();
    }
    if (value(ext_cl[0]) == l_False) {
        VERBOSE_PRINT("[user-prop] external clause is falsified -> conflict");
        //Both watches are falsified on the current level: a normal conflict.
        assert(varData[ext_cl[0].var()].level == decisionLevel());
        if (ext_cl.size() == 2) failBinLit = ext_cl[0];
        frat_func_end();
        return by;
    }
    //Satisfied by its first literal, which after the backtrack above is
    //assigned no later than the second one. Nothing to do.
    frat_func_end();
    return PropBy();
}

/**
Algorithms 2 and 3 of the paper, run whenever unit propagation has reached a
fixed point: first ask the propagator for literals it can imply, then for
clauses it wants to add. Either may change the trail, so each round ends with
propagation and a fresh notification, and adding a clause earns the propagator
another turn.

Propagated literals are explained eagerly: the reason clause is asked for
straight away and added like any other external clause, which is exactly what
makes the literal end up on the trail (or produces the conflict). Conflict
analysis therefore needs to know nothing about external propagation.
*/
PropBy Searcher::external_propagate()
{
    assert(ext_prop != nullptr);
    //A lazy propagator only ever looks at complete assignments.
    if (ext_prop->is_lazy || ext_prop_private_steps) return PropBy();

    PropBy confl;
    bool another_round = true;
    while (another_round && confl.isnullptr() && okay()) {
        another_round = false;

        //////////
        // Algorithm 2: literals implied by the propagator
        //////////
        notify_assignments();
        Lit elit = ext_prop->cb_propagate();
        while (elit != lit_Undef) {
            release_assert(elit.var() < nVarsOuter() &&
                "external propagation of a variable that does not exist");
            const Lit ilit = map_outer_to_inter(elit);
            release_assert(varData[ilit.var()].observed &&
                "external propagation is only allowed over observed variables");

            //An already satisfied literal is simply ignored. Otherwise the
            //reason clause both explains and performs the propagation: it
            //propagates a free literal and conflicts on a falsified one.
            if (value(ilit) != l_True) {
                VERBOSE_PRINT("[user-prop] external propagation of " << ilit
                    << " (value " << value(ilit) << ")");
                confl = add_external_clause(ext_prop->are_reasons_forgettable, elit);
                if (!okay()) return PropBy();
                if (!confl.isnullptr()) break;

                release_assert(value(ilit) != l_Undef &&
                    "the reason clause of an external propagation must imply it"
                    " under the current trail");

                if (qhead != trail.size()) {
                    confl = propagate<false>();
                    if (!confl.isnullptr()) break;
                }
                notify_assignments();
            }
            elit = ext_prop->cb_propagate();
        }
        if (!confl.isnullptr() || !okay()) break;

        //////////
        // Algorithm 3: clauses the propagator wants to add
        //////////
        notify_assignments();
        bool forgettable = false;
        while (ext_prop->cb_has_external_clause(forgettable)) {
            confl = add_external_clause(forgettable);
            forgettable = false;
            if (!okay()) return PropBy();
            if (!confl.isnullptr()) break;

            if (qhead != trail.size()) {
                confl = propagate<false>();
                if (!confl.isnullptr()) break;
            }
            notify_assignments();
            //The trail moved, so the propagator may have more to say now.
            another_round = true;
        }
    }
    return confl;
}

////////////////////////////
// Decisions and solution analysis
////////////////////////////

void Searcher::apply_ext_forced_backtrack()
{
    assert(ext_forced_backtrack_set);
    ext_forced_backtrack_set = false;
    if (ext_forced_backtrack_level < decisionLevel()) {
        verb_print(6, "[user-prop] forced backtrack to level " << ext_forced_backtrack_level);
        cancelUntil(ext_forced_backtrack_level);
    }
}

/**
Algorithm 4 of the paper. Only reached once every assumption is satisfied --
the caller has already walked the assumption stack -- so the propagator can
never be asked to decide while an assumption is still open.
*/
Lit Searcher::ext_decide()
{
    assert(ext_prop != nullptr);
    if (ext_prop->is_lazy || ext_prop_private_steps) return lit_Undef;

    notify_assignments();
    ext_forced_backtrack_allowed = true;
    const Lit elit = ext_prop->cb_decide();
    ext_forced_backtrack_allowed = false;
    if (elit == lit_Undef) return lit_Undef;

    release_assert(elit.var() < nVarsOuter() &&
        "external decision over a variable that does not exist");
    const Lit ilit = map_outer_to_inter(elit);
    release_assert(varData[ilit.var()].observed &&
        "external decisions are only allowed over observed variables");

    //An already assigned literal is no decision at all; fall back on the
    //solver's own heuristic.
    if (value(ilit) != l_Undef) return lit_Undef;
    return ilit;
}

/**
Solution analysis: a complete assignment has been found, and the propagator gets
to say whether it is consistent with whatever it knows.

If it is not, the propagator is expected to hand over clauses, or to have forced
a backtrack. Rejecting a model without doing either leaves nothing to act on, so
it is taken as acceptance -- the same way CaDiCaL treats it.
*/
lbool Searcher::external_check_solution()
{
    assert(ext_prop != nullptr);
    if (ext_prop_private_steps) return l_True;

    notify_assignments();

    //One literal per observed variable, in the order they were observed.
    ext_model.clear();
    for(const uint32_t outer_var: ext_observed_vars) {
        const uint32_t v = map_outer_to_inter(outer_var);
        release_assert(value(v) != l_Undef &&
            "an observed variable is unassigned in a complete assignment");
        ext_model.push_back(Lit(outer_var, value(v) == l_False));
    }

    ext_forced_backtrack_allowed = true;
    const bool consistent = ext_prop->cb_check_found_model(ext_model);
    ext_forced_backtrack_allowed = false;

    if (ext_forced_backtrack_set) {
        apply_ext_forced_backtrack();
        return l_Undef;
    }
    if (consistent) return l_True;

    //Rejected: take whatever the propagator has to say about it.
    bool any_clause = false;
    bool forgettable = false;
    while (ext_prop->cb_has_external_clause(forgettable)) {
        any_clause = true;
        ext_confl = add_external_clause(forgettable);
        forgettable = false;
        if (!okay()) return l_False;
        if (!ext_confl.isnullptr()) return l_Undef;

        if (qhead != trail.size()) {
            ext_confl = propagate<false>();
            if (!ext_confl.isnullptr()) return l_Undef;
        }
        notify_assignments();
    }

    if (!any_clause) {
        verb_print(2, "[user-prop] the model was rejected but nothing was added,"
            " treating it as accepted");
        return l_True;
    }
    //The assignment is very likely no longer complete: back to the search.
    return l_Undef;
}
