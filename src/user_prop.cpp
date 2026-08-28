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

    ext_prop = p;
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

    const uint32_t inter_var = map_outer_to_inter(outer_var);
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
            ext_pending_fixed.push_back(Lit(outer_var, value(inter_var) == l_False));
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
