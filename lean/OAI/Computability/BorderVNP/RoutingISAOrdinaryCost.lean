import OAI.Computability.BorderVNP.RoutingISADeterministic
import OAI.Computability.BorderVNP.RoutingISANatural

/-! # Tick counts of deterministic ordinary assembly -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- A deterministic fragment has no private burst charge, so its logical
tick cost is exactly its event count. -/
theorem Runs.deterministic_cost {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (r : Runs pub macros c s m es t mt) (hc : c.deterministic = true) :
    traceCost es = es.length := by
  induction r with
  | @atom c s m a t z bits atomic action _ =>
    suffices h : a.extra = 0 by simp [traceCost,VPVNP.RAMBuckets.cost,h]
    cases c <;> try {simp [Code.isAtom,Code.deterministic] at atomic hc}
    all_goals try {simp [Code.atom,TeamRAM.Instr.action] at action; subst a; rfl}
    case binary op d x y =>
      simp only [Code.atom] at action
      split at action
      · contradiction
      · cases action; rfl
  | seq _ _ ih ih' =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp hc
    simp only [traceCost,VPVNP.RAMBuckets.cost_append,List.length_append]
    exact congrArg₂ (·+·) (ih hl) (ih' hr)
  | ifEq _ ih | ifLt _ ih =>
    obtain ⟨hl,hr⟩ := Bool.and_eq_true_iff.mp hc
    have h := ih (by split <;> assumption)
    change 1+traceCost _ = _+1
    omega
  | choose => contradiction
  | whileDone => rfl
  | whileStep _ _ _ ih ih' =>
    have a := ih hc
    have b := ih' hc
    simp only [traceCost,VPVNP.RAMBuckets.cost,VPVNP.RAMBuckets.cost_append,tick,
      TeamTranscript.Action.extra,List.length_cons,List.length_append] at a b ⊢
    omega

/-- An ordinary deterministic native fragment incurs no burst charge at any event. -/
theorem Runs.deterministic_extra {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m es t mt} (r : Runs pub macros c s m es t mt) (hc : c.deterministic = true)
    (e : TeamRAM.Event w) (he : e ∈ es) : e.action.extra = 0 := by
  have eq := r.deterministic_cost hc
  rw [traceCost,VPVNP.RAMBuckets.cost_eq_length_add_probes] at eq
  suffices bound : e.action.extra ≤ VPVNP.RAMBuckets.probeCount (fun z => z.action.extra) es by omega
  clear r eq
  induction es with
  | nil => simp at he
  | cons a es ih =>
    rcases List.mem_cons.mp he with rfl | he
    · exact Nat.le_add_right ..
    · exact (ih he).trans (Nat.le_add_left ..)

end RoutingISA

end BorderVNP
end Computability
end OAI
