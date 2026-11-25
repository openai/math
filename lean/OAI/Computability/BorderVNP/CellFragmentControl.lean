import OAI.Computability.BorderVNP.CellFragments

/-! # Branching, private allocation, and record loops for sparse generator programs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator.Fragment

open VPVNP.RAMTape

variable {K T : Type} [DecidableEq K] [DecidableEq T] [Fintype T]

/-- Hide a set of named work registers at a fragment boundary. -/
def hide (r : Fragment (K ⊕ T)) : Fragment K where
  Scratch := T ⊕ r.Scratch
  body := r.body.onPorts (Equiv.sumAssoc ..)

/-- Clean auxiliary registers on both ends of a call permit hiding them from its caller. -/
theorem runs_hide {r : Fragment (K ⊕ T)} {t : ℕ} {s u : Stacks K}
    (h : r.Runs t (Sum.elim s (fun _ => [])) (Sum.elim u (fun _ => []))) :
    r.hide.Runs t s u := by
  apply r.body.runs_onPorts_framed (Equiv.sumAssoc ..).injective h
  · rintro ((k|j)|z) <;> rfl
  · rintro ((k|j)|z) <;> rfl
  · intro p hp; exact (hp ((Equiv.sumAssoc ..).symm p) ((Equiv.sumAssoc ..).apply_symm_apply p)).elim

/-- Pop a row tag and dispatch to the selected fragment. Missing tags reject. -/
def select (k : K) (lo hi : Fragment K) : Fragment K where
  Scratch := lo.Scratch ⊕ hi.Scratch
  body := .ofRoutine (Routine.popCase (.inl k) (Routine.halt false)
    (lo.body.onPorts (Sum.map id Sum.inl)).body (hi.body.onPorts (Sum.map id Sum.inr)).body)

private theorem bank_pop (r : Fragment K) (s : Stacks K) (k : K) (v : List Bool) :
    Function.update (r.bank s) (.inl k) v = r.bank (Function.update s k v) := by
  funext i
  rcases i with l | z
  · by_cases h : l = k <;> simp [bank, h]
  · simp [bank]

/-- A zero tag selects only the low branch, preserving the caller's other registers. -/
theorem runs_select_false {k : K} {lo hi : Fragment K} {s u : Stacks K} {v : List Bool} {t : ℕ}
    (hs : s k = false :: v) (h : lo.Runs t (Function.update s k v) u) :
    (select k lo hi).Runs (t+1) s u := by
  apply Routine.runs_popCase_false (s := (select k lo hi).bank s) (tail := v) (Sum.inl k : K ⊕ (lo.Scratch ⊕ hi.Scratch)) _ _ _
    (show (select k lo hi).bank s (Sum.inl k) = _ from hs)
  erw [bank_pop (select k lo hi) s k v]
  apply lo.body.runs_onPorts_framed (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩) h
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · intro i hn; cases i with | inl j => exact (hn (.inl j) rfl).elim | inr _ => rfl

/-- A one tag selects only the high branch. -/
theorem runs_select_true {k : K} {lo hi : Fragment K} {s u : Stacks K} {v : List Bool} {t : ℕ}
    (hs : s k = true :: v) (h : hi.Runs t (Function.update s k v) u) :
    (select k lo hi).Runs (t+1) s u := by
  apply Routine.runs_popCase_true (s := (select k lo hi).bank s) (tail := v) (Sum.inl k : K ⊕ (lo.Scratch ⊕ hi.Scratch)) _ _ _
    (show (select k lo hi).bank s (Sum.inl k) = _ from hs)
  erw [bank_pop (select k lo hi) s k v]
  apply hi.body.runs_onPorts_framed (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inr_injective⟩) h
  · intro i; cases i <;> rfl
  · intro i; cases i <;> rfl
  · intro i hn; cases i with | inl j => exact (hn (.inl j) rfl).elim | inr _ => rfl

/-- Consume a one marker before each body invocation, ending on an empty stream. -/
def each (k : K) (r : Fragment K) : Fragment K where
  Scratch := r.Scratch
  body := .ofRoutine (Routine.popLoop (.inl k) (fun _ => true) (.halt false) r.body.body)

/-- An exhausted input has one terminating pop. -/
theorem each_empty (k : K) (r : Fragment K) (s : Stacks K) (hs : s k = []) :
    (each k r).Runs 1 s s :=
  Routine.Runs.popLoop_empty (s := r.bank s) (Sum.inl k : K ⊕ r.Scratch) (fun _ => true) (Routine.halt false) r.body.body
    (show r.bank s (Sum.inl k) = _ from hs)

/-- The next marked iteration costs exactly one additional pop. -/
theorem each_cons {k : K} {r : Fragment K} {s u v : Stacks K} {rest : List Bool} {t d : ℕ}
    (hs : s k = true :: rest) (hr : r.Runs t (Function.update s k rest) u)
    (hnext : (each k r).Runs d u v) : (each k r).Runs (1+t+d) s v := by
  apply Routine.Runs.popLoop_true_continue (s := r.bank s) (mid := r.bank u) (Sum.inl k : K ⊕ r.Scratch) (fun _ => true) (Routine.halt false) r.body.body
    (show r.bank s (Sum.inl k) = true :: rest from hs) rfl _ hnext
  erw [bank_pop r s k rest]
  exact hr

end CellMacro.Generator.Fragment

end BorderVNP
end Computability
end OAI
