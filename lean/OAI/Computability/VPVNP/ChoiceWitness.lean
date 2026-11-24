import OAI.Computability.VPVNP.UniversalMachine
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Canonical accepting-path witnesses

For the counting polynomial in §1.1 of *VP and VNP differ over every field*, we use
one Boolean choice for every machine step. This is the combinatorial counting identity
that lets the VNP summand verify one candidate path deterministically.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalMachine

/-- One choice bit per step. A single transition consumes zero, and an early halt
accepts only the all-zero unused suffix. The two instructions in a branch have
separate bits even when they induce the same successor configuration. -/
def acceptsChoices (p : Program) : (t : ℕ) → Config p.extra → (Fin t → Bool) → Bool
  | 0, c, _ => decide (c.state.val = 1)
  | t + 1, c, w =>
    if c.state.val = 1 then decide (w = fun _ => false) else if c.state.val = 0 then false else
      match branches p c with
      | .stop => false
      | .one a => !w 0 && acceptsChoices p t (advance c a) (Fin.tail w)
      | .two a b => acceptsChoices p t (advance c (if w 0 then b else a)) (Fin.tail w)

/-- Enter rejection without further tape operations. -/
def reject {extra : ℕ} (c : Config extra) : Config extra := { c with state := 0 }

/-- Consume a single witness bit. Invalid choices enter the rejecting state, which is
absorbing. An accepting halt survives precisely the zero padding of a canonical witness. -/
def choiceStep (p : Program) (c : Config p.extra) (bit : Bool) : Config p.extra :=
  if c.state.val = 1 then if bit then reject c else c
  else if c.state.val = 0 then c
  else match branches p c with
    | .stop => reject c
    | .one a => if bit then reject c else advance c a
    | .two a b => advance c (if bit then b else a)

private theorem acceptsChoices_of_accept (p : Program) (t : ℕ) (c : Config p.extra)
    (ha : c.state.val = 1) (w : Fin t → Bool) :
    acceptsChoices p t c w = decide (w = fun _ => false) := by
  cases t with
  | zero => simp [acceptsChoices, ha, Subsingleton.elim w (fun _ => false)]
  | succ t => simp [acceptsChoices, ha]

private theorem acceptsChoices_of_reject (p : Program) (t : ℕ) (c : Config p.extra)
    (hr : c.state.val = 0) (w : Fin t → Bool) : acceptsChoices p t c w = false := by
  cases t <;> simp [acceptsChoices, hr]

private theorem all_zero_succ {t : ℕ} (w : Fin (t + 1) → Bool) :
    (w = fun _ => false) ↔ w 0 = false ∧ Fin.tail w = fun _ => false := by
  constructor
  · rintro rfl
    exact ⟨rfl, rfl⟩
  · rintro ⟨h₀, ht⟩
    funext i
    refine Fin.cases h₀ (fun j => ?_) i
    exact congrFun ht j

/-- Consuming the leading bit agrees with one deterministic machine transition. -/
theorem acceptsChoices_succ (p : Program) (t : ℕ) (c : Config p.extra) (w : Fin (t + 1) → Bool) :
    acceptsChoices p (t + 1) c w = acceptsChoices p t (choiceStep p c (w 0)) (Fin.tail w) := by
  have reject_bit := acceptsChoices_of_reject p t (reject c) rfl (Fin.tail w)
  by_cases ha : c.state.val = 1
  · cases hb : w 0 <;>
      simp [acceptsChoices, choiceStep, ha, hb, all_zero_succ, acceptsChoices_of_accept p t c ha,
        reject_bit]
  by_cases hr : c.state.val = 0
  · simp [acceptsChoices, choiceStep, hr, acceptsChoices_of_reject p t c hr]
  cases h : branches p c with
  | stop => simp [acceptsChoices, choiceStep, ha, hr, h, reject_bit]
  | one a => cases hb : w 0 <;> simp [acceptsChoices, choiceStep, ha, hr, h, hb, reject_bit]
  | two a b => simp [acceptsChoices, choiceStep, ha, hr, h]

/-- The final state of the fixed-length simulation determines the verifier's answer. -/
theorem acceptsChoices_eq_foldl (p : Program) (t : ℕ) (c : Config p.extra) (w : Fin t → Bool) :
    acceptsChoices p t c w = decide (((List.ofFn w).foldl (choiceStep p) c).state.val = 1) := by
  induction t generalizing c with
  | zero => simp [acceptsChoices]
  | succ t ih =>
    rw [acceptsChoices_succ, List.ofFn_succ, List.foldl_cons]
    exact ih _ _

private theorem sum_choice_succ {t : ℕ} (f : (Fin (t + 1) → Bool) → ℕ) :
    ∑ w, f w = (∑ v, f (Fin.cons false v)) + ∑ v, f (Fin.cons true v) := by
  rw [← (Fin.consEquiv (fun _ : Fin (t + 1) => Bool)).sum_comp f,
    Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  rfl

/-- Counting accepting strings of fixed length recovers the number of accepting paths
of the encoded machine within the step bound, with each halted path counted once. -/
theorem paths_eq_sum_choices (p : Program) (t : ℕ) (c : Config p.extra) :
    paths p t c = ∑ w, if acceptsChoices p t c w then 1 else 0 := by
  induction t generalizing c with
  | zero => simp [paths, acceptsChoices]
  | succ t ih =>
    rw [paths]
    by_cases ha : c.state.val = 1
    · simp [ha, acceptsChoices]
    by_cases hr : c.state.val = 0
    · simp [hr, acceptsChoices]
    simp only [ha, hr, ite_false]
    cases h : branches p c with
    | stop => simp [ha, hr, h, acceptsChoices]
    | one a => rw [sum_choice_succ]; simp [acceptsChoices, ha, hr, h, ih]
    | two a b => rw [sum_choice_succ]; simp [acceptsChoices, ha, hr, h, ih]

/-- The cardinality form of the fixed-length witness identity. -/
theorem paths_eq_card_choices (p : Program) (t : ℕ) (c : Config p.extra) :
    paths p t c = (Finset.univ.filter (fun w => acceptsChoices p t c w)).card := by
  rw [paths_eq_sum_choices]
  simpa only [Nat.cast_id] using
    (Finset.sum_boole (R := ℕ) (fun w => acceptsChoices p t c w = true) Finset.univ)

end UniversalMachine

section

open UniversalMachine

/-- A candidate for the coefficient indexed by `x` consists of one bit per clock tick. -/
def verifiesInput {n : ℕ} (x : Fin n → Bool) (w : Fin (n ^ clockExponent) → Bool) : Bool :=
  let input := List.ofFn x
  match decode input with
  | none => false
  | some p => acceptsChoices p (n ^ clockExponent) (initial p input) w

/-- The number of canonical witnesses is the coefficient `U_n(x)` from equation (1.1). -/
theorem acceptingCount_eq_card_witnesses {n : ℕ} (x : Fin n → Bool) :
    acceptingCount x = (Finset.univ.filter (fun w => verifiesInput x w)).card := by
  cases h : decode (List.ofFn x) with
  | none => simp [acceptingCount, verifiesInput, h]
  | some p => simp [acceptingCount, verifiesInput, h, paths_eq_card_choices]

/-- The Boolean witness sum gives the same coefficient in every target semiring. -/
theorem acceptingCount_eq_sum_witnesses {R : Type*} [Semiring R] {n : ℕ}
    (x : Fin n → Bool) :
    (acceptingCount x : R) = ∑ w, if verifiesInput x w then 1 else 0 := by
  rw [acceptingCount_eq_card_witnesses]
  exact Finset.natCast_card_filter _ _

end

end VPVNP
end Computability
end OAI
