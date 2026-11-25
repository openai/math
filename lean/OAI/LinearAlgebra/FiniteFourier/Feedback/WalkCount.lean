import OAI.LinearAlgebra.FiniteFourier.Feedback
import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Short-walk supports in a binary feedback system

All tensor slots share one delay variable. A first slot that has reached an input
fixes its column label and disappears without consuming a bit. Visiting a state
consumes one bit and selects one of two predecessors. Induction on total degree
and number of slots therefore counts endpoints without encoding the individual
walk lengths, even when the state graph has cycles.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open scoped BigOperators Classical

namespace Feedback

noncomputable section

open PowerSeries

variable {K I O : Type*} [Field K] {s : ℕ} (F : Feedback K I O s)

/-- Coefficient of the signal on a wire, with one delay charged at every state. -/
def signalCoeff : ℕ → I ⊕ Fin s → I → K
  | 0, .inl a, x => if a = x then 1 else 0
  | 0, .inr _, _ => 0
  | _ + 1, .inl _, _ => 0
  | n + 1, .inr a, x => (F.equation a).eval (fun w => signalCoeff n w x)

/-- Formal transfer to an individual input or state wire. -/
def signalSeries (p : I ⊕ Fin s) (x : I) : PowerSeries K :=
  PowerSeries.mk (fun n => F.signalCoeff n p x)

@[simp] theorem signalSeries_input (a x : I) :
    F.signalSeries (.inl a) x = if a = x then 1 else 0 := by
  ext n
  cases n <;> by_cases h : a = x <;> simp [signalSeries, signalCoeff, h, PowerSeries.coeff_one]

theorem signalSeries_state (a : Fin s) (x : I) :
    F.signalSeries (.inr a) x = X *
      (C (F.equation a).leftCoeff * F.signalSeries (F.equation a).left x +
       C (F.equation a).rightCoeff * F.signalSeries (F.equation a).right x) := by
  ext n
  cases n with
  | zero => simp [signalSeries, signalCoeff]
  | succ n => simp [signalSeries, signalCoeff, BinaryGate.eval, coeff_succ_X_mul, coeff_C_mul]

/-- The output transfer as a matrix of power series at delay zero. -/
def delaySeries (o : O) (x : I) : PowerSeries K :=
  match F.output o with
  | .zero => 0
  | .scaled c p => C c * F.signalSeries p x

/-- A coefficient row tested on the state registers evaluates the chosen predecessor
when it is a state, and gives zero when it is an input. -/
private theorem statePart {W Z : Type*} [Fintype Z] [DecidableEq (W ⊕ Z)] (w : W ⊕ Z) (c : K) (v : Z → K) :
    ∑ a, Pi.single (M := fun _ => K) w c (.inr a) * v a =
      Sum.elim (fun _ => 0) (fun a => c * v a) w := by
  classical
  cases w with
  | inl i => simp
  | inr a => simp [Pi.single_apply, ite_mul]

private theorem oneStateCoeff (a : Fin s) (x : I) :
    F.signalCoeff 1 (.inr a) x = F.inputMatrix a x := by
  let _ : DecidableEq (I ⊕ Fin s) := Classical.decEq _
  simp only [signalCoeff, BinaryGate.eval, inputMatrix, gateRow, Pi.add_apply]
  let g := F.equation a
  change g.leftCoeff * F.signalCoeff 0 g.left x + g.rightCoeff * F.signalCoeff 0 g.right x =
    Pi.single (M := fun _ => K) g.left g.leftCoeff (.inl x) + Pi.single (M := fun _ => K) g.right g.rightCoeff (.inl x)
  have h (w : I ⊕ Fin s) (v : K) :
      v * F.signalCoeff 0 w x = Pi.single (M := fun _ => K) w v (.inl x) := by
    cases w <;> simp [signalCoeff, Pi.single_apply, eq_comm, mul_ite]
  rw [h, h]

/-- The coefficient obtained after visiting `n+1` states is the usual matrix walk
sum, including repeated state visits. -/
theorem signalCoeff_state (n : ℕ) (a : Fin s) (x : I) :
    F.signalCoeff (n + 1) (.inr a) x = (F.stateMatrix ^ n * F.inputMatrix) a x := by
  classical
  let _ : DecidableEq (I ⊕ Fin s) := Classical.decEq _
  induction n generalizing a with
  | zero => simpa using F.oneStateCoeff a x
  | succ n ih =>
    rw [pow_succ', Matrix.mul_assoc, Matrix.mul_apply]
    simp only [signalCoeff, BinaryGate.eval, stateMatrix, gateRow, Pi.add_apply]
    let g := F.equation a
    let v (b : Fin s) := (F.stateMatrix ^ n * F.inputMatrix) b x
    change g.leftCoeff * F.signalCoeff (n + 1) g.left x +
        g.rightCoeff * F.signalCoeff (n + 1) g.right x =
      ∑ b, (Pi.single (M := fun _ => K) g.left g.leftCoeff (.inr b) + Pi.single (M := fun _ => K) g.right g.rightCoeff (.inr b)) * v b
    simp_rw [add_mul, Finset.sum_add_distrib, statePart]
    have h (w : I ⊕ Fin s) (c : K) : c * F.signalCoeff (n + 1) w x =
        Sum.elim (fun _ => 0) (fun b => c * v b) w := by
      cases w with
      | inl a => simp [signalCoeff]
      | inr b => exact congrArg (c * ·) (ih b)
    rw [h, h]

/-- The direct term of the delay transfer is the input-to-output readout matrix. -/
theorem coeff_zero_delaySeries (o : O) (x : I) :
    PowerSeries.coeff 0 (F.delaySeries o x) = F.readInput o x := by
  cases h : F.output o with
  | zero => simp [delaySeries, h, readInput, readRow]
  | scaled c w =>
    cases w <;> simp [delaySeries, h, readInput, readRow, signalSeries, signalCoeff,
      coeff_C_mul, Pi.single_apply, eq_comm, mul_ite]

/-- The positive-degree transfer coefficients are `E C^n T` for degree `n+1`. -/
theorem coeff_succ_delaySeries (n : ℕ) (o : O) (x : I) :
    PowerSeries.coeff (n + 1) (F.delaySeries o x) =
      (F.readState * F.stateMatrix ^ n * F.inputMatrix) o x := by
  let _ : DecidableEq (I ⊕ Fin s) := Classical.decEq _
  rw [Matrix.mul_assoc, Matrix.mul_apply]
  cases h : F.output o with
  | zero => simp [delaySeries, h, readState, readRow]
  | scaled c w =>
    simp only [delaySeries, h, coeff_C_mul, signalSeries, coeff_mk, readState, readRow]
    rw [statePart w c (fun a => (F.stateMatrix ^ n * F.inputMatrix) a x)]
    cases w with
    | inl a => simp [signalCoeff]
    | inr a => simp [F.signalCoeff_state]

/-- Tensor entry of the signals selected in a tuple, in the common variable. -/
def signalProduct {j : ℕ} (p : Fin j → I ⊕ Fin s) (x : Fin j → I) : PowerSeries K :=
  ∏ a, F.signalSeries (p a) (x a)

private theorem product_cons {j : ℕ} (p : I ⊕ Fin s) (ps : Fin j → I ⊕ Fin s)
    (x : Fin (j + 1) → I) :
    F.signalProduct (Fin.cons p ps) x = F.signalSeries p (x 0) * F.signalProduct ps (Fin.tail x) := by
  simp [signalProduct, Fin.prod_univ_succ, Fin.tail]

variable [Fintype I]

/-- Input tuples supporting one total degree at the indicated tuple of signals. -/
def walkSupport (n : ℕ) {j : ℕ} (p : Fin j → I ⊕ Fin s) : Finset (Fin j → I) :=
  Finset.univ.filter fun x => PowerSeries.coeff n (F.signalProduct p x) ≠ 0

private theorem mem_walkSupport (n : ℕ) {j : ℕ} (p : Fin j → I ⊕ Fin s) (x : Fin j → I) :
    x ∈ F.walkSupport n p ↔ PowerSeries.coeff n (F.signalProduct p x) ≠ 0 := by
  simp [walkSupport]

/-- For arbitrary starting signals, all tuples of walks with total length `n` have
at most `2^n` different tuples of endpoints with nonzero coefficients. -/
theorem card_walkSupport (n j : ℕ) (p : Fin j → I ⊕ Fin s) :
    (F.walkSupport n p).card ≤ 2 ^ n := by
  classical
  cases j with
  | zero =>
    exact (Finset.card_le_univ _).trans (by simp; exact Nat.one_le_iff_ne_zero.mpr (pow_ne_zero _ (by decide)))
  | succ j =>
    let ps := Fin.tail p
    have hp : Fin.cons (p 0) ps = p := Fin.cons_self_tail p
    cases he : p 0 with
    | inl a =>
      have hsub : F.walkSupport n p ⊆
          (F.walkSupport n ps).image (fun xs => Fin.cons a xs) := by
        intro x hx
        have h := (F.mem_walkSupport _ _ _).mp hx
        rw [← hp, he, F.product_cons, F.signalSeries_input] at h
        by_cases ha : a = x 0
        · rw [ite_eq_left ha, one_mul] at h
          exact Finset.mem_image.mpr ⟨Fin.tail x, (F.mem_walkSupport _ _ _).mpr h,
            ha ▸ Fin.cons_self_tail x⟩
        · simp [ha] at h
      exact (Finset.card_le_card hsub).trans
        (Finset.card_image_le.trans (card_walkSupport n j ps))
    | inr a =>
      let g := F.equation a
      cases n with
      | zero =>
        have he' : F.walkSupport 0 p = ∅ := by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro x hx
          have h := (F.mem_walkSupport _ _ _).mp hx
          rw [← hp, he, F.product_cons, F.signalSeries_state, mul_assoc,
            coeff_zero_X_mul] at h
          exact h rfl
        simp [he']
      | succ n =>
        let l : Fin (j + 1) → I ⊕ Fin s := Fin.cons g.left ps
        let r : Fin (j + 1) → I ⊕ Fin s := Fin.cons g.right ps
        have hsub : F.walkSupport (n + 1) p ⊆ F.walkSupport n l ∪ F.walkSupport n r := by
          intro x hx
          by_contra! hneg
          rw [Finset.mem_union, not_or] at hneg
          have hl : PowerSeries.coeff n (F.signalProduct l x) = 0 := by
            simpa [F.mem_walkSupport] using hneg.1
          have hr : PowerSeries.coeff n (F.signalProduct r x) = 0 := by
            simpa [F.mem_walkSupport] using hneg.2
          have h := (F.mem_walkSupport _ _ _).mp hx
          rw [← hp, he, F.product_cons, F.signalSeries_state, mul_assoc, coeff_succ_X_mul,
            add_mul, mul_assoc, mul_assoc, map_add, coeff_C_mul, coeff_C_mul] at h
          rw [← F.product_cons, ← F.product_cons] at h
          apply h
          change g.leftCoeff * PowerSeries.coeff n (F.signalProduct l x) +
              g.rightCoeff * PowerSeries.coeff n (F.signalProduct r x) = 0
          simp [hl, hr]
        calc
          _ ≤ (F.walkSupport n l ∪ F.walkSupport n r).card := Finset.card_le_card hsub
          _ ≤ (F.walkSupport n l).card + (F.walkSupport n r).card := Finset.card_union_le _ _
          _ ≤ 2 ^ n + 2 ^ n := Nat.add_le_add
            (card_walkSupport n (j + 1) l) (card_walkSupport n (j + 1) r)
          _ = _ := by rw [pow_succ]; omega
termination_by (n, j)

/-- Columns where the degree-`n` coefficient of the tensor power is nonzero
in this row of output selections. -/
def outputSupport (n : ℕ) {j : ℕ} (row : Fin j → O) : Finset (Fin j → I) :=
  Finset.univ.filter fun x => PowerSeries.coeff n (∏ t, F.delaySeries (row t) (x t)) ≠ 0

/-- The small-price walk bound for actual circuit readouts, including free zero outputs,
repeated reads and arbitrary scaling. -/
theorem card_outputSupport (n j : ℕ) (row : Fin j → O) :
    (F.outputSupport n row).card ≤ 2 ^ n := by
  classical
  by_cases hzero : ∃ t, F.output (row t) = .zero
  · obtain ⟨t, ht⟩ := hzero
    have h : F.outputSupport n row = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro x
      have hz : (∏ a, F.delaySeries (row a) (x a)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ t) (by simp [delaySeries, ht])
      simp [outputSupport, hz]
    simp [h]
  · have hscaled (a : Fin j) : ∃ c p, F.output (row a) = .scaled c p := by
      cases he : F.output (row a) with
      | zero => exact (hzero ⟨a, he⟩).elim
      | scaled c p => exact ⟨c, p, rfl⟩
    choose c p hp using hscaled
    apply (Finset.card_le_card (s := F.outputSupport n row) (t := F.walkSupport n p) ?_).trans
      (F.card_walkSupport n j p)
    intro x hx
    have hprod : (∏ a, F.delaySeries (row a) (x a)) =
        PowerSeries.C (R := K) (∏ a, c a) * F.signalProduct p x := by
      simp [delaySeries, hp, Finset.prod_mul_distrib, map_prod, signalProduct]
    rw [F.mem_walkSupport]
    simp only [outputSupport, Finset.mem_filter, Finset.mem_univ, true_and, hprod,
      PowerSeries.coeff_C_mul] at hx
    exact right_ne_zero_of_mul hx

end
end Feedback

end FiniteFourier
end LinearAlgebra
end OAI
