import OAI.Computability.VPVNP.ChainAssignments

/-!
# The two live modes in the physical chain contraction

A unit-mode group accepts only zero strings on its incident cuts. An
evaluation-mode group reads a true mode bit on each incident interior cut.
Neighboring groups therefore cannot contribute in different modes to a
nonzero product. The unit-mode product counts the unique all-zero assignment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ChainAssignments

open CutSchedule
open scoped Classical

variable {h Δ : ℕ}

/-- The unit group accepts exactly once when both incident cut fields are zero. -/
noncomputable def unitGroupCount (cuts : AllCuts h Δ) (i : Fin (2 ^ (h+1))) : ℕ :=
  if cuts i.castSucc = (fun _ => false) ∧ cuts i.succ = (fun _ => false) then 1 else 0

/-- The first bit on an interior cut selects evaluation mode. Endpoints carry no bits. -/
def evalCutMode (cuts : AllCuts h Δ) (j : Fin (2 ^ (h+1) + 1)) : Prop :=
  0 < j.val → j.val < 2 ^ (h+1) → distributedBit (cuts j) 0 = true

/-- Every interior cut has its evaluation-mode bit, the bit at distributed position zero, set
to true. -/
def activeCuts (cuts : AllCuts h Δ) : Prop := ∀ j, evalCutMode cuts j

private theorem prod_modes {N : ℕ} (hn : 0 < N) (u e : Fin N → ℕ)
    (adj : ∀ i j : Fin N, i.val+1 = j.val → u i * e j = 0 ∧ e i * u j = 0) :
    (∏ i, (u i + e i)) = (∏ i, u i) + ∏ i, e i := by
  cases N with
  | zero => omega
  | succ k =>
    induction k with
    | zero => simp
    | succ k ih =>
      have hprefix := ih (by omega) (fun i => u i.castSucc) (fun i => e i.castSucc)
        (fun i j he => adj i.castSucc j.castSucc he)
      let last := Fin.last (k+1)
      have ⟨h₁, h₂⟩ := adj (Fin.last k).castSucc last rfl
      have cross (f : Fin (k+1) → ℕ) (b : ℕ) (hb : f (Fin.last k) * b = 0) :
          (∏ i, f i) * b = 0 := by
        rw [Fin.prod_univ_castSucc f, mul_assoc, hb, mul_zero]
      have hcross₁ := cross (fun i => u i.castSucc) (e last) h₁
      have hcross₂ := cross (fun i => e i.castSucc) (u last) h₂
      rw [Fin.prod_univ_castSucc (fun i => u i + e i), Fin.prod_univ_castSucc u,
        Fin.prod_univ_castSucc e, hprefix, add_mul, mul_add, mul_add, hcross₁, hcross₂, add_zero, zero_add]

private theorem prod_unit (cuts : AllCuts h Δ) :
    (∏ i, unitGroupCount cuts i) = if cuts = (fun _ _ => false) then 1 else 0 := by
  have allZero : (∀ i : Fin (2^(h+1)), cuts i.castSucc = (fun _ => false) ∧
      cuts i.succ = (fun _ => false)) ↔ cuts = (fun _ _ => false) := by
    constructor
    · intro hz
      funext j
      apply Fin.cases (motive := fun j => cuts j = fun _ => false) _ (fun i => (hz i).2) j
      exact (hz ⟨0, Nat.two_pow_pos _⟩).1
    · rintro rfl
      simp
  simp only [unitGroupCount, Fintype.prod_ite_zero, Finset.prod_const_one]
  split_ifs <;> tauto

variable (eval : AllCuts h Δ → Fin (2^(h+1)) → ℕ)
variable (mode : ∀ cuts i, eval cuts i ≠ 0 → evalCutMode cuts i.castSucc ∧ evalCutMode cuts i.succ)

include mode

/-- At fixed cuts every mixed-mode term vanishes, including terms switching
modes across the midpoint. -/
theorem group_mode_product (cuts : AllCuts h Δ) :
    (∏ i, (unitGroupCount cuts i + eval cuts i)) =
      (if cuts = (fun _ _ => false) then 1 else 0) + ∏ i, eval cuts i := by
  rw [← prod_unit cuts]
  apply prod_modes (Nat.two_pow_pos _)
  intro i j hij
  have he : i.succ = j.castSucc := Fin.ext hij
  have hi : 0 < i.succ.val := Nat.succ_pos _
  have hj : j.castSucc.val < 2^(h+1) := j.isLt
  have falseBit {d : ℕ} (bits : Bits d) (hz : bits = fun _ => false) : distributedBit bits 0 = false := by
    subst bits
    simp [distributedBit]
  constructor
  · by_cases hu : cuts i.castSucc = (fun _ => false) ∧ cuts i.succ = (fun _ => false)
    · have ez : eval cuts j = 0 := by
        by_contra hne
        have htrue := (mode cuts j hne).1 (he ▸ hi) hj
        rw [← he, falseBit _ hu.2] at htrue
        contradiction
      simp [ez]
    · unfold unitGroupCount
      split_ifs with hit
      · exact (hu hit).elim
      · simp
  · by_cases hu : cuts j.castSucc = (fun _ => false) ∧ cuts j.succ = (fun _ => false)
    · have ez : eval cuts i = 0 := by
        by_contra hne
        have htrue := (mode cuts i hne).2 hi (he.symm ▸ hj)
        rw [he, falseBit _ hu.1] at htrue
        contradiction
      simp [ez]
    · unfold unitGroupCount
      split_ifs with hit
      · exact (hu hit).elim
      · simp

/-- A zero evaluation-mode bit on any interior cut kills the whole evaluation product. -/
theorem eval_product_zero_of_inactive (cuts : AllCuts h Δ) (bad : ¬activeCuts cuts) :
    (∏ i, eval cuts i) = 0 := by
  by_contra hn
  apply bad
  intro j _ hlt
  let i : Fin (2^(h+1)) := ⟨j.val, hlt⟩
  have hmode := (mode cuts i (Finset.prod_ne_zero_iff.mp hn i (Finset.mem_univ _))).1
  exact hmode ‹0 < j.val› hlt

/-- Summing the physical products counts one unit execution and the full
contraction of evaluation-mode groups. -/
theorem sum_groupCount_eq_one_add_eval (groups : AllCuts h Δ → Fin (2^(h+1)) → ℕ)
    (localCount : ∀ cuts i, groups cuts i = unitGroupCount cuts i + eval cuts i) :
    (∑ cuts, ∏ i, groups cuts i) = 1 + ∑ cuts, ∏ i, eval cuts i := by
  simp_rw [localCount, group_mode_product eval mode]
  rw [Finset.sum_add_distrib]
  simp

/-- The evaluation sum in the live-mode identity can be restricted to cut
assignments with true mode bits on every interior cut. -/
theorem sum_groupCount_eq_one_add_active (groups : AllCuts h Δ → Fin (2^(h+1)) → ℕ)
    (localCount : ∀ cuts i, groups cuts i = unitGroupCount cuts i + eval cuts i) :
    (∑ cuts, ∏ i, groups cuts i) = 1 + ∑ cuts, if activeCuts cuts then ∏ i, eval cuts i else 0 := by
  rw [sum_groupCount_eq_one_add_eval eval mode groups localCount]
  congr 1
  apply Finset.sum_congr rfl
  intro cuts _
  by_cases ok : activeCuts cuts
  · simp [ok]
  · simp [ok, eval_product_zero_of_inactive eval mode cuts ok]

end ChainAssignments

end VPVNP
end Computability
end OAI
