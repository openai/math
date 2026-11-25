import OAI.Computability.BorderVNP.ParseBatchSort
import OAI.Computability.BorderVNP.CrossingParallelFrame
import Mathlib.Data.List.Sort

/-!
# Multiset comparison of two fixed-width bit arrays

The two Batcher sorts preserve multiplicities. A linear scan tests equality of
every output bit. All gates are deterministic, including the treatment of ties.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatchLeaves

open VPVNP VPVNP.VerifierNetwork BorderVNP.ParseBatchSort
open BinPackingGames.Foundations.Complexity.CookLevin
open scoped Classical

variable {τ : Type*} [Fintype τ]

private def different (i : τ) : Expr (τ ⊕ τ) :=
  .or (.and (.input (.inl i)) (.not (.input (.inr i))))
    (.and (.not (.input (.inl i))) (.input (.inr i)))

private noncomputable def same : Expr (τ ⊕ τ) :=
  .not (StatementCircuit.Expr.disjoin (Finset.univ.toList.map different))

private theorem same_eval (z : τ ⊕ τ → Bool) :
    same.eval z = true ↔ ∀ i, z (.inl i) = z (.inr i) := by
  have hd (i : τ) : (different i).eval z = true ↔ z (.inl i) ≠ z (.inr i) := by
    cases hl : z (.inl i) <;> cases hr : z (.inr i) <;> simp [different, StatementCircuit.Expr.eval, hl, hr]
  simp only [same, StatementCircuit.Expr.eval, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  change (¬ _ = true) ↔ _
  simp only [StatementCircuit.Expr.eval_disjoin_true]
  simp [hd]

private theorem same_size : (same (τ := τ)).size ≤ 10 * Fintype.card τ + 2 := by
  have hd := StatementCircuit.Expr.size_disjoin_le (Finset.univ.toList.map (different (τ := τ))) 9
    (by rintro _ hx; obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx; exact (show 9 ≤ 9 from le_rfl))
  simp only [same, StatementCircuit.Expr.size]
  simp at hd
  omega

variable {b w : ℕ}

/-- Input wires of the two arrays, each padded to a power-of-two row count. -/
abbrev SortInputs (b w : ℕ) := Pins b w ⊕ Pins b w

private noncomputable def sortLeft (b w : ℕ) : Frame (SortInputs b w) (Pins b w) :=
  phases b le_rfl (Frame.initial Sum.inl)

private noncomputable def sortRight (b w : ℕ) : Frame (SortInputs b w) (Pins b w) :=
  phases b le_rfl (Frame.initial Sum.inr)

/-- Concrete Boolean network comparing the multisets of two word arrays. -/
noncomputable def compareFrame (b w : ℕ) : Frame (SortInputs b w) Unit :=
  (Crossing.parallelFrame (sortLeft b w) (sortRight b w)).step fun _ => same

private theorem sort_eq_iff (a c : Fin (2^b) → ℕ) :
    RAMSort.sort b true a = RAMSort.sort b true c ↔ (List.ofFn a).Perm (List.ofFn c) := by
  have ha := RAMSort.sort_perm b true a
  have hc := RAMSort.sort_perm b true c
  constructor
  · intro e
    rw [← e] at hc
    exact ha.symm.trans hc
  · intro e
    apply List.ofFn_injective
    apply ((ha.trans e).trans hc.symm).eq_of_pairwise' (r := (· ≤ ·))
    · exact List.pairwise_ofFn.mpr fun _ _ hij => RAMSort.sort_monotone _ _ hij.le
    · exact List.pairwise_ofFn.mpr fun _ _ hij => RAMSort.sort_monotone _ _ hij.le

/-- The frame accepts precisely equal multisets of the actual fixed-width words. -/
theorem compareFrame_eval (z : SortInputs b w → Bool) :
    (compareFrame b w).eval z () = true ↔
      (List.ofFn fun i : Fin (2^b) => value (fun j : Fin w => z (.inl (i,j)))).Perm
        (List.ofFn fun i : Fin (2^b) => value (fun j : Fin w => z (.inr (i,j)))) := by
  rw [compareFrame, Frame.step_eval, same_eval]
  simp only [Crossing.parallelFrame_eval_inl, Crossing.parallelFrame_eval_inr]
  have ha := phases_correct (Frame.initial (Sum.inl : Pins b w → SortInputs b w)) z
  have hc := phases_correct (Frame.initial (Sum.inr : Pins b w → SortInputs b w)) z
  simp only [Frame.initial_eval] at ha hc
  rw [← sort_eq_iff, ← ha, ← hc]
  constructor
  · intro h
    funext i
    exact congrArg value (funext fun j => h (i,j))
  · intro h i
    exact congrFun (value_injective w (congrFun h i.1)) i.2

/-- Two quadratic-depth sorting networks and a single linear scan suffice. -/
theorem compareFrame_size (b w : ℕ) : (compareFrame b w).size ≤
    2 * (b^2 * (2^b * (24*w+1))) + 10 * (2^b * w) + 2 := by
  have h₁ := phases_size b le_rfl (Frame.initial (Sum.inl : Pins b w → SortInputs b w))
  have h₂ := phases_size b le_rfl (Frame.initial (Sum.inr : Pins b w → SortInputs b w))
  have h₃ := Frame.step_size_le (Crossing.parallelFrame (sortLeft b w) (sortRight b w))
    (fun _ : Unit => same) (10 * Fintype.card (Pins b w) + 2) (fun _ => same_size)
  simp only [Crossing.parallelFrame_size, Fintype.card_unit, one_mul, Pins, Fintype.card_prod, Fintype.card_fin] at h₃
  simp only [Frame.initial_size, zero_add] at h₁ h₂
  change (sortLeft b w).size ≤ _ at h₁
  change (sortRight b w).size ≤ _ at h₂
  change (compareFrame b w).size ≤ _ at h₃
  omega

end ParseBatchLeaves

end BorderVNP
end Computability
end OAI
