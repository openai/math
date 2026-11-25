import OAI.ThreeFlat.Routing.CallPoolBudget
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Fin.Embedding

namespace OAI
/-! # Ordered batches of connections within a public class -/

namespace ThreeFlat.Routing.CallPool

open scoped BigOperators
noncomputable section

/-- Enumerate batches separately within each class. -/
abbrev Batch {I : Type*} (count : I → ℕ) (capacity : ℕ) :=
  (i : I) × Fin (poolBatchCount (count i) capacity)

/-- A batch holds a consecutive interval in the order for its class. -/
abbrev Unit {I : Type*} (count : I → ℕ) (capacity : ℕ) (b : Batch count capacity) :=
  {u : Fin (count b.1) // u.val / capacity = b.2.val}

theorem count_le_batches_mul (n h : ℕ) (pos : 0 < h) : n ≤ h * poolBatchCount n h := by
  change n ≤ h * (n ⌈/⌉ h)
  exact (ceilDiv_le_iff_le_mul pos).1 le_rfl

/-- Every unit has a prescribed batch. -/
def batchIndex {I : Type*} {c : I → ℕ} {h : ℕ} (pos : 0 < h) (i : I) (u : Fin (c i)) :
    Batch c h :=
  ⟨i, ⟨u.val / h, (Nat.div_lt_iff_lt_mul pos).2 <| by
    simpa [mul_comm] using u.isLt.trans_le (count_le_batches_mul (c i) h pos)⟩⟩

/-- The offset inside the batch separates its units. -/
def offset {I : Type*} {c : I → ℕ} {h : ℕ} (pos : 0 < h) (b : Batch c h) :
    Unit c h b ↪ Fin h where
  toFun u := ⟨u.val.val % h, Nat.mod_lt _ pos⟩
  inj' := by
    intro u v e
    have d : u.val.val / h = v.val.val / h := u.property.trans v.property.symm
    have m : u.val.val % h = v.val.val % h := congrArg Fin.val e
    apply Subtype.ext
    apply Fin.ext
    calc
      _ = h * (u.val.val / h) + u.val.val % h := (Nat.div_add_mod _ _).symm
      _ = h * (v.val.val / h) + v.val.val % h := by rw [d,m]
      _ = _ := Nat.div_add_mod _ _

theorem unit_slack {I : Type*} (c : I → ℕ) {H : ℕ} (size : 1000 ≤ H)
    (b : Batch c (999*H/1000)) :
    1000 * Fintype.card (Unit c (999*H/1000) b) + H ≤ 1000 * H := by
  have h : 0 < 999*H/1000 := by omega
  have le := Fintype.card_le_of_embedding (offset h b)
  simp only [Fintype.card_fin] at le
  omega

/-- Restrict the public batch addresses to the prefix of active batches in each class. -/
def batchAddress {I : Type*} {c C : I → ℕ} (capacity : ℕ) (bounded : ∀ i, c i ≤ C i) :
    Batch c capacity ↪ Batch C capacity where
  toFun b := ⟨b.1, Fin.castLE (by
    unfold poolBatchCount
    exact Nat.div_le_div_right (Nat.sub_le_sub_right (Nat.add_le_add_right (bounded b.1) _) _)) b.2⟩
  inj' := by
    rintro ⟨i,u⟩ ⟨j,v⟩ e
    obtain rfl : i = j := congrArg Sigma.fst e
    congr
    apply Fin.ext
    exact congrArg (fun b : Batch C capacity => b.2.val) e

/-- The active batch indices satisfy the mask bound on the common pool. -/
theorem batch_slack {I : Type*} [Fintype I] (c : I → ℕ) (H U W : ℕ)
    (size : 1000 ≤ H) (width : 0 < U)
    (occupied : 100 * (∑ i, c i) * U ≤ 125 * W)
    (last : 100 * Fintype.card I * (H*U) ≤ W) :
    let cap := 999*H/1000
    let K := 129*W/(100*(H*U))
    1000*Fintype.card (Batch c cap) + K ≤ 1000*K := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using callPoolBudget c H U W size width occupied last

end
end ThreeFlat.Routing.CallPool

end OAI
