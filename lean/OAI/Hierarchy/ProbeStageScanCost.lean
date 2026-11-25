import OAI.Hierarchy.ProbeStageMask

namespace OAI
/-! # Amortized scan cost for the actual endpoint residue masks -/

namespace Hierarchy.ProbeStage

open Finset
open scoped BigOperators

private theorem residue_fiber {n B : ℕ} {E : Type*} (pos : 0<B) [DecidableEq E]
    (block : Fin n → E) (x : E) (offset : {i // block i=x} ↪ Fin (blockSize B))
    (index : Fin n → MaskIndex B) (side : MaskIndex B → Fin (B^2))
    (residue : ∀ i, (offset i).val % (B^2) = (side (index i.val)).val) (w : MaskIndex B) :
    (univ.filter fun i => block i=x ∧ index i=w).card ≤ B^7 := by
  let z (i : {i // block i=x ∧ index i=w}) : Fin (blockSize B) := offset ⟨i.val,i.property.1⟩
  let f (i : {i // block i=x ∧ index i=w}) : Fin (B^7) := ⟨(z i).val / (B^2),by
    apply (Nat.div_lt_iff_lt_mul (pow_pos pos _)).mpr
    simpa only [← pow_add, blockSize] using (z i).isLt⟩
  have hinj : Function.Injective f := by
    intro i j h
    have hdiv : (z i).val/(B^2) = (z j).val/(B^2) := congrArg Fin.val h
    have hmod (i : {i // block i=x ∧ index i=w}) : (z i).val % (B^2) = (side w).val := by
      rw [← i.property.2]; exact residue ⟨i.val,i.property.1⟩
    have he : z i = z j := Fin.ext (by
      rw [← Nat.mod_add_div (z i).val (B^2), ← Nat.mod_add_div (z j).val (B^2),hmod i,hmod j,hdiv])
    exact Subtype.ext (congrArg (fun a : {i // block i=x} => a.val) (offset.injective he))
  simpa only [Fintype.card_subtype, Fintype.card_fin] using Fintype.card_le_of_injective f hinj

/-- For a source block and a fixed label `(u mod B²,v mod B²)`, the inner source quotient
uniquely identifies a record. -/
theorem source_residue_bound {n m B : ℕ} {G : Type*} [DecidableEq G] (p : Tiles (Fin n) G m)
    (pos : 0<B) (g : G × Fin (blocks m B)) (w : MaskIndex B) :
    (univ.filter fun i => leftBlock p pos i=g ∧ maskIndex p pos i=w).card ≤ B^7 :=
  residue_fiber pos _ g (leftBlockFiber p pos g) (maskIndex p pos) Prod.fst (fun _ => rfl) w

/-- The same injection uses the target position and the second residue at the target block. -/
theorem target_residue_bound {n m B : ℕ} {G : Type*} [DecidableEq G] (p : Tiles (Fin n) G m)
    (pos : 0<B) (g : G × Fin (blocks m B)) (w : MaskIndex B) :
    (univ.filter fun i => rightBlock p pos i=g ∧ maskIndex p pos i=w).card ≤ B^7 :=
  residue_fiber pos _ g (rightBlockFiber p pos g) (maskIndex p pos) Prod.snd (fun _ => rfl) w

def overloaded {B ℓ : ℕ} (strings : MaskIndex B → Fin ℓ → Fin B) (S : Finset (Fin B)) : Finset (MaskIndex B) :=
  univ.filter fun w => ℓ ≤ 2*(univ.filter fun t => strings w t ∈ S).card

/-- Charge a full search over all `B` colors to one of its two final endpoint masks. Each bad
string receives at most `B⁷` charges, and the string advice leaves fewer than `B` bad strings. -/
theorem scan_cost {B n ℓ : ℕ} {E : Type*} [DecidableEq E] (block : Fin n → E)
    (index : Fin n → MaskIndex B) (x : E)
    (cap : ∀ w, (univ.filter fun i => block i=x ∧ index i=w).card ≤ B^7)
    (strings : MaskIndex B → Fin ℓ → Fin B) (S : Finset (Fin B))
    (few : (overloaded strings S).card < B) :
    B*(univ.filter fun i => block i=x ∧ index i ∈ overloaded strings S).card ≤ blockSize B := by
  let bad := overloaded strings S
  let charged := univ.filter fun i => block i=x ∧ index i ∈ bad
  have sum := card_eq_sum_card_fiberwise (s := charged) (t := bad) (f := index)
    (fun i hi => (mem_filter.mp hi).2.2)
  have hle (w : MaskIndex B) : (charged.filter fun i => index i=w).card ≤ B^7 := by
    apply LE.le.trans (card_le_card _) (cap w)
    intro i h
    obtain ⟨hc,hi⟩ := mem_filter.mp h
    exact mem_filter.mpr ⟨mem_univ _,(mem_filter.mp hc).2.1,hi⟩
  have h := sum.trans_le (sum_le_sum (fun w _ => hle w))
  simp only [sum_const,nsmul_eq_mul] at h
  have h' := h.trans (Nat.mul_le_mul_right (B^7) few.le)
  change B*charged.card ≤ B^9
  exact (Nat.mul_le_mul_left B h').trans_eq (by ring)

end Hierarchy.ProbeStage

end OAI
