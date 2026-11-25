import OAI.Computability.BorderVNP.CubeGroupLoad
import OAI.Computability.BorderVNP.CubePhysicalDeclaration

/-! # Exact raw-wire charge of a symbol group

Every ordered label pair has the same padded width. A wire with both ends in a
group contributes once. This gives the inclusion-exclusion count used by the
public group-weight program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

open Finset

/-- Count the padded ordered wires with at least one endpoint in the group. -/
theorem groupRaw_eq {n d : ℕ} (S : ℕ) (i : Fin (n+1)) (s : Fin d) :
    groupRaw S i s = S * d^n * (2*d^(n+1) - d^n) := by
  let inside := fun u : Label (n+1) d => u i = s
  let A := univ.filter inside
  let B := univ.filter fun u => ¬inside u
  have ha : A.card = d^n := card_fixed_symbol i s
  have hc : Fintype.card (Label (n+1) d) = d^(n+1) := by simp [Label]
  have hab : d^n + B.card = d^(n+1) := by
    simpa only [← ha, A, B, card_univ, hc] using card_filter_add_card_filter_not (s := univ) inside
  let ends := fun u : Label (n+1) d => ∑ v : Label (n+1) d, if u i = s ∨ v i = s then S else 0
  have hA : (∑ u ∈ A, ends u) = A.card * (d^(n+1)*S) := by
    have h u (hu : u ∈ A) : ends u = d^(n+1)*S := by
      have hi : u i = s := (mem_filter.mp hu).2
      simp [ends,hi,hc]
    simp only [sum_congr rfl h, sum_const, nsmul_eq_mul, Nat.cast_id]
  have hB : (∑ u ∈ B, ends u) = B.card * (d^n*S) := by
    have h u (hu : u ∈ B) : ends u = d^n*S := by
      have hi : u i ≠ s := (mem_filter.mp hu).2
      simp only [ends,hi,false_or]
      rw [← sum_filter]; simp only [sum_const, nsmul_eq_mul, Nat.cast_id, card_fixed_symbol]
    simp only [sum_congr rfl h, sum_const, nsmul_eq_mul, Nat.cast_id]
  change ∑ u, ends u = _
  rw [← sum_filter_add_sum_filter_not univ inside ends, hA, hB, ha,
    show 2*d^(n+1)-d^n = d^(n+1)+B.card by omega]
  ring

namespace Physical

variable {n d blocks width : ℕ}

private abbrev Pieces (n d blocks width : ℕ) :=
  (Packet n d blocks × (Vertex n × Fin width)) ⊕ SingleSlot n d blocks width

private def pieceRow (i : Fin (n+1)) : Pieces n d blocks width → Sym2 (Fin d)
  | .inl (p, _, _) => itemRow i (.inl p : Item n d blocks width)
  | .inr z => itemRow i (.inr z)

private theorem slot_meets (i : Fin (n+1)) (s : Fin d) (a : Pieces n d blocks width) :
    let z := (splitSlot n d blocks width).symm a
    (z.1.1 i = s ∨ z.1.2 i = s) ↔ s ∈ pieceRow i a := by
  rcases a with ⟨p,v,j⟩ | z
  · change _ ↔ s ∈ Sym2.mk (p.1.1 i).val.1 (p.1.1 i).val.2
    rw [Sym2.mem_iff]
    let corner := Fin.cons (α := fun _ : Fin (n+1) => Bool) p.1.2 (fun k => finTwoEquiv (v k))
    change ((if corner i then (p.1.1 i).val.2 else (p.1.1 i).val.1) = s ∨
      (if corner i then (p.1.1 i).val.1 else (p.1.1 i).val.2) = s) ↔ _
    cases corner i <;> simp [eq_comm,or_comm]
  · change (z.1.val.1 i = s ∨ z.1.val.2 i = s) ↔ s ∈ Sym2.mk (z.1.val.1 i) (z.1.val.2 i)
    simp [Sym2.mem_iff,eq_comm]

/-- The charge in the actual packet and singleton inventory equals the incidence
count of the original padded slots. Each incident packet contributes all its
antipodal words and each incident singleton contributes one bit. -/
theorem item_raw_eq_groupRaw (i : Fin (n+1)) (s : Fin d) :
    (∑ p : Packet n d blocks, if s ∈ itemRow i (.inl p : Item n d blocks width)
        then 2^n*width else 0) +
      (∑ z : SingleSlot n d blocks width, if s ∈ itemRow i (.inr z) then 1 else 0) =
    groupRaw (blocks*width) i s := by
  let w := fun z : Slot n d blocks width => if z.1.1 i = s ∨ z.1.2 i = s then 1 else 0
  let f := fun a : Pieces n d blocks width => if s ∈ pieceRow i a then 1 else 0
  have eq : ∑ a, f a = ∑ z, w z :=
    Fintype.sum_equiv (splitSlot n d blocks width).symm f w fun a => by
      simp only [f,w,slot_meets]
  have hf : ∑ a, f a = _ := Fintype.sum_sum_type f
  rw [hf, Fintype.sum_prod_type (fun a : Packet n d blocks × (Vertex n × Fin width) => f (.inl a))] at eq
  have hw (uv : Label (n+1) d × Label (n+1) d) :
      (∑ j : Fin (blocks*width), w (uv,j)) = if uv.1 i = s ∨ uv.2 i = s then blocks*width else 0 := by
    by_cases h : uv.1 i = s ∨ uv.2 i = s <;> simp [w,h]
  have hp (p : Packet n d blocks) :
      (∑ v : Vertex n × Fin width, f (.inl (p,v))) =
        if s ∈ itemRow i (.inl p : Item n d blocks width) then 2^n*width else 0 := by
    by_cases h : s ∈ itemRow i (.inl p : Item n d blocks width) <;>
      simp [f,pieceRow,h,Vertex]
  rw [Fintype.sum_prod_type w] at eq
  simp_rw [hp,hw] at eq
  rw [Fintype.sum_prod_type (fun uv : Label (n+1) d × Label (n+1) d =>
    if uv.1 i = s ∨ uv.2 i = s then blocks*width else 0)] at eq
  exact eq

end Physical

end Cube

end BorderVNP
end Computability
end OAI
