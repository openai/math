import OAI.Hierarchy.FactorPinIntervals
import Mathlib.Data.List.Sort

namespace OAI
/-! # Reading only the input intervals listed by a factor descriptor -/

namespace Hierarchy.FactorPinIntervals

variable {S N L : ℕ}

def bucketLength (S span bucket : ℕ) := min span (S-bucket*span)

/-- Arithmetic address of this entry in a (possibly truncated) source interval. -/
def blockBit (S span b : ℕ) (z : Fin (bucketLength S span b)) : Fin S :=
  ⟨b*span+z.val, by
    have hz := lt_of_lt_of_le z.isLt (Nat.min_le_right span (S-b*span))
    omega⟩

def blockBits (S span b : ℕ) := (List.finRange (bucketLength S span b)).map (blockBit S span b)

@[simp] theorem blockBits_length (S span b : ℕ) :
    (blockBits S span b).length=bucketLength S span b := by simp [blockBits]

theorem blockBits_mem {span b : ℕ} (pos : 0<span) (j : Fin S) :
    j ∈ blockBits S span b ↔ j.val/span=b := by
  constructor
  · intro h
    obtain ⟨z,_,rfl⟩ := List.mem_map.mp h
    apply Nat.div_eq_of_lt_le
    · change b*span ≤ b*span+z.val
      omega
    · change b*span+z.val<(b+1)*span
      have hz := lt_of_lt_of_le z.isLt (Nat.min_le_left span (S-b*span))
      rw [Nat.add_mul,Nat.one_mul]
      omega
  · intro h
    have offset := Nat.mod_add_div j.val span
    rw [h,Nat.mul_comm span b] at offset
    have hS := j.isLt
    let z : Fin (bucketLength S span b) := ⟨j.val%span, lt_min (Nat.mod_lt _ pos) (by omega)⟩
    apply List.mem_map.mpr
    refine ⟨z,List.mem_finRange _,Fin.ext ?_⟩
    change b*span+j.val%span=j.val
    omega

theorem blockBits_sorted (S span b : ℕ) : (blockBits S span b).Pairwise (· < ·) := by
  apply List.pairwise_map.mpr
  apply (List.pairwise_lt_finRange _).imp
  intro i j h
  change b*span+i.val<b*span+j.val
  exact Nat.add_lt_add_left h _

/-- A factor scans exactly the input intervals in its descriptor, in descriptor
order. The arithmetic block loop visits no bits assigned to other factors. -/
theorem expand_descriptors (span : ℕ) (pos : 0<span) (origin : Fin S → Fin N)
    (bucket : Fin S → Fin L) (quotient : ∀ j, (bucket j).val=j.val/span)
    (f : Fin N) (descriptor : List (Fin L)) (ordered : descriptor.Pairwise (· < ·))
    (membership : ∀ j, bucket j ∈ descriptor ↔ origin j=f) :
    descriptor.flatMap (fun b => blockBits S span b.val)=intervalBits origin f := by
  have mem (j : Fin S) : j ∈ descriptor.flatMap (fun b => blockBits S span b.val) ↔ origin j=f := by
    constructor
    · intro h
      obtain ⟨b,hb,hj⟩ := List.mem_flatMap.mp h
      have eqn : bucket j=b := Fin.ext ((quotient j).trans ((blockBits_mem pos j).mp hj))
      exact (membership j).mp (eqn.symm ▸ hb)
    · intro h
      exact List.mem_flatMap.mpr ⟨bucket j,(membership j).mpr h,
        (blockBits_mem pos j).mpr (quotient j).symm⟩
  have order' : (descriptor.flatMap (fun b => blockBits S span b.val)).Pairwise (· < ·) := by
    apply List.pairwise_flatMap.mpr
    refine ⟨fun b _ => blockBits_sorted ..,?_⟩
    refine ordered.imp fun {a b} lt x hx y hy => ?_
    have xq := (blockBits_mem pos x).mp hx
    have yq := (blockBits_mem pos y).mp hy
    by_contra! bad
    have r := Nat.div_le_div_right (show y.val≤x.val from bad) (c:=span)
    rw [xq,yq] at r
    exact (Nat.not_le_of_lt lt) r
  exact List.Subset.antisymm_of_pairwise order' ((List.pairwise_lt_finRange S).filter _)
    (fun j h => mem_intervalBits.mpr ((mem j).mp h))
    (fun j h => (mem j).mpr (mem_intervalBits.mp h))

end Hierarchy.FactorPinIntervals

end OAI
