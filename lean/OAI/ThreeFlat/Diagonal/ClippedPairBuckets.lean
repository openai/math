import OAI.ThreeFlat.Diagonal.PackedBucketBijection
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Original lane buckets and the owner of every external bit -/

namespace ThreeFlat.Diagonal.ClippedPairBuckets

open HistoryContraction
variable {I : Type*} {lanes C a : ℕ}

def row (site : Fin lanes → I) (total span : ℕ) (i : Fin lanes) : Bucket I :=
  ⟨site i,min total (i.val*span),min total ((i.val+1)*span)⟩

def rows (site : Fin lanes → I) (total span : ℕ) := List.ofFn (row site total span)

theorem bounded (site : Fin lanes → I) (total span : ℕ) (b : Bucket I)
    (hb : b∈rows site total span) : b.hi ≤ total := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
  exact Nat.min_le_left ..

theorem disjoint (site : Fin lanes → I) (total span : ℕ) (group : I → ℕ) :
    PackedBucketBijection.Disjoint group (rows site total span) := by
  apply List.pairwise_ofFn.mpr
  intro i j before _ x ilo ihi jlo jhi
  have step : (i.val+1)*span ≤ j.val*span := Nat.mul_le_mul_right _ before
  change x < min total ((i.val+1)*span) at ihi
  change min total (j.val*span) ≤ x at jlo
  exact (not_lt_of_ge jlo) (lt_of_lt_of_le ihi (min_le_min_left _ step))

def address (z : Fin C × Fin a) := z.1.val*a+z.2.val

theorem address_lt (z : Fin C × Fin a) : address z < C*a := by
  have step := Nat.mul_le_mul_right a z.1.isLt
  rw [Nat.succ_mul] at step
  have := z.2.isLt
  dsimp [address]
  omega

def lane (span : ℕ) (pos : 0<span) (fit : C*a≤lanes*span) (z : Fin C × Fin a) : Fin lanes :=
  ⟨address z/span,(Nat.div_lt_iff_lt_mul pos).mpr ((address_lt z).trans_le fit)⟩

theorem covered (site : Fin lanes → I) (span : ℕ) (pos : 0<span) (fit : C*a≤lanes*span) (z : Fin C × Fin a) :
    ∃ b∈rows site (C*a) span, b.lo ≤ address z ∧ address z < b.hi := by
  let i := lane span pos fit z
  refine ⟨row site (C*a) span i,List.mem_ofFn.mpr ⟨i,rfl⟩,?_,?_⟩
  · exact (Nat.min_le_right ..).trans (Nat.div_mul_le_self (address z) span)
  · exact lt_min (address_lt z) (by simpa only [i,lane,Nat.succ_mul] using Nat.lt_div_mul_add (a:=address z) pos)

theorem owner (site : Fin lanes → I) (span : ℕ) (pos : 0<span) (fit : C*a≤lanes*span)
    (z : Fin C × Fin a) (b : Bucket I) (hb : b∈rows site (C*a) span)
    (lo : b.lo≤address z) (hi : address z<b.hi) : b.site=site (lane span pos fit z) := by
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hb
  change min (C*a) (i.val*span) ≤ address z at lo
  change address z < min (C*a) ((i.val+1)*span) at hi
  have top := address_lt z
  have left : i.val*span ≤ address z := by omega
  have h₁ : i.val ≤ address z/span := (Nat.le_div_iff_mul_le pos).mpr left
  have h₂ : address z/span < i.val+1 := (Nat.div_lt_iff_lt_mul pos).mpr (hi.trans_le (Nat.min_le_right ..))
  exact congrArg site (Fin.ext (by change i.val=address z/span; omega))

end ThreeFlat.Diagonal.ClippedPairBuckets

end OAI
