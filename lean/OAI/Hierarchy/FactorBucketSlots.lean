import OAI.Hierarchy.FactorBucketInputs
import OAI.Hierarchy.FactorPinPrefix

namespace OAI
/-! # Turning the native bucket base into the exact selected data pin -/

namespace Hierarchy.FactorPinIntervals

variable {T : Type} {S N L d span : ℕ} (P : Layout T S N d) (pos : 0 < span)
    (bucket : Fin S → Fin L) (quotient : ∀ j, (bucket j).val=j.val/span)
    (desc : Fin N → List (Fin L)) (sorted : ∀ f, (desc f).Pairwise (· < ·))
    (admits : ∀ f j, bucket j ∈ desc f ↔ P.origin j=f)

include pos quotient in
private theorem within_block (j : Fin S) :
    (blockBits S span (bucket j).val).idxOf j=j.val%span := by
  let b := (bucket j).val
  have div := (quotient j).symm
  have dec := Nat.mod_add_div j.val span
  rw [div,Nat.mul_comm span (bucket j).val] at dec
  have js := j.isLt
  let i : Fin (bucketLength S span b) := ⟨j.val%span,lt_min (Nat.mod_lt _ pos) (by dsimp [b];omega)⟩
  have eqn : blockBit S span b i=j := by
    apply Fin.ext
    change (bucket j).val*span+j.val%span=j.val
    exact (Nat.add_comm _ _).trans dec
  have nd : (blockBits S span b).Nodup :=
    (blockBits_sorted S span b).imp (fun {_ _} h => ne_of_lt h)
  have bound : i.val < (blockBits S span b).length := by simp
  have idx := nd.idxOf_getElem i.val bound
  have val : (blockBits S span b)[i.val]=j := by simpa [blockBits] using eqn
  rw [val] at idx
  exact idx

include pos quotient sorted in
private theorem prev_missing {f : Fin N} {pre post : List (Fin L)} {b : Fin L}
    (split : desc f=pre++b::post) (j : Fin S) (number : bucket j=b) :
    j ∉ pre.flatMap (fun u => blockBits S span u.val) := by
  intro hj
  obtain ⟨b',hb',inBlock⟩ := List.mem_flatMap.mp hj
  have same : b'=b := Fin.ext (((blockBits_mem pos j).mp inBlock).symm.trans
    ((quotient j).symm.trans (congrArg Fin.val number)))
  have nd := (sorted f).imp (fun {_ _} h => ne_of_lt h)
  rw [split] at nd
  exact (List.nodup_append.mp nd).2.2 b' hb' b List.mem_cons_self same

include pos quotient sorted admits in
/-- The first pass charges preceding occurrences of the same tick. The second
pass charges preceding physical buckets of the same factor. A word lookup
and one remainder recover the exact mathematical slot. -/
theorem slot_at_bucket {t : T} {f : Fin N} {preF postF : List (Fin N)}
    {preB postB : List (Fin L)} (j : Fin S) (own : P.origin j=f)
    (factorAt : P.rows t=preF++f::postF)
    (bucketAt : desc f=preB++bucket j::postB) :
    (P.slot j).val = (P.header t).length+(stream P.origin preF).length +
      (preB.map (fun b => bucketLength S span b.val)).sum + j.val%span := by
  rw [P.slot_prefix factorAt own,←expand_descriptors span pos P.origin bucket quotient
    f (desc f) (sorted f) (admits f),bucketAt,List.flatMap_append,List.flatMap_cons]
  rw [List.idxOf_append_of_notMem (prev_missing pos bucket quotient desc sorted bucketAt j rfl)]
  have found := (blockBits_mem pos j (b:=(bucket j).val)).mpr (quotient j).symm
  rw [List.idxOf_append_of_mem found,within_block pos bucket quotient]
  simp only [List.length_flatMap,blockBits_length]
  omega

end Hierarchy.FactorPinIntervals

end OAI
