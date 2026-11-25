import OAI.Computability.NearSquareRoot.CommonAlphabetNumbering
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.Dedup
import Mathlib.Data.List.NodupEquivFin

/-! # Addresses of compiler locations in a finite list

Different occurrences of the same compiler location denote one state. An injective
encoding of locations gives a numbering by positions in the deduplicated list of
codes. Both lookup directions depend primitively recursively on that list.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.SyntaxAddress

open CommonAlphabet

variable {T N : Type} [DecidableEq N]

def size (codes : List N) : ℕ := codes.dedup.length

def rank (codes : List N) (n : N) : ℕ := codes.dedup.idxOf n

def read (codes : List N) (i : ℕ) : Option N := codes.dedup[i]?

theorem rank_lt_iff {codes : List N} {n : N} : rank codes n < size codes ↔ n ∈ codes := by
  simp [rank, size, List.idxOf_lt_length_iff]

theorem size_le_length (codes : List N) : size codes ≤ codes.length :=
  (List.dedup_sublist codes).length_le

/-- Recover the original compiler location at the first occurrence of its code. -/
private def memberEquiv (encode : T ↪ N) (l : List T) :
    {x // x ∈ l} ≃ {n // n ∈ (l.map encode).dedup} where
  toFun x := ⟨encode x.val, List.mem_dedup.mpr (List.mem_map.mpr ⟨_, x.property, rfl⟩)⟩
  invFun n := by
    let i := (l.map encode).idxOf n.val
    have hi : i < (l.map encode).length := List.idxOf_lt_length_of_mem (List.mem_dedup.mp n.property)
    have hi' : i < l.length := by simpa only [List.length_map] using hi
    exact ⟨l[i], List.getElem_mem hi'⟩
  left_inv x := by
    apply Subtype.ext
    apply encode.injective
    rw [List.getElem_map_rev encode, List.getElem_idxOf]
  right_inv n := by
    apply Subtype.ext
    dsimp only
    rw [List.getElem_map_rev encode, List.getElem_idxOf]

def numbering (encode : T ↪ N) (l : List T) : Numbering {x // x ∈ l} :=
  let codes := l.map encode
  ⟨size codes, (memberEquiv encode l).trans ((List.nodup_dedup codes).getEquiv _).symm⟩

@[simp] theorem numbering_size (encode : T ↪ N) (l : List T) :
    (numbering encode l).size = size (l.map encode) := rfl

@[simp] theorem numbering_rank (encode : T ↪ N) (l : List T) (x : {x // x ∈ l}) :
    ((numbering encode l).equiv x).val = rank (l.map encode) (encode x.val) := rfl

theorem numbering_read (encode : T ↪ N) (l : List T) (i : Fin (numbering encode l).size) :
    read (l.map encode) i.val = some (encode (((numbering encode l).equiv.symm i).val)) := by
  obtain ⟨x, rfl⟩ := (numbering encode l).equiv.surjective i
  simp only [Equiv.symm_apply_apply, numbering_rank, read, rank]
  rw [List.getElem?_eq_getElem, List.getElem_idxOf]
  exact (rank_lt_iff.mpr (List.mem_map.mpr ⟨x.val, x.property, rfl⟩))

variable [Primcodable N]

theorem primrec_dedup : Primrec (List.dedup : List N → List N) := by
  let step (p : N × List N) := if p.2.idxOf p.1 < p.2.length then p.2 else p.1 :: p.2
  have hs : Primrec step := Primrec.ite
    (Primrec.nat_lt.comp (Primrec.list_idxOf.comp Primrec.fst Primrec.snd)
      (Primrec.list_length.comp Primrec.snd)) Primrec.snd Primrec.list_cons
  have h := Primrec.list_foldr (α := List N) Primrec.id (Primrec.const ([] : List N))
    (hs.comp Primrec.snd).to₂
  apply h.of_eq
  intro l
  change l.foldr (fun b s => step (b, s)) [] = l.dedup
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.foldr_cons, ih, List.dedup_cons']
    simp only [step, List.idxOf_lt_length_iff]

theorem primrec_size : Primrec (size (N := N)) := Primrec.list_length.comp primrec_dedup

theorem primrec_rank : Primrec₂ (rank (N := N)) :=
  (Primrec.list_idxOf.comp Primrec.snd (primrec_dedup.comp Primrec.fst)).to₂

theorem primrec_read : Primrec₂ (read (N := N)) :=
  (Primrec.list_getElem?.comp (primrec_dedup.comp Primrec.fst) Primrec.snd).to₂

end Generator.SyntaxAddress

end NearSquareRoot
end Computability
end OAI
