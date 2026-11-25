import OAI.Computability.BorderVNP.CellPacketGeometryRegroup

/-! # Invariance of public descriptor references under stable site-major grouping -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteWords

open CellSparse CellSparse.Packet LiveWords
open private reindex_span original_ref known_ref reference_payloads
  from OAI.Computability.BorderVNP.CellPacketGeometryFixedReferences
open private referenceOwners from OAI.Computability.BorderVNP.CellPacketGeometryLiveOwners

variable {s C : ℕ} {Orig E : Type}
variable (D : Directory (Fin s) Orig C) (anchor : Fin s → Fin s)
variable (allSites : D.sites = List.finRange s) (owns : ∀ i, D.owner (anchor i)=D.owner i)

include allSites owns in
/-- Sorting only the record block preserves the actual source capacity. -/
theorem Directory.regroup_wordCapacity : (D.regroup anchor).words.length = D.words.length := by
  obtain ⟨h,b,c,r⟩ := D.regroup_sections anchor allSites owns
  simp only [Directory.words,List.length_append,h,b,c,r,D.regroup_record_length anchor allSites]

/-- Every native descriptor belongs to the same real cell after the record sort,
including opaque private boxes and the three supplemental reservations. -/
theorem Directory.regroup_owners (pin : Orig → E) :
    ((D.regroup anchor).referenceRows pin).map Prod.fst = (D.referenceRows pin).map Prod.fst := by
  rw [referenceOwners,referenceOwners]
  rfl

include allSites in
/-- Stable reordering preserves every hardwired reference ordinal, the private
slot operand, the owner labels, and the numerical descriptor array capacity. -/
theorem Directory.regroup_refPayloads (pin : Orig → E) {K : ℕ} (h : D.words.length=K)
    (g : (D.regroup anchor).words.length=K) :
    (D.referenceRows pin).map (fun a => a.2.reindex h) =
      ((D.regroup anchor).referenceRows pin).map (fun a => a.2.reindex g) := by
  let G := D.regroup anchor
  have heads (c : Fin C) : (D.headerSpan c).reference.reindex h = ((G.headerSpan c).reference (E := E)).reindex g :=
    reindex_span _ _ _ _ ((D.header_ordinals c).1.trans (G.header_ordinals c).1.symm)
      ((D.header_ordinals c).2.trans (G.header_ordinals c).2.symm)
  have boxes (i : Fin D.sites.length) (j : Fin (D.boxes D.sites[i.val]).length) :
      (D.boxReference pin i j).reindex h = (G.boxReference pin i j).reindex g := by
    cases eqn : (D.boxes D.sites[i.val])[j.val] with
    | inr a =>
      rw [original_ref D pin i j a eqn,original_ref G pin i j a eqn]
      rfl
    | inl fs =>
      rw [known_ref D pin i j fs eqn,known_ref G pin i j fs eqn]
      exact reindex_span _ _ _ _ ((D.box_ordinals i j fs eqn).1.trans (G.box_ordinals i j fs eqn).1.symm)
        ((D.box_ordinals i j fs eqn).2.trans (G.box_ordinals i j fs eqn).2.symm)
  have lengths : (G.sites.map (fun i => ((G.rows i).flatMap record).length)).sum =
      (D.sites.map (fun i => ((D.rows i).flatMap record).length)).sum := by
    simpa only [Directory.recordRows,siteRows_length] using D.regroup_record_length anchor allSites
  have tails (c : Fin C) : (D.tailSpan c).reference.reindex h = ((G.tailSpan c).reference (E := E)).reindex g := by
    apply reindex_span
    · exact (D.tail_ordinals c).1.trans (G.tail_ordinals c).1.symm
    · rw [(D.tail_ordinals c).2,(G.tail_ordinals c).2]
      simp only [Directory.reportOffset,lengths]
      rfl
  rw [reference_payloads,reference_payloads]
  change (List.ofFn (fun c => (D.headerSpan c).reference.reindex h) ++
    (List.ofFn (fun i => List.ofFn (fun j => (D.boxReference pin i j).reindex h))).flatten ++
    (List.ofFn (fun c => [(D.tailSpan c).reference.reindex h,.blank,.blank,.blank])).flatten) = _
  simp only [heads,boxes,tails]
  rfl

end CellPacketGeometry.SiteWords

namespace CellPacketGeometry.LiveWords

open SiteWords
variable {s C : ℕ} {E I Orig Q : Type}

/-- The physical descriptor and private-slot gate table from the original fixed
template therefore also agrees exactly with the final site-major physical directory. -/
theorem Template.fixedReference_regroup (T : Template E I Orig s C) (baseOwner owner : Fin s → Fin C)
    (pin : Orig → Q) (args : E → ℕ) (fields : Fin s → I → ℕ) (anchor : Fin s → Fin s)
    (cell : ∀ i, owner (anchor i) = owner i) (i : Fin T.chunkLabels.length) :
    let D := T.directory owner args fields
    let G := D.regroup anchor
    let nEq := ((D.regroup_wordCapacity anchor rfl cell).trans (T.wordCapacity owner args fields)).symm
    let mEq : T.chunkLabels.length = (G.referenceRows pin).length := by
      simpa only [List.length_map] using congrArg List.length
        ((T.chunkLabels_eval owner args fields pin).trans (D.regroup_owners anchor pin).symm)
    cast (congrArg (fun n => Reference n Q) nEq)
      ((T.fixedReferences baseOwner pin).get (i.cast (T.fixedReferences_length baseOwner pin).symm)) =
        ((G.referenceRows pin).get (i.cast mEq)).2 := by
  intro D G nEq mEq
  have eqn := (T.fixedReferences_eq baseOwner owner pin args fields).trans
    (D.regroup_refPayloads anchor rfl pin (T.wordCapacity owner args fields) nEq.symm)
  have word := List.getElem_of_eq eqn (i.cast (T.fixedReferences_length baseOwner pin).symm).isLt
  simp only [List.getElem_map,Reference.reindex_eq_cast,Fin.val_cast] at word
  simp only [List.get_eq_getElem,Fin.val_cast,word,cast_cast]
  rfl

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI
