import OAI.Computability.BorderVNP.CellPacketGeometryLiveOwners
import OAI.Computability.BorderVNP.CellPacketGeometrySpanShape

/-! # Branch-independent descriptor operands of the live geometry frame

The row labels depend on the current site placement. The first/last word indices,
private operand pins, and blank reservations are the same for every placement and
every scalar input to a fixed record-code template.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

variable {N M : ℕ} {Q : Type}

/-- Transport the fixed public ordinals of a reference across an equality of
word-bank capacities; the private slot operands are retained verbatim. -/
def Reference.reindex (h : N=M) : Reference N Q → Reference M Q
  | .words a b => .words (a.cast h) (b.cast h)
  | .site q => .site q
  | .blank => .blank

/-- The public-index transport is the ordinary type cast along the size equality. -/
theorem Reference.reindex_eq_cast (h : N=M) (r : Reference N Q) :
    r.reindex h = cast (congrArg (fun n => Reference n Q) h) r := by
  subst M
  cases r <;> rfl

namespace LiveWords

open CellSparse CellSparse.Packet Packing.BankPacket SiteWords

variable {E I Orig : Type} {s C : ℕ}

/-- The public bank capacity equals the same number of source pins on every branch. -/
theorem Template.wordCapacity (T : Template E I Orig s C) (owner : Fin s → Fin C) (args : E → ℕ)
    (fields : Fin s → I → ℕ) : (T.directory owner args fields).words.length = T.atoms.length := by
  simpa only [List.length_map] using (congrArg List.length (T.atoms_eval owner args fields)).symm

private theorem reindex_span {raw raw' : List (Fin C × ℕ)} {pos pos' n n' K : ℕ} {a b : Fin C}
    (sp : Span raw a pos n) (sp' : Span raw' b pos' n')
    (h : raw.length=K) (h' : raw'.length=K) (first : sp.first.ordinal.val=sp'.first.ordinal.val)
    (last : sp.last.ordinal.val=sp'.last.ordinal.val) :
    (sp.reference (E := Q)).reindex h = sp'.reference.reindex h' :=
  congrArg₂ Reference.words (Fin.ext first) (Fin.ext last)

private theorem original_ref (D : Directory (Fin s) Orig C) (pin : Orig → Q)
    (i : Fin D.sites.length) (j : Fin (D.boxes D.sites[i.val]).length) (q : Orig)
    (eqn : (D.boxes D.sites[i.val])[j.val] = Sum.inr q) : D.boxReference pin i j = .site (pin q) := by
  unfold Directory.boxReference
  split <;> rename_i e <;> rw [eqn] at e <;> cases e
  rfl

private theorem known_ref (D : Directory (Fin s) Orig C) (pin : Orig → Q)
    (i : Fin D.sites.length) (j : Fin (D.boxes D.sites[i.val]).length) (fs : List Factor)
    (eqn : (D.boxes D.sites[i.val])[j.val] = Sum.inl fs) :
    D.boxReference pin i j = (D.boxSpan i j fs eqn).reference := by
  unfold Directory.boxReference
  split <;> rename_i e <;> rw [eqn] at e <;> cases e
  rfl

private theorem report_length (T : Template E I Orig s C) (args : E → ℕ) (c : Fin C) :
    (fieldList vector ((T.reports c).map (List.map args))).length =
      1+((T.reports c).map (fun v => v.length+1)).sum := by
  simp [fieldList,vector,List.length_flatMap,List.map_map,Function.comp_def,Nat.add_comm]

private theorem row_length (T : Template E I Orig s C) (fields : Fin s → I → ℕ) (i : Fin s) :
    (((T.format i).map (RecordCode.read (fields i))).flatMap record).length = (tape (T.format i)).length-1 := by
  have h := congrArg List.length (tape_eval (fields i) (T.format i))
  simp only [fieldList,List.length_map,List.length_cons] at h
  omega

private theorem reference_payloads (D : Directory (Fin s) Orig C) (pin : Orig → Q)
    {K : ℕ} (h : D.words.length=K) :
    (D.referenceRows pin).map (fun x => x.2.reindex h) =
      List.ofFn (fun c => (D.headerSpan c).reference.reindex h) ++
      (List.ofFn (fun i : Fin D.sites.length => List.ofFn (fun j =>
        (D.boxReference pin i j).reindex h))).flatten ++
      (List.ofFn fun c => [(D.tailSpan c).reference.reindex h,.blank,.blank,.blank]).flatten := by
  simp only [Directory.referenceRows,List.map_append,List.map_flatten,List.map_ofFn,Function.comp_def,
    Directory.siteReferences,List.map_cons,List.map_nil,Reference.reindex,Span.reference]

/-- All public chunk intervals and private operand pins agree across every two
evaluations of the same template. The proof computes their raw source offsets. -/
theorem Template.reference_payloads_eq (T : Template E I Orig s C) (pin : Orig → Q)
    (o o' : Fin s → Fin C) (a a' : E → ℕ) (f f' : Fin s → I → ℕ) :
    ((T.directory o a f).referenceRows pin).map
      (fun x => x.2.reindex (T.wordCapacity o a f)) =
    ((T.directory o' a' f').referenceRows pin).map
      (fun x => x.2.reindex (T.wordCapacity o' a' f')) := by
  let D := T.directory o a f
  let G := T.directory o' a' f'
  let h := T.wordCapacity o a f
  let h' := T.wordCapacity o' a' f'
  have heads (c : Fin C) : (D.headerSpan c).reference.reindex h =
      ((G.headerSpan c).reference (E := Q)).reindex h' :=
    reindex_span _ _ _ _ ((D.header_ordinals c).1.trans (G.header_ordinals c).1.symm)
      ((D.header_ordinals c).2.trans (G.header_ordinals c).2.symm)
  have boxes (i : Fin D.sites.length) (j : Fin (D.boxes D.sites[i.val]).length) :
      (D.boxReference pin i j).reindex h = (G.boxReference pin i j).reindex h' := by
    cases eqn : (D.boxes D.sites[i.val])[j.val] with
    | inr q => rw [original_ref D pin i j q eqn,original_ref G pin i j q eqn]; rfl
    | inl fs =>
      rw [known_ref D pin i j fs eqn,known_ref G pin i j fs eqn]
      apply reindex_span
      · exact (D.box_ordinals i j fs eqn).1.trans (G.box_ordinals i j fs eqn).1.symm
      · exact (D.box_ordinals i j fs eqn).2.trans (G.box_ordinals i j fs eqn).2.symm
  have tails (c : Fin C) : (D.tailSpan c).reference.reindex h =
      ((G.tailSpan c).reference (E := Q)).reindex h' := by
    apply reindex_span
    · exact (D.tail_ordinals c).1.trans (G.tail_ordinals c).1.symm
    · rw [(D.tail_ordinals c).2,(G.tail_ordinals c).2]
      simp only [D,G,Directory.reportOffset,Template.directory,row_length,report_length]
  rw [reference_payloads,reference_payloads]
  change (List.ofFn (fun c => (D.headerSpan c).reference.reindex h) ++
    (List.ofFn (fun i => List.ofFn (fun j => (D.boxReference pin i j).reindex h))).flatten ++
    (List.ofFn (fun c => [(D.tailSpan c).reference.reindex h,.blank,.blank,.blank])).flatten) = _
  simp only [heads,boxes,tails]
  rfl

/-- Descriptor operand table chosen once, before site labels or word values are
known. Any fixed initial placement gives the same list. -/
def Template.fixedReferences (T : Template E I Orig s C) (baseOwner : Fin s → Fin C) (pin : Orig → Q) :
    List (Reference T.atoms.length Q) :=
  ((T.directory baseOwner (fun _ => 0) (fun _ _ => 0)).referenceRows pin).map fun x =>
    x.2.reindex (T.wordCapacity baseOwner (fun _ => 0) (fun _ _ => 0))

/-- The fixed operands denote the true linked public intervals of every input. -/
theorem Template.fixedReferences_eq (T : Template E I Orig s C) (baseOwner owner : Fin s → Fin C)
    (pin : Orig → Q) (args : E → ℕ) (fields : Fin s → I → ℕ) :
    T.fixedReferences baseOwner pin = ((T.directory owner args fields).referenceRows pin).map fun x =>
      x.2.reindex (T.wordCapacity owner args fields) :=
  T.reference_payloads_eq pin baseOwner owner _ _ _ _

/-- The two static descriptor columns have the same length. -/
theorem Template.fixedReferences_length (T : Template E I Orig s C) (baseOwner : Fin s → Fin C)
    (pin : Orig → Q) : (T.fixedReferences baseOwner pin).length = T.chunkLabels.length := by
  have eqn := congrArg List.length (T.chunkLabels_eval baseOwner (fun _ => 0) (fun _ _ => 0) pin)
  simpa only [Template.fixedReferences,List.length_map] using eqn.symm

/-- Raw row count on any branch equals the static descriptor-label count. -/
theorem Template.referenceCapacity (T : Template E I Orig s C) (owner : Fin s → Fin C)
    (pin : Orig → Q) (args : E → ℕ) (fields : Fin s → I → ℕ) :
    T.chunkLabels.length = ((T.directory owner args fields).referenceRows pin).length := by
  simpa only [List.length_map] using congrArg List.length (T.chunkLabels_eval owner args fields pin)

/-- Pointwise identification of the hardwired descriptor operand used in the physical
gate table with the reference proved linked on the actual runtime branch. -/
theorem Template.fixedReference_get (T : Template E I Orig s C) (baseOwner owner : Fin s → Fin C)
    (pin : Orig → Q) (args : E → ℕ) (fields : Fin s → I → ℕ) (i : Fin T.chunkLabels.length) :
    let D := T.directory owner args fields
    let nEq := (T.wordCapacity owner args fields).symm
    let mEq := T.referenceCapacity owner pin args fields
    cast (congrArg (fun n => Reference n Q) nEq)
      ((T.fixedReferences baseOwner pin).get (i.cast (T.fixedReferences_length baseOwner pin).symm)) =
      ((D.referenceRows pin).get (i.cast mEq)).2 := by
  intro D nEq mEq
  have e := List.getElem_of_eq (T.fixedReferences_eq baseOwner owner pin args fields)
    (i.cast (T.fixedReferences_length baseOwner pin).symm).isLt
  simp only [List.getElem_map,Reference.reindex_eq_cast,Fin.val_cast] at e
  simp only [List.get_eq_getElem,Fin.val_cast,e,cast_cast]
  rfl

end LiveWords
end CellPacketGeometry

end BorderVNP
end Computability
end OAI
