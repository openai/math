import OAI.Computability.BorderVNP.PackedInheritedSeedPacket
import OAI.Computability.BorderVNP.PackedFrozenTapeRows

/-! # Scalar locations of the immutable main birth records

The count at word zero precedes the payload. A record's first scalar follows
all words of the preceding records, and its finite column selects the exact
relocation tag and expression from the immutable template.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Birth

open BankPacket BankJoint Word CellSparse Shortening.StaticRows Crossing ParseBatchSort
open scoped Classical

private theorem tape_split {I : Type*} (rs : List (RecordCode I)) (r : Fin rs.length) :
    tape rs = .const rs.length :: ((rs.take r.val).flatMap RecordCode.words ++
      (rs[r].words ++ (rs.drop (r.val+1)).flatMap RecordCode.words)) := by
  have h := congrArg (List.flatMap RecordCode.words) (List.take_append_drop r.val rs).symm
  rw [List.flatMap_append,List.drop_eq_getElem_cons r.isLt,List.flatMap_cons] at h
  exact congrArg (List.cons (.const rs.length)) h

/-- Word index of the indicated scalar in the full length-prefixed main-packet tape. -/
def wordIndex {I : Type*} (rs : List (RecordCode I)) (r : Fin rs.length) (i : Fin rs[r].words.length) :
    Fin (tape rs).length :=
  ⟨((rs.take r.val).flatMap RecordCode.words).length+i.val+1,by
    rw [tape_split rs r]
    simp only [List.length_cons,List.length_append]
    have := i.isLt
    omega⟩

/-- This finite index reads the indicated word of that record, with every prefix and tag included. -/
theorem wordIndex_read {I : Type*} (rs : List (RecordCode I)) (r : Fin rs.length) (i : Fin rs[r].words.length) :
    (tape rs)[wordIndex rs r i] = rs[r].words[i] := by
  apply Option.some.inj
  change some (tape rs)[(wordIndex rs r i).val] = some rs[r].words[i.val]
  rw [←List.getElem?_eq_getElem (wordIndex rs r i).isLt,←List.getElem?_eq_getElem i.isLt]
  change (tape rs)[((rs.take r.val).flatMap RecordCode.words).length+i.val+1]? = rs[r].words[i.val]?
  rw [tape_split rs r,List.getElem?_cons_succ,List.getElem?_append_right (Nat.le_add_right _ _),
    Nat.add_sub_cancel_left,List.getElem?_append_left i.isLt]

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m) (first : Fin D × Bool)
    (S : Type*) [Fintype S]

/-- All record slots of the immutable main bank at each seed site. -/
noncomputable abbrev Row := Σ sv : S × TemplateSite e, Fin (rows e first sv.2).length

/-- The single stored record expression at its finite template row. -/
noncomputable def code (r : Row e first S) : RecordCode (Operands e r.1.2) := (rows e first r.1.2)[r.2]

/-- Enumeration of each site's main records in source order, within one complete seed rectangle. -/
noncomputable def rowList : List (Row e first S) :=
  (List.ofFn (Fintype.equivFin (S × TemplateSite e)).symm).flatMap
    (fun z => List.ofFn (fun i : Fin (rows e first z.2).length => (⟨z,i⟩ : Row e first S)))

/-- Relocation roles are fixed by the actual immutable seed schema. -/
noncomputable def fieldTags (r : Row e first S) : List Kind := (markedCode (code e first S r)).map Prod.fst

omit [Fintype S] in
private theorem columns (r : Row e first S) : (fieldTags e first S r).length = (code e first S r).words.length := by
  rw [← markedCode_words (code e first S r),List.length_map,fieldTags,List.length_map]

/-- Select exactly the emitted binary scalar of this immutable record. -/
noncomputable def scalar (r : Row e first S) (i : Fin (fieldTags e first S r).length) : Output e first :=
  ⟨r.1.2,wordIndex (rows e first r.1.2) r.2 (Fin.cast (columns e first S r) i)⟩

/-- The frozen record is stored at the exact original compiler word indices. -/
noncomputable def schema (w : ℕ) : Schema (Row e first S) (S × Output e first × Fin w) where
  rows := rowList e first S
  tags := fieldTags e first S
  width _ := w
  pin r i b := (r.1.1,scalar e first S r i,b)

/-- Every scalar selected from the public word frame has its correct fixed relocation role. -/
theorem read {w d : ℕ} (x : Pins (Row e first S) (S × Output e first × Fin w) d → Bool)
    (raw : S → Raw e → ℕ) (h : ∀ a z, value (fun j => x (.inr (a,z,j))) =
      (Packet.fieldList Packet.record (emitted e first (raw a) z.1))[z.2.val]?.getD 0)
    (r : Row e first S) :
    (schema e first S w).read x r =
      marked ((code e first S r).read (fun i => word e (raw r.1.1) (pin e r.1.2 i))) := by
  let vals := fun i => word e (raw r.1.1) (pin e r.1.2 i)
  let c := code e first S r
  let codes := markedCode c
  rw [← markedCode_eval]
  unfold Schema.read
  apply List.ext_getElem
  · simp [schema,fieldTags]
  · intro i hi hj
    let j : Fin (fieldTags e first S r).length := ⟨i,by simpa [schema] using hi⟩
    let k := Fin.cast (columns e first S r) j
    let z := scalar e first S r j
    have hh := (h r.1.1 z).trans (expr_packet e first (raw r.1.1) z).symm
    have hc : expr e first z = c.words[k] := wordIndex_read _ _ _
    have hw : c.words[k] = (codes[i]'(by simpa only [List.length_map,codes,c] using hj)).2 := by
      have hmap := markedCode_words c
      simpa [codes,k,j] using (List.getElem_of_eq hmap.symm (i := i) (by exact k.isLt))
    have hs : value (fun b => x (.inr (r.1.1,z,b))) = (codes[i]'(by simpa only [List.length_map,codes,c] using hj)).2.eval vals :=
      hh.trans (congrArg (WidthExpr.eval vals) (hc.trans hw))
    rw [List.getElem_ofFn,List.getElem_map]
    apply Prod.ext
    · simp [schema,fieldTags]
    · exact hs

end Packing.Inherited.FrozenTape.Birth

end BorderVNP
end Computability
end OAI
