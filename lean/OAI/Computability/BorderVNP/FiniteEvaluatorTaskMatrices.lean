import OAI.Computability.BorderVNP.FiniteEvaluatorTaskCubeChoices

/-! # Real preparatory report tapes indexed by finite scalar matrices

Every owned cell supplies all field-label digits in the bit-major order
read by the actual scalar routine. Splitting at the stored cell lengths
identifies this family of matrices with the full native report tape.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.TaskReadback

open FiniteScalarRounds
open private shape bits_rebit capacity_cons from OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReportsInverse

variable (F : Type*) [Fintype F] (d : ℕ)

/-- A bit for every owned row, field label and binary place. -/
abbrev Matrices (rows : List Reports.Row) := Fin rows.length → Index F → Fin d → Bool

private def encodeRows (rows : List Reports.Row) (c : Matrices F d rows) : List Bool :=
  (List.ofFn fun i => stream F (c i)).flatten

private theorem fields_read (rows : List Reports.Row) (sized : ∀ i : Fin rows.length, rows[i].bits.length=d*Fintype.card F)
    (c : Matrices F d rows) : ∀ i : Fin rows.length,
      ((Reports.rebit rows (encodeRows F d rows c))[i.val]'(by simp)).bits = stream F (c i) := by
  induction rows with
  | nil => exact fun i => Fin.elim0 i
  | cons r rs ih =>
    let rest : Matrices F d rs := fun j => c j.succ
    have head : r.bits.length=(stream F (c 0)).length := (sized 0).trans (stream_length F (c 0)).symm
    have code : encodeRows F d (r::rs) c=stream F (c 0) ++ encodeRows F d rs rest := by
      unfold encodeRows
      rw [List.ofFn_succ,List.flatten_cons]
    have tail := ih (fun i => sized i.succ) rest
    intro i
    rw [code]
    simp only [Reports.rebit,head,List.take_left,List.drop_left]
    exact Fin.cases rfl (fun j => tail j) i

private theorem encode_length (rows : List Reports.Row) (sized : ∀ i : Fin rows.length, rows[i].bits.length=d*Fintype.card F)
    (c : Matrices F d rows) : (encodeRows F d rows c).length=Reports.capacity rows := by
  induction rows with
  | nil => rfl
  | cons r rs ih =>
    have head := sized 0
    have rest := ih (fun i => sized i.succ) (fun j => c j.succ)
    change r.bits.length = d*Fintype.card F at head
    rw [capacity_cons]
    unfold encodeRows
    rw [List.ofFn_succ,List.flatten_cons,List.length_append,stream_length,head]
    exact congrArg (d*Fintype.card F+·) rest

/-- Every tuple of field report matrices has one chronological tape and every
legal tape comes from exactly one such tuple. -/
noncomputable def matrixEquiv (rows : List Reports.Row)
    (sized : ∀ i : Fin rows.length, rows[i].bits.length=d*Fintype.card F) :
    Matrices F d rows ≃ ReportTape rows := by
  let pack (c : Matrices F d rows) : ReportTape rows := ⟨encodeRows F d rows c,encode_length F d rows sized c⟩
  apply Equiv.ofBijective pack
  constructor
  · intro a b same
    have bits : encodeRows F d rows a=encodeRows F d rows b := congrArg Subtype.val same
    funext i
    have w := fields_read F d rows sized a i
    rw [bits,fields_read F d rows sized b i] at w
    obtain ⟨c,_,unique⟩ := Reports.decode_unique F d (stream F (a i)) (stream_length ..)
    exact (unique _ rfl).trans (unique _ w).symm
  · intro bs
    let source := Reports.rebit rows bs.val
    have len : source.length=rows.length := Reports.rebit_length ..
    let values (i : Fin rows.length) := (source[i.val]'(by rw [len]; exact i.isLt)).bits
    have right (i : Fin rows.length) : (values i).length=d*Fintype.card F :=
      (shape rows bs.val bs.property.symm.le i).2.2.2.symm.trans (sized i)
    let c : Matrices F d rows := fun i => (Reports.decode_unique F d (values i) (right i)).exists.choose
    have live (i : Fin rows.length) : stream F (c i)=values i := (Reports.decode_unique F d (values i) (right i)).exists.choose_spec
    refine ⟨c,Subtype.ext ?_⟩
    change (List.ofFn fun i => stream F (c i)).flatten=bs.val
    have maps : (List.ofFn values)=source.map Reports.Row.bits := by
      apply List.ext_getElem (by simp [len])
      intro j hj hk
      simp only [List.getElem_ofFn,List.getElem_map,values]
    simp_rw [live]
    rw [maps,← List.flatMap_def,show source=Reports.rebit rows bs.val from rfl,bits_rebit,List.take_of_length_le bs.property.le]

/-- Reading the corresponding row in the physical tape recovers the supplied
matrix in the exact order seen by the scalar routine. -/
theorem matrixEquiv_read (rows : List Reports.Row)
    (sized : ∀ i : Fin rows.length, rows[i].bits.length=d*Fintype.card F) (c : Matrices F d rows) (i : Fin rows.length) :
    ((Reports.rebit rows (matrixEquiv F d rows sized c).val)[i.val]'(by simp)).bits=stream F (c i) :=
  fields_read F d rows sized c i

end FiniteEvaluator.TaskReadback

end BorderVNP
end Computability
end OAI
