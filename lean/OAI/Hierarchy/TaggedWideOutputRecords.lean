import OAI.Hierarchy.TaggedWideOutputSlices
import OAI.Hierarchy.TaggedWideReportedBonds

namespace OAI
/-! # Decoding the archive's actual common IDs onto the fixed terminal barrel -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open ProtocolStackContraction TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open scoped Classical

variable {n groups ports lanes : ℕ} (rows : Fin n→ProtocolRAMEmit.Row) (w m : ℕ)
    (id : Function.Injective fun i=>(rows i).link)
    (port : Bool→Fin n→Fin ports)
    (anchor : {i : Fin n // 0<pieces rows w i} × Bool ↪ Fin groups × Fin ports)
    (owner : ∀i s,(anchor (i,s)).1.val=(rows i.val).group)
    (pin : ∀i s,(anchor (i,s)).2=port s i.val)
    (reserved : ∀i,pieces rows w i≤lanes)
set_option quotPrecheck false in
local notation "R" => {i : Fin n // 0<pieces rows w i}
set_option quotPrecheck false in
local notation "T" => Fin (m+1)
set_option quotPrecheck false in
local notation "width" => fun t:T=>⌈dyadic t.val*w⌉₊
set_option quotPrecheck false in
local notation "bits" => fun r:R=>(rows r.val).width
set_option quotPrecheck false in
local notation "kind" => fun r:R=>(⟨widthIndex m ((rows r.val).width/(w:ℝ)),Nat.lt_succ_of_le (widthIndex_spec m).1⟩ : T)
set_option quotPrecheck false in
local notation "counts" => fun (t:T) (g:Fin groups)=>count rows w m t.val g.val
set_option quotPrecheck false in
local notation "index" => fun (t:T) (g:Fin groups)=>common rows w m t.val g.val id

def recordOfPiece (t : T) (g : Fin groups) (u : Fin (counts t g)) : R :=
  let slot := (index t g).symm u
  ⟨slot.1.val,Nat.zero_lt_of_lt slot.2.isLt⟩

def digitOfPiece (t : T) (g : Fin groups) (u : Fin (counts t g)) : Fin lanes :=
  let slot := (index t g).symm u
  slot.2.castLE (reserved slot.1.val)

def placedRecord (t : T) (g : Fin groups) (s : Bool) : Fin (counts t g) ↪ Fin (ports*lanes) :=
  (index t g).symm.toEmbedding.trans (staticUnit rows g port (fun b=>
    portDistinct_of_grouped rows w m t.val (port b)
      ((Function.Embedding.sectL R b).trans anchor) (fun r=>owner r b) (fun r=>pin r b) g) reserved le_rfl s)

set_option quotPrecheck false in
local notation "loc" => placedRecord rows w m id port anchor owner pin reserved
set_option quotPrecheck false in
local notation "rec" => recordOfPiece rows w m id
set_option quotPrecheck false in
local notation "piece" => digitOfPiece rows w m id reserved

/-- On an original live ordinal, read from the publicly located endpoint
independently of the term's width class and its relative ordering of links. -/
theorem output_record (hw : 0<w) (word : (r:R)→Fin (bits r)→Bool)
    (r : R) (side : Bool) (j : Fin (bits r)) :
    positivePlane width (afterCuts width bits counts loc rec piece word) (anchor (r,side)) j.val=word r j := by
  have wp (t:T) : 0<width t := Nat.ceil_pos.mpr (mul_pos (dyadic_pos _) (Nat.cast_pos.mpr hw))
  apply output_slice_bit width bits kind anchor counts loc rec piece
  · intro t g u
    exact Fin.ext ((index t g).symm u).1.property.2
  · intro t g u s
    exact Fin.ext ((owner (rec t g u) s).trans ((index t g).symm u).1.property.1)
  · intro t g u s
    change fixedSlot le_rfl (port s (rec t g u).val,piece t g u)=_
    rw [pin]
  · intro r s j t g
    let inGroup : InGroup rows w m t.val g.val :=
      ⟨r.val,(owner r s).symm,rfl⟩
    have qualified : (rows r.val).width≤pieces rows w r.val*width t := rounded_room _ _ _ hw
    let digit : Fin (pieces rows w r.val) := ⟨j.val/width t,(Nat.div_lt_iff_lt_mul (wp t)).mpr (j.isLt.trans_le qualified)⟩
    let named := (index t g) ⟨inGroup,digit⟩
    use named
    constructor
    · exact Subtype.ext (by simp only [recordOfPiece,named,Equiv.symm_apply_apply];rfl)
    · exact congrArg (fun u : ProtocolRAMReportedPorts.Unit rows w m t.val g.val=>u.2.val)
        ((index t g).symm_apply_apply ⟨inGroup,digit⟩)
  · exact wp

/-- The data tensor after summing the two shorter-call tags is literally
the bit vector used by 'output_record'. Absolute bits of the shared row
label are split at its true subslot, with zeros above the original width. -/
theorem output_expanded (word : (r:R)→Fin (bits r)→Bool) (hw : 0<w) :
    let rows' := fun _ : T=>rows
    let gs := fun _ : T=>groups
    let γ := fun t:T=>t.val
    let ords := Occ gs γ rows' w m
    let original := fun v : ((a : ords) × Fin ((rows a.2.2.val).width))=>
      word ⟨v.1.2.2.val,by
        apply Nat.ceil_pos.mpr
        exact div_pos (Nat.cast_pos.mpr (Nat.zero_lt_of_lt v.2.isLt)) (Nat.cast_pos.mpr hw)⟩ v.2
    let labels := expandedLabels gs γ rows' w m (fun _=>id) original
    (fun a : OutputData T (Fin groups) ports lanes width=>
      encode (loc a.1) (fun _=>false) (labels a.1) a.2.1 a.2.2) =
      afterCuts width bits counts loc rec piece word := by
  intro rows' gs γ ords original labels
  funext a
  apply congrFun _ a.2.2
  apply congrArg (fun f=>encode (loc a.1) (fun _=>false) f a.2.1)
  funext e j
  rfl

end Hierarchy.Tagged.WideStack

end
end OAI
