import OAI.Computability.NearSquareRoot.InterchangeROMStageVerify
import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasPacking
import OAI.Computability.NearSquareRoot.InterchangeVerifiedAtlas

/-! # Checked source indices and oriented chart slots in each sparse stage route -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame.Realization
open Interchange Interchange.RectangleAtlas StageLedger StageRoute IntegerMultiplication.Port

variable {g : Frame} (r : Realization g)

abbrev NativeMove := StageRoute.Move r.rect (Fin (queries g)) (r.sel true) (r.sel false)

private def slot (s : Bool) (c : Chart r.rect (queries g)) : Frame.Move :=
  some (s,FlatAtlas.chartIndex c)

/-- The packed table entry corresponding to a typed address operation. -/
def operand : r.NativeMove → Frame.Move
  | .idle => none
  | .prepare e => slot r false (.prepare e)
  | .restore e => slot r true (.prepare e)
  | .align j e => slot r false (.localMap j e)
  | .unalign j e => slot r true (.localMap j e)
  | .gather j ⟨i,none⟩ => slot r false (.label false j (r.sel true i))
  | .gather j ⟨_,some b⟩ => slot r false (.common j b.1)
  | .distribute j ⟨i,none⟩ => slot r true (.label true j (r.sel false i))
  | .distribute j ⟨_,some b⟩ => slot r true (.common j b.1)

/-- Ordinary result of the source-row and chart-slot selector for a typed route. -/
def CorrectRoute (n : ℕ) (src : r.Boundary (n+1) → r.Boundary n)
    (op : r.Boundary (n+1) → r.NativeMove) : Prop :=
  ∀ v, leg g n (r.code (n+1) v) = (r.code n (src v),r.operand (op v))

theorem prepare_correct : r.CorrectRoute 0 (Sum.elim id Sigma.fst)
    (Sum.elim (fun _ => .idle) .prepare) := by
  rintro (v|e) <;> rfl

theorem align_correct : r.CorrectRoute 1 (Sum.map id Prod.snd)
    (Sum.elim (fun _ => .idle) (fun (j,e) => .align j e)) := by
  rintro (v|⟨j,e⟩) <;> rfl

theorem gather_correct : r.CorrectRoute 3
    (Sum.elim id (fun (j,t) => gatherFrom r.rect (r.sel true) j t))
    (Sum.elim (fun _ => .idle) (fun (j,t) => .gather j t)) := by
  rintro ((v|⟨j,b⟩)|⟨j,i,_|b⟩)
  · rfl
  · rfl
  · change (label (((minor g true)[i.val]?).getD 0),
      some (false,labelChart g false j.val (((minor g true)[i.val]?).getD 0))) = _
    rw [r.minor_get]; rfl
  · rfl

theorem distribute_correct : r.CorrectRoute 5
    (Sum.map id (fun (j,t) => (j,t.1)))
    (Sum.elim (fun _ => .idle) (fun (j,t) => .distribute j t)) := by
  rintro ((v|⟨j,b⟩)|⟨j,i,_|b⟩)
  · rfl
  · rfl
  · change (rankRow j.val i.val,
      some (true,labelChart g true j.val (((minor g false)[i.val]?).getD 0))) = _
    rw [r.minor_get]; rfl
  · rfl

theorem unalign_correct : r.CorrectRoute 7 (Sum.map id (fun (j,e) => (j,e.2.1)))
    (Sum.elim (fun _ => .idle) (fun (j,e) => .unalign j e)) := by
  rintro ((v|⟨j,i⟩)|⟨j,e⟩) <;> rfl

theorem restore_correct : r.CorrectRoute 9 id (Sum.elim (fun _ => .idle) .restore) := by
  rintro (v|e) <;> rfl

end InterchangeROMStage.Frame.Realization

namespace InterchangeROMStage
open IntegerMultiplication.Port Interchange

/-- Word-level inversion used by a reverse chart slot, including the null gather. -/
def rewindOp (o : Opcode.Op) : Opcode.Op :=
  match Opcode.tag o with
  | 0 => (0,Opcode.target o,Opcode.source o,Opcode.negative o,Opcode.denominator o,Opcode.numerator o)
  | 1 => if Opcode.numerator o = 0 then o else
    (1,Opcode.target o,Opcode.source o,!Opcode.negative o,Opcode.numerator o,Opcode.denominator o)
  | _ => o

theorem rewind_encode {n b : ℕ} (c : Lag (Fin n) b) :
    rewindOp (Opcode.encode c) = Opcode.encode c.rewind := by
  cases c with
  | width => rfl
  | pivot => rfl
  | gather a k q =>
    cases q with
    | none => rfl
    | some s => simp [rewindOp,Opcode.encode,Lag.rewind,Pinpoint.opposite,Span.opposite,
        Opcode.numerator,s.top.pos]

def lookup (A : List Opcode.Word) : Frame.Move → Opcode.Word
  | none => []
  | some (inverse,pos) =>
    let w := FlatAtlas.chart A pos
    if inverse then w.reverse.map rewindOp else w

namespace Frame.Realization

variable {g : Frame} (r : Realization g)

/-- Reading an oriented slot of a verified catalog gives exactly its typed P192
Lag instruction list, including the reversal and reciprocal/sign changes. -/
theorem lookup_operand {a b : ℕ} (w : AddressROM.Catalog r.rect a (queries g) b)
    (A : List Opcode.Word)
    (ha : ∀ c, FlatAtlas.chart A (FlatAtlas.chartIndex c) = (w c).map Opcode.encode)
    (m : r.NativeMove) :
    lookup A (r.operand m) = (AddressROM.instructions w m).map Opcode.encode := by
  have fwd (c : RectangleAtlas.Chart r.rect (queries g)) :
      lookup A (slot r false c) = (w c).map Opcode.encode := ha c
  have back (c : RectangleAtlas.Chart r.rect (queries g)) :
      lookup A (slot r true c) = (AddressROM.reverseList (w c)).map Opcode.encode := by
    simp [slot,lookup,ha,AddressROM.reverseList,List.map_reverse,List.map_map,Function.comp_def,rewind_encode]
  cases m with
  | idle => rfl
  | prepare e => exact fwd _
  | restore e => exact back _
  | align j e => exact fwd _
  | unalign j e => exact back _
  | gather j t => rcases t with ⟨i,_ | b⟩ <;> exact fwd _
  | distribute j t => rcases t with ⟨i,_ | b⟩ <;> exact back _

end Frame.Realization
end InterchangeROMStage

end NearSquareRoot
end Computability
end OAI
