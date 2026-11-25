import OAI.Hierarchy.TaggedWireEndMuxData
import OAI.Hierarchy.TaggedWideOutputRecords
import OAI.Hierarchy.TaggedWidePrivateOrdinals

namespace OAI
/-! # Reading the original paid or un-compacted private word on a fixed barrel wire -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
open AdaptiveProbe ReportSockets Tagged Tagged.WideStack ProtocolStackContraction
open TaggedShorterSupergroups TaggedShorterFields TaggedShorterBudget ProtocolRAMReportedPorts
open ProtocolRAM.Calendar.CatalogueRows
open ThreeFlat Routing
open scoped Classical

variable {h W k attempts H n lanes : ℕ} (S : PurchaseSampler)
variable (dir : Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H)

variable (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (rows : Fin b.rows→ProtocolRAMEmit.Row) (words : ∀i,Fin (2^(rows i).width))

/-- Both half-ends of an original private word use that same native ordinal.
The private equality switches have already identified the two live prefixes. -/
def privateOriginal (capacity : b.Private order→ℕ) :
    Free S h (2^W) k→Bool→ℕ→Bool :=
  let f:=b.freeOrdinal order
  let use:=fun x:b.Private order=>(rows x.val).width
  let sideWords:=privateEncode use capacity (fun i j=>(words i.val).val.testBit j.val)
  fun e s j=>if bound:j<capacity (f e) then sideWords s (f e) ⟨j,bound⟩ else false

theorem private_original_read (capacity : b.Private order→ℕ)
    (room : ∀i:b.Private order,(rows i.val).width≤capacity i)
    (i : b.Private order) (side : Bool) (j : Fin (rows i.val).width)
    (previous : Public S h W k attempts→ℕ→Bool) (positiveBits : Fin dir.groups×Fin H→ℕ→Bool) :
    publicData S dir previous (privateOriginal S b order rows words capacity) positiveBits true
      (.inl (.inl ((b.freeOrdinal order).symm i,side))) j.val=(words i.val).val.testBit j.val := by
  simp only [publicData,privateOriginal,Equiv.apply_symm_apply,dite_eq_left (j.isLt.trans_le (room i)),
    privateEncode,dite_eq_left j.isLt]
  exact congrArg (fun q : b.Private order => (words q.val).val.testBit j.val) ((b.freeOrdinal order).apply_symm_apply i)

variable (w m : ℕ) (inject : Function.Injective fun i=>(rows i).link)
  (port : Bool→Fin b.rows→Fin H)
  (location : ({i // 0<pieces rows w i}×Bool) ↪ StageColumns h (2^W) × Role k attempts)
local notation "anchor" => location.trans (packed dir)
variable (owner : ∀i s,((location.trans (packed dir)) (i,s)).1.val=(rows i.val).group)
  (pins : ∀i s,((location.trans (packed dir)) (i,s)).2=port s i.val) (reserved : ∀i,pieces rows w i≤lanes)
local notation "width" => fun t:Fin (m+1)=>⌈dyadic t.val*w⌉₊
local notation "countAt" => fun (t:Fin (m+1)) (g:Fin dir.groups)=>count rows w m t.val g.val
local notation "rec" => recordOfPiece rows w m inject
local notation "dig" => digitOfPiece rows w m inject reserved
local notation "loc" => placedRecord rows w m inject port anchor owner pins reserved
local notation "bits" => fun (r:{i // 0<pieces rows w i})=>(rows r.val).width

/-- A paid site's native output register is the bit at its original report
row, even when several generations of retained births share its public group. -/
theorem positive_original_read (hw : 0<w) (i : {r // 0<pieces rows w r}) (side : Bool)
    (j : Fin (rows i.val).width) (previous : Public S h W k attempts→ℕ→Bool)
    (free : Free S h (2^W) k→Bool→ℕ→Bool) :
    publicData S dir previous free
      (positivePlane width (afterCuts width bits countAt loc rec dig
        (fun r q=>(words r.val).val.testBit q.val))) true (.inl (.inr (location (i,side)))) j.val=
      (words i.val).val.testBit j.val := by
  exact output_record rows w m inject port anchor owner pins reserved hw _ i side j

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal

end
end OAI
