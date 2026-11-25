import OAI.Hierarchy.TaggedWireTerminalScale
import OAI.Hierarchy.TaggedWireEndMux

namespace OAI
/-! # The terminal slab reads actual private and switched words at their original ordinals -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
open ProbeStage CoreBoard AdaptiveProbe ReportSockets Tagged Tagged.WideStack ProtocolStackContraction
open ProtocolRAMEmit ProtocolRAMReportedPorts TaggedShorterBudget TaggedShorterFields TaggedShorterSupergroups
open scoped Classical
variable {h W k attempts M H lanes : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)
    (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k) (acquired : Bought S π depth marked→Fin b.boughtRows)
    (raw : Fin b.rows→ProtocolRAMEmit.Row)
local notation "ordinal" => b.original S π depth marked order acquired
variable (receipt : Alignment b S π depth marked M raw (fun i=>(raw i).width)
    (b.original S π depth marked order acquired))
variable (dir : Directory (TaggedShorterSupergroups.reserved h W (ReportSockets.copies k attempts)) H)
variable (w m : ℕ) (hw : 0<w)
local notation "maskRows" => atScale (b.transport order) (fun _=>0) 0 raw
local notation "Live" => {i // 0<pieces maskRows w i}
local notation "place" => location S π depth marked unique b order acquired raw receipt (fun _=>0) 0 w hw
local notation "anch" => (place).trans (ReportSockets.packed dir)
variable (inject : Function.Injective fun i=>(raw i).link)
variable (port : Bool→Fin b.rows→Fin H)
variable (owner : ∀i s,
    (((location S π depth marked unique b order acquired raw receipt (fun _=>0) 0 w hw).trans (ReportSockets.packed dir)) (i,s)).1.val=(raw i.val).group)
variable (pins : ∀i s,
    (((location S π depth marked unique b order acquired raw receipt (fun _=>0) 0 w hw).trans (ReportSockets.packed dir)) (i,s)).2=port s i.val)
variable (room : ∀i,pieces (atScale (b.transport order) (fun _=>0) 0 raw) w i≤lanes)
variable (words : ∀i,Fin (2^(raw i).width))
local notation "unitWidth" => fun t:Fin (m+1)=>⌈dyadic t.val*w⌉₊
local notation "countAt" => fun (t:Fin (m+1)) (g:Fin dir.groups)=>count maskRows w m t.val g.val
local notation "record" => recordOfPiece maskRows w m inject
local notation "digit" => digitOfPiece maskRows w m inject room
local notation "slots" => placedRecord maskRows w m inject port anch owner pins room
local notation "bits" => fun i:Live=>(maskRows i.val).width
local notation "edgeWords" => fun (i:Live) (j:Fin (bits i))=>(words i.val).val.testBit j.val

/-- One public directory pools all stages at the common positive height
fraction. Width classes vary by the measured width of each original row. -/
def paidPlane : Fin dir.groups×Fin H→ℕ→Bool :=
  positivePlane unitWidth (afterCuts unitWidth bits countAt slots record digit edgeWords)

variable (capacity : b.Private order→ℕ) (maxPrivate : ∀i:b.Private order,(raw i.val).width≤capacity i)
local notation "freeBits" => HistoryRoles.Terminal.privateOriginal S b order raw words capacity
local notation "switched" => paidPlane S π depth marked unique b order acquired raw receipt dir w m hw inject port owner pins room words

include maxPrivate in
/-- For every truly used output wire, either side yields the actual packed
bit of the same un-compacted native row. The input is the literal width-type
switch wiring on the positive side and the private equality wiring on the other. -/
theorem output_bit (i : Active b raw) (s : Bool) (j : Fin (raw i.val).width)
    (previous : HistoryRoles.Public S h W k attempts→ℕ→Bool) :
    HistoryRoles.Terminal.publicData S dir previous freeBits switched true
      (originalPort S π depth marked unique b order acquired raw receipt i s) j.val=(words i.val).val.testBit j.val := by
  by_cases keep:b.transport order i.val
  · let q:Live:=⟨i.val,(atScale_iff b order raw (fun _=>0) 0 w hw i.val).mpr ⟨keep,rfl,i.property⟩⟩
    have eq:=atScale_port S π depth marked unique b order acquired raw receipt (fun _=>0) 0 w hw q s
    change originalPort S π depth marked unique b order acquired raw receipt i s=.inl (.inr (place (q,s))) at eq
    rw [eq]
    let d:Fin (bits q):=j.cast (atScale_width b order raw (fun _=>0) 0 w hw q).symm
    exact output_record maskRows w m inject port anch owner pins room hw edgeWords q s d
  · rw [private_original S π depth marked unique b order acquired raw receipt i keep s]
    exact HistoryRoles.Terminal.private_original_read S dir b order raw words capacity maxPrivate
      ⟨i.val,keep⟩ (sourceSide S π depth marked b order acquired raw receipt i s) j previous switched

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment

end
end OAI
