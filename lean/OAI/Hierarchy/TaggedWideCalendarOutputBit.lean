import OAI.Hierarchy.TaggedWideCalendarExit
import OAI.Hierarchy.TaggedWireTerminalScale
import OAI.Hierarchy.TaggedWideCalendarLeaf
import OAI.Hierarchy.TaggedWideLeafBits

namespace OAI
/-! # The terminal comparator reads the actual original committed row digit -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing
open AdaptiveProbe ProbeStage CoreBoard ReportSockets Tagged Tagged.WideStack ProtocolStackContraction
open HistoryRoles RoleProgram WireTelescope CalendarTape TaggedShorterBudget ProtocolRAMReportedPorts
open Leaf WideCalendarSites
open scoped Classical BigOperators
set_option quotPrecheck false
variable {F : Type*} [Field F] {stageHeight : ℕ} {h W k attempts M H lanes w m p e view : ℕ}
    (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ) (marked : Marks h W k attempts)
    (unique : Exclusive marked) (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k)
    (acquired : Bought S π depth marked→Fin b.boughtRows) (raw : Fin b.rows→ProtocolRAMEmit.Row)
local notation "ord" => b.original S π depth marked order acquired
variable (A : Alignment b S π depth marked M raw (fun i=>(raw i).width) (b.original S π depth marked order acquired))
    (dir : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H)
    (hw : 0<w)
local notation "pos" => b.transport order
local notation "stage" => fun _ : Fin b.rows=>stageHeight
local notation "rows" => atScale pos stage stageHeight raw
local notation "key" => stageKey stageHeight m
local notation "width" => fun t : Fin (m+1)=>⌈dyadic t.val*w⌉₊
local notation "Live" => {i : Fin b.rows // 0<pieces rows w i}
local notation "loc" => location S π depth marked unique b order acquired raw A stage stageHeight w hw
local notation "anchor" => (loc).trans (ReportSockets.packed dir)
local notation "pub" => originalPort S π depth marked unique b order acquired raw A
variable (ins : ∀t : Fin (m+1),Installed F dir.groups H lanes w m t.val (atScale (b.transport order) (fun _ : Fin b.rows=>stageHeight) stageHeight raw))
    (inject : Function.Injective fun i=>((atScale (b.transport order) (fun _ : Fin b.rows=>stageHeight) stageHeight raw) i).link) (port : Bool→Fin b.rows→Fin H)
    (same : ∀t,(ins t).port=port)
    (owner : ∀(i:({i : Fin b.rows // 0<pieces (atScale (b.transport order) (fun _ : Fin b.rows=>stageHeight) stageHeight raw) w i})) s,((((location S π depth marked unique b order acquired raw A (fun _ : Fin b.rows=>stageHeight) stageHeight w hw)).trans (ReportSockets.packed dir)) (i,s)).1.val=((atScale (b.transport order) (fun _ : Fin b.rows=>stageHeight) stageHeight raw) i.val).group)
    (pins : ∀(i:({i : Fin b.rows // 0<pieces (atScale (b.transport order) (fun _ : Fin b.rows=>stageHeight) stageHeight raw) w i})) s,((((location S π depth marked unique b order acquired raw A (fun _ : Fin b.rows=>stageHeight) stageHeight w hw)).trans (ReportSockets.packed dir)) (i,s)).2=port s i.val) (room : ∀i,pieces (atScale (b.transport order) (fun _ : Fin b.rows=>stageHeight) stageHeight raw) w i≤lanes)
    (capacity : b.Private order→ℕ) (maxPrivate : ∀i : b.Private order,(raw i.val).width≤capacity i)
    (es : List Event) (histCap : Public S h W k attempts→ℕ)
local notation "Q" => (q:Public S h W k attempts) × Fin (histCap q)
local notation "time" => Fin ((es.length+1)*Fintype.card Q)
variable (a : ∀i,Fin (2^(raw i).width)) (history : (Fin ((es.length+1)*Fintype.card ((q:Public S h W k attempts) × Fin (histCap q))))→Bool)
local notation "val" => nativePins (view:=view) key raw pos stage ins capacity a history
variable (s : Site h (2^W) k)
local notation "Fib" => Fiber (attempts:=attempts) S s
variable (enough : ∀r:(Fiber (attempts:=attempts) S s),∀t,RoleProgram.labelled S t r.val<2^p)
local notation "ap" => Terminal.outputAperture (lanes:=lanes) (view:=view) S dir es b order capacity histCap width s enough

include hw inject same owner pins room maxPrivate in
/-- On the actual common data written by the contraction, both privately
retained and positively purchased native report rows yield their original
digit at the end of the selected chronological itinerary. -/
theorem originalAperture_digit (i : Active b raw) (side : Bool) (j : Fin (raw i.val).width)
    (here : HistoryRoles.site S (pub i side)=s) (viewRoom : (raw i.val).width≤view)
    (q : TurnShelf.Aperture p e) (code : q.1.val=RoleProgram.labelled S true (pub i side)) (digit : q.2.val=j.val) :
    Sum.elim val id (ap q)=(a i.val).val.testBit j.val := by
  let f : Fib:=⟨pub i side,here⟩
  refine (Terminal.outputAperture_at (lanes:=lanes) (view:=view) S dir es b order capacity histCap width s enough val q f true code).trans ?_
  change Sum.elim val id (Terminal.endPin S dir _ _ _ true (pub i side) q.2.val)=_
  rw [digit]
  by_cases paid : pos i.val
  · let r : Live:=⟨i.val,(atScale_iff b order raw stage stageHeight w hw i.val).mpr ⟨paid,rfl,i.property⟩⟩
    have wh := atScale_port S π depth marked unique b order acquired raw A stage stageHeight w hw r side
    change pub i side=.inl (.inr (loc (r,side))) at wh
    rw [wh]
    have top := j.isLt.trans_le viewRoom
    let l : Fin (rows r.val).width := j.cast (atScale_width b order raw stage stageHeight w hw r).symm
    simp only [Terminal.endPin, Terminal.positiveOutputPin, dite_eq_left top]
    exact decoded_original raw pos stage ins inject port same anchor owner pins room hw a r side l
  · rw [private_original S π depth marked unique b order acquired raw A i paid side]
    let r : b.Private order:=⟨i.val,paid⟩
    change Sum.elim val id (Terminal.freeOutputPin S dir es b order capacity histCap width
      ((b.freeOrdinal order).symm r) _ j.val)=_
    let g := (b.freeOrdinal order) ((b.freeOrdinal order).symm r)
    have sameRow : g = r := (b.freeOrdinal order).apply_symm_apply r
    have allocated : j.val < capacity g := sameRow.symm ▸ j.isLt.trans_le (maxPrivate r)
    have active : j.val < (raw g.val).width := sameRow.symm ▸ j.isLt
    unfold Terminal.freeOutputPin
    rw [dite_eq_left allocated]
    change (if live : j.val < (raw g.val).width then (a g.val).val.testBit j.val else false) = _
    rw [dite_eq_left active]
    exact congrArg (fun row : b.Private order => (a row.val).val.testBit j.val) sameRow

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment

end
end OAI
