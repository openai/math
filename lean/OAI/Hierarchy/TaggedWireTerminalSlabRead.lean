import OAI.Hierarchy.TaggedWireTerminalOutputBits
import OAI.Hierarchy.TaggedWireTerminalOutputSite

namespace OAI
/-! # Original native row bits on the literal fixed wiring of the turn barrel -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
open ProbeStage CoreBoard AdaptiveProbe ReportSockets Tagged Tagged.WideStack ProtocolStackContraction WireTelescope
open ProtocolRAMEmit ProtocolRAMReportedPorts TaggedShorterBudget TaggedShorterFields TaggedShorterSupergroups
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical
variable {h W k attempts M H lanes p e : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)
    (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k) (acquired : Bought S π depth marked→Fin b.boughtRows)
    (raw : Fin b.rows→ProtocolRAMEmit.Row)
local notation "ordinal" => b.original S π depth marked order acquired
variable (receipt : Alignment b S π depth marked M raw (fun i=>(raw i).width)
    (b.original S π depth marked order acquired))
variable (dir : Directory (TaggedShorterSupergroups.reserved h W (ReportSockets.copies k attempts)) H)
variable (w m : ℕ) (hw : 0<w)
local notation "masked" => atScale (b.transport order) (fun _=>0) 0 raw
local notation "Live" => {i // 0<pieces masked w i}
local notation "anch" => (location S π depth marked unique b order acquired raw receipt (fun _=>0) 0 w hw).trans (ReportSockets.packed dir)
variable (inject : Function.Injective fun i=>(raw i).link) (port : Bool→Fin b.rows→Fin H)
variable (owner : ∀i s,
    (((location S π depth marked unique b order acquired raw receipt (fun _=>0) 0 w hw).trans (ReportSockets.packed dir)) (i,s)).1.val=(raw i.val).group)
variable (pins : ∀i s,
    (((location S π depth marked unique b order acquired raw receipt (fun _=>0) 0 w hw).trans (ReportSockets.packed dir)) (i,s)).2=port s i.val)
variable (room : ∀i,pieces (atScale (b.transport order) (fun _=>0) 0 raw) w i≤lanes)
variable (words : ∀i,Fin (2^(raw i).width)) (capacity : b.Private order→ℕ)
variable (maxPrivate : ∀i:b.Private order,(raw i.val).width≤capacity i)
variable (previous : HistoryRoles.Public S h W k attempts→ℕ→Bool)
local notation "switched" => paidPlane S π depth marked unique b order acquired raw receipt dir w m hw inject port owner pins room words
local notation "freeBits" => HistoryRoles.Terminal.privateOriginal S b order raw words capacity
local notation "field" => HistoryRoles.Terminal.publicData S dir previous freeBits switched
local notation "K" => siteLast h (2^W) k+1
local notation "name" => siteNumber h (2^W) k
variable (B : Mount (S:=S) π (siteNumber h (2^W) k) b.rows) (pad : Chord (siteLast h (2^W) k+1))
variable (v : Site h (2^W) k)
local notation "Fibre" => HistoryRoles.RoleProgram.Fiber (attempts:=attempts) S v
variable (roleFit : ∀a:HistoryRoles.RoleProgram.Fiber (attempts:=attempts) S v,∀t,HistoryRoles.RoleProgram.labelled S t a.val<2^p)
local notation "physical" => fun q : (Bool×Fibre)×Tagged.Row e=>field q.1.1 q.1.2.val q.2.val
local notation "slab" => Sum.elim physical id ∘ HistoryRoles.RoleProgram.slabPins S v roleFit
local notation "pub" => originalPort S π depth marked unique b order acquired raw receipt

include maxPrivate in
/-- The five native selector words address the same local geometric party
and the same uncompressed output bit as the abstract route contraction. -/
theorem paid_bit (i : Active b raw) (side : Bool) (j : Fin (raw i.val).width)
    (tail : (B.actual.tail i.val).val=(raw i.val).endpoint)
    (head : (B.actual.head i.val).val=(raw i.val).opposite)
    (here : (portGraph K).vertex (filledChord B.actual pad i.val) side=name v)
    (q : TurnShelf.Aperture p e) (key : q.1.val=HistoryRoles.RoleProgram.labelled S true (pub i side))
    (digit : q.2.val=j.val) :
    slab q=(words i.val).val.testBit j.val := by
  have onSite : HistoryRoles.site S (pub i side)=v:=
    (name).injective ((original_site S π depth marked unique b order acquired raw receipt B pad i side tail head).trans here)
  let a:Fibre:=⟨pub i side,onSite⟩
  rw [HistoryRoles.RoleProgram.slabBits_at S v roleFit physical q a true key]
  change field true (pub i side) q.2.val=_
  rw [digit]
  exact output_bit S π depth marked unique b order acquired raw receipt dir w m hw inject port owner pins room words
    capacity maxPrivate i side j previous

theorem previous_bit (a : Fibre) (q : TurnShelf.Aperture p e)
    (key : q.1.val=HistoryRoles.RoleProgram.labelled S false a.val) :
    slab q=previous a.val q.2.val :=
  HistoryRoles.RoleProgram.slabBits_at S v roleFit physical q a false key

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment

end
end OAI
