import OAI.Hierarchy.TaggedWireTerminalSlabRead
import OAI.Hierarchy.TaggedWireAlignedEmitter

namespace OAI
/-! # Reading a paid barrel pin from the actual original group and slot registers -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
open ProbeStage CoreBoard AdaptiveProbe ReportSockets Tagged Tagged.WideStack ProtocolStackContraction WireTelescope
open HistoryRoles RoleProgram ProtocolRAMEmit ProtocolRAMReportedPorts TaggedShorterBudget TaggedShorterSupergroups
open Computability.VPVNP.BurstRAM PrivateRAM LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical Fin.CommRing
variable {h W k attempts M H lanes p e u : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)
    (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k) (acquired : Bought S π depth marked→Fin b.boughtRows)
    (raw : Fin b.rows→ProtocolRAMEmit.Row)
variable (receipt : Alignment b S π depth marked M raw (fun i=>(raw i).width)
    (b.original S π depth marked order acquired))
variable (dir : Directory (TaggedShorterSupergroups.reserved h W (ReportSockets.copies k attempts)) H)
variable (w m : ℕ) (hw : 0<w)
local notation "masked" => atScale (b.transport order) (fun _=>0) 0 raw
variable (inject : Function.Injective fun i=>(raw i).link)
variable (L : RoleProgram.Chart) (mem : Memory u) (core bought : Bool→Socket)
variable (rooms : siteLast h (2^W) k+1≤2^u) (pos : 0<H) (format : H≤2^u)
variable (reported : ∀r,(raw (b.original S π depth marked order acquired ((HistoryRoles.labelled S π depth marked).symm (.inr r)))).group=(placed S π depth marked unique dir (r,false)).1.val)
variable (resolved : ∀i:Active b raw,∀s,Resolved S L (paidInputs b core bought s) mem (i.val.val:Word u)
  (.inl (paid S π depth marked unique (receipt.ident i,s))))
variable (socket : ∀r s,Coordinates dir (paidInputs b core bought s) mem ((b.original S π depth marked order acquired ((HistoryRoles.labelled S π depth marked).symm (.inr r))).val:Word u)
  (locate S π depth marked unique (r,s)))
local notation "win" => (fun _:Fin b.rows=>0)
local notation "groupReads" => owner_of_table S π depth marked unique b order acquired raw receipt dir win 0 w hw reported
local notation "slotReads" => literal_slot S π depth marked unique b order acquired raw receipt dir win 0 w hw L mem core bought rooms resolved socket
local notation "fits" => pins_of_slots S π depth marked unique b order acquired raw receipt dir win 0 w hw pos format L mem core bought slotReads
local notation "physicalPortAt" => physicalPort pos L b core bought mem
variable (room : ∀i,pieces (atScale (b.transport order) (fun _=>0) 0 raw) w i≤lanes)
variable (words : ∀i,Fin (2^(raw i).width)) (capacity : b.Private order→ℕ)
variable (maxPrivate : ∀i:b.Private order,(raw i.val).width≤capacity i)
variable (previous : Public S h W k attempts→ℕ→Bool)
local notation "switched" => paidPlane S π depth marked unique b order acquired raw receipt dir w m hw inject physicalPortAt groupReads fits room words
local notation "freeBits" => Terminal.privateOriginal S b order raw words capacity
local notation "field" => Terminal.publicData S dir previous freeBits switched
local notation "K" => siteLast h (2^W) k+1
local notation "name" => siteNumber h (2^W) k
variable (B : Mount (S:=S) π (siteNumber h (2^W) k) b.rows) (pad : Chord (siteLast h (2^W) k+1))
variable (v : Site h (2^W) k)
local notation "Fibre" => Fiber (attempts:=attempts) S v
variable (roleFit : ∀a:Fiber (attempts:=attempts) S v,∀t,RoleProgram.labelled S t a.val<2^p)
local notation "localValues" => fun q : (Bool×Fibre)×Tagged.Row e=>field q.1.1 q.1.2.val q.2.val
local notation "pub" => originalPort S π depth marked unique b order acquired raw receipt

include maxPrivate in
/-- The read is performed at the physically normalized socket in the same
initial memory used by the two side-compactors and the routed-turn program. -/
theorem paidRead (i : Active b raw) (side : Bool) (j : Fin (raw i.val).width)
    (tail : (B.actual.tail i.val).val=(raw i.val).endpoint)
    (head : (B.actual.head i.val).val=(raw i.val).opposite)
    (here : (portGraph K).vertex (filledChord B.actual pad i.val) side=name v)
    (q : TurnShelf.Aperture p e) (key : q.1.val=RoleProgram.labelled S true (pub i side))
    (digit : q.2.val=j.val) :
    (Sum.elim localValues id ∘ slabPins S v roleFit) q=(words i.val).val.testBit j.val :=
  paid_bit S π depth marked unique b order acquired raw receipt dir w m hw inject physicalPortAt groupReads fits room
    words capacity maxPrivate previous B pad v roleFit i side j tail head here q key digit

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment

end
end OAI
