import OAI.Hierarchy.TaggedWireSocketCoordinates
import OAI.Hierarchy.TaggedWireTerminalScale
import OAI.Hierarchy.ProtocolRAMCatalogueSlotScan

namespace OAI
/-! # The terminal seven-word group and the two fixed physical role operands -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
open ProbeStage CoreBoard AdaptiveProbe ReportSockets TaggedShorterSupergroups
open HistoryRoles RoleProgram ProtocolRAMReportedPorts Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing

variable {h W k attempts M H u : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)
    (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k) (acquired : Bought S π depth marked→Fin b.boughtRows)
    (raw : Fin b.rows→ProtocolRAMEmit.Row)
local notation "ord" => b.original S π depth marked order acquired
variable (receipt : Alignment b S π depth marked M raw (fun i=>(raw i).width)
    (b.original S π depth marked order acquired))
variable (dir : Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H)
variable (stage : Fin b.rows→ℕ) (scale w : ℕ) (hw : 0<w)
local notation "selected" => Tagged.WideStack.atScale (b.transport order) stage scale raw
local notation "Live" => {i // 0<pieces selected w i}
local notation "siteLoc" => location S π depth marked unique b order acquired raw receipt stage scale w hw
local notation "anchor" => (siteLoc).trans (ReportSockets.packed dir)
local notation "rAt" => reportedRow S π depth marked b order acquired raw receipt stage scale w hw
local notation "original" => atOriginal b order raw stage scale w hw
local notation "lab" => HistoryRoles.labelled S π depth marked
local notation "place" => ReportSockets.placed S π depth marked unique dir
local notation "sideAt" => sourceSide S π depth marked b order acquired raw receipt

/-- Read a control word from the *actual* ordered socket expression. All
out-of-range unused words share the same typed default. -/
def physicalPort {H : ℕ} (pos : 0<H) (L : RoleProgram.Chart) (b : Board) (left right : Bool→Socket)
    (m : Memory u) (s : Bool) (i : Fin b.rows) : Fin H :=
  let n:=((Slot.ordered L b left right s).eval m (i.val:Word u)).val
  if lt:n<H then ⟨n,lt⟩ else ⟨0,pos⟩

theorem physicalPort_read {H : ℕ} (pos : 0<H) (L : RoleProgram.Chart) (b : Board) (left right : Bool→Socket)
    (m : Memory u) (s : Bool) (i : Fin b.rows) (p : Fin H) (fit : H≤2^u)
    (read : (Slot.ordered L b left right s).eval m (i.val:Word u)=(p.val:Word u)) :
    physicalPort pos L b left right m s i=p := by
  apply Fin.ext
  simp [physicalPort,read,Fin.val_cast_of_lt (p.isLt.trans_le fit),p.isLt]

private theorem true_row (i : Live) :
    ord ((lab).symm (.inr (rAt i)))=i.val := by
  have labelled : lab (receipt.ident (original i).val) = .inr (rAt i) :=
    positive_spec S π depth marked b order acquired raw receipt (original i)
  rw [←labelled,Equiv.symm_apply_apply]
  exact receipt.original _

/-- The two counts and slot ordinals are the very operands selected by
the chronological core/bought selector. Both sides use the original row. -/
theorem table_coordinates (m : Memory u) (core bought : Bool→Socket) (room : b.rows<2^u)
    (coreAt : ∀t p l s,Coordinates dir (core s) m ((order.symm (.inr ((p,t),l))).val:Word u)
      (locate S π depth marked unique (.inl ((t,p),l),s)))
    (boughtAt : ∀e s,Coordinates dir (bought s) m ((acquired e).val:Word u)
      (locate S π depth marked unique (.inr e,s))) (r : ReportSockets.Row S π depth marked) (s : Bool) :
    Coordinates dir (paidInputs b core bought s) m ((ord ((lab).symm (.inr r))).val:Word u)
      (locate S π depth marked unique (r,s)) := by
  rcases r with ⟨⟨t,p⟩,l⟩|e
  · exact paid_coordinates_core b dir core bought m _ s _ room (coreAt t p l s)
  · exact paid_coordinates_bought b dir core bought m _ s _ room (boughtAt e s)

/-- Native .core_reads/.bought_reads give the original group for every live
row, even though the catalogue may store its two ends in reverse order. -/
theorem table_group (m : Memory u) (groupFit : dir.groups≤2^u)
    (coreRows : CoreCatalogue.Rows b.core order dir π M m)
    (coreRead : ∀j,(raw (b.coreIndex j)).group=(b.core.view m (j.val:Word u)).group)
    (boughtRead : ∀j,(raw (b.boughtIndex j)).group=(b.bought.view m (j.val:Word u)).group)
    (actual : ∀e,b.bought.group.eval m ((acquired e).val:Word u)=((place (.inr e,false)).1.val:Word u))
    (r : ReportSockets.Row S π depth marked) :
    (raw (ord ((lab).symm (.inr r)))).group=(place (r,false)).1.val := by
  rcases r with ⟨⟨t,p⟩,l⟩|e
  · let j:=order.symm (.inr ((p,t),l))
    have atGroup:=(coreRows j).1
    rw [show order j=.inr ((p,t),l) from order.apply_symm_apply _] at atGroup
    have fit:=(place (.inl ((t,p),l),false)).1.isLt.trans_le groupFit
    exact (coreRead j).trans ((congrArg Fin.val atGroup).trans (Fin.val_cast_of_lt fit))
  · exact (boughtRead (acquired e)).trans ((congrArg Fin.val (actual e)).trans
      (Fin.val_cast_of_lt ((place (.inr e,false)).1.isLt.trans_le groupFit)))

theorem owner_of_table
    (groups : ∀r,(raw (ord ((lab).symm (.inr r)))).group=(place (r,false)).1.val)
    (i : Live) (s : Bool) : (anchor (i,s)).1.val=(raw i.val).group := by
  have src:=true_row S π depth marked b order acquired raw receipt stage scale w hw i
  have orig:=groups (rAt i)
  rw [src] at orig
  exact (congrArg Fin.val (placed_group S π depth marked unique dir (rAt i) (sideAt (original i).val s))).trans orig.symm

theorem literal_slot (L : RoleProgram.Chart) (m : Memory u) (core bought : Bool→Socket)
    (sitesFit : siteLast h (2^W) k+1≤2^u)
    (resolved : ∀i : Active b raw,∀s,Resolved S L (paidInputs b core bought s) m (i.val.val:Word u)
      (.inl (paid S π depth marked unique (receipt.ident i,s))))
    (coordinates : ∀r s,Coordinates dir (paidInputs b core bought s) m ((ord ((lab).symm (.inr r))).val:Word u)
      (locate S π depth marked unique (r,s)))
    (i : Live) (s : Bool) :
    (Slot.ordered L b core bought s).eval m (i.val.val:Word u)=((anchor (i,s)).2.val:Word u) := by
  let q:= (original i).val
  let x:=receipt.ident q
  let ends:=actualEnds S π depth marked x
  let first:=HistoryRoles.name ends.1
  let last:=HistoryRoles.name ends.2
  have row : q.val = i.val := rfl
  have seen (a : Bool) := (resolved q a).1
  have left : (socketSite L (paidInputs b core bought false)).eval m (i.val.val:Word u)=(first.val:Word u) := by
    simpa only [row,first,ends,x,HistoryRoles.site,Sum.elim_inl,HistoryRoles.paid_site,Incident.choose] using seen false
  have right : (socketSite L (paidInputs b core bought true)).eval m (i.val.val:Word u)=(last.val:Word u) := by
    simpa only [row,last,ends,x,HistoryRoles.site,Sum.elim_inl,HistoryRoles.paid_site,Incident.choose] using seen true
  have flip : Slot.orientation L (paidInputs b core bought) m (i.val.val:Word u) s=sideAt q s := by
    change (if _ then s else !s)=(if first<last then s else !s)
    rw [left,right]
    simp only [Fin.lt_def,Fin.val_cast_of_lt (first.isLt.trans_le sitesFit),Fin.val_cast_of_lt (last.isLt.trans_le sitesFit)]
  have read:=(coordinates (rAt i) (sideAt q s)).2
  rw [true_row S π depth marked b order acquired raw receipt stage scale w hw i] at read
  rw [Slot.ordered_at]
  change (paidInputs b core bought (Slot.orientation L (paidInputs b core bought) m (i.val.val:Word u) s)).slot.eval m (i.val.val:Word u) = _
  rw [flip]
  exact read

theorem pins_of_slots (pos : 0<H) (format : H≤2^u) (L : RoleProgram.Chart) (m : Memory u) (core bought : Bool→Socket)
    (slots : ∀(i:Live) s,(Slot.ordered L b core bought s).eval m (i.val.val:Word u)=((anchor (i,s)).2.val:Word u))
    (i : Live) (s : Bool) : (anchor (i,s)).2=physicalPort pos L b core bought m s i.val :=
  (physicalPort_read pos L b core bought m s i.val _ format (slots i s)).symm

/-- The native retained-bought source places the group bank at its original
unoriented left entry. Its value agrees with the common placed group. -/
theorem bought_group {K : ℕ} (m : Memory u) (v : BoughtSockets.Directory attempts)
    (source : b.bought=v.source S h W k depth K dir.groups H)
    (coords : ∀e,Coordinates dir (boughtInputs v S h W k depth K false) m ((acquired e).val:Word u)
      (locate S π depth marked unique (.inr e,false))) (e : Bought S π depth marked) :
    b.bought.group.eval m ((acquired e).val:Word u)=((place (.inr e,false)).1.val:Word u) := by
  rw [source]
  exact (coords e).1

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
end

end OAI
