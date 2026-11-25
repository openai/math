import OAI.Hierarchy.TaggedWideDatedOperands
import OAI.Hierarchy.TaggedWideOriginalRoleShelf
import OAI.Hierarchy.TaggedWideRoleScatter
import OAI.Hierarchy.TaggedWideChronologicalOrder
import OAI.Hierarchy.TaggedWireRoleSemantics

namespace OAI
/-! # Native widths, global sparse row ordinals and opposite sites at original spatial ports -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open AdaptiveProbe ProtocolRAM RoleProgram ReportSockets
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr
open scoped Classical Fin.CommRing

def RoleField.data {I : Type} : RoleField → (I → ℕ) → (I → ℕ) → (I → ℕ) → I → ℕ
  | .width,w,_,_,i=>w i
  | .ordinal,w,id,_,i=>if w i=0 then 0 else id i
  | .opposite,w,_,opp,i=>if w i=0 then 0 else opp i

def RoleField.page (L : ℕ) (field : RoleField) :=
  match field with
  | .width=>0
  | .ordinal=>L
  | .opposite=>2*L

theorem RoleField.read {W : ℕ} (field : RoleField) (width ordinal opposite : Expr) (m : Memory W)
    (r : Word W) (qty id other : ℕ) (small : qty<2^W) (wr : width.eval m r=(qty:Word W))
    (ir : 0<qty → ordinal.eval m r=(id:Word W)) (nr : 0<qty → opposite.eval m r=(other:Word W)) :
    (field.expr width ordinal opposite).eval m r=
      (field.data (fun _ : Unit=>qty) (fun _=>id) (fun _=>other) ():Word W) := by
  cases field
  · exact wr
  all_goals
    by_cases empty : qty=0
    · simp [RoleField.expr,RoleField.data,Expr.eval,Comparison.test,wr,empty]
    · have live := Nat.pos_of_ne_zero empty
      have nonzero : (qty:Word W)≠0 := by
        intro eqn
        have val := congrArg (fun f : Word W=>f.val) eqn
        exact empty ((Fin.val_cast_of_lt small).symm.trans val)
      simp [RoleField.expr,RoleField.data,Expr.eval,Comparison.test,wr,nonzero,empty,ir live,nr live]

private theorem RoleField.positive_width {I : Type} (field : RoleField)
    (width ordinal peer : I → ℕ) (i : I) (live : 0 < field.data width ordinal peer i) :
    0 < width i := by
  by_cases zero : width i = 0
  · cases field <;> simp [RoleField.data, zero] at live
  · exact Nat.pos_of_ne_zero zero

private theorem RoleField.below {I : Type} (field : RoleField)
    (width ordinal peer : I → ℕ) (i : I) (bound : ℕ) (positive : 0 < bound)
    (hw : width i < bound) (ho : ordinal i < bound) (hp : peer i < bound) :
    field.data width ordinal peer i < bound := by
  cases field with
  | width => exact hw
  | ordinal => by_cases zero : width i = 0 <;> simp [RoleField.data, zero, positive, ho]
  | opposite => by_cases zero : width i = 0 <;> simp [RoleField.data, zero, positive, hp]

private theorem RoleField.at_unit {I : Type} (field : RoleField)
    (width ordinal peer : I → ℕ) (i : I) :
    field.data width ordinal peer i =
      field.data (fun _ : Unit => width i) (fun _ => ordinal i) (fun _ => peer i) () := by
  cases field <;> rfl

private theorem RoleField.zero_read {native : ℕ} (field : RoleField)
    (size number peer : Expr) (m : Memory native) (row : Word native) (empty : size.eval m row = 0) :
    (field.expr size number peer).eval m row = 0 := by
  cases field <;> simp [RoleField.expr, Expr.eval, Comparison.test, empty]

variable {h W k attempts native N count : ℕ} (S : PurchaseSampler)
    (π : Equiv.Perm (Fin (2^h))) (depth : ℕ) (mark : Marks h W k attempts) (unique : Exclusive mark)
    (rows : Fin N ≃ Source S π depth mark)
local notation "port" => named S π depth mark unique rows
local notation "Nport" => (siteLast h (2^W) k+1)*stride k S.degree attempts

/-- One fixed half of a sparse original RAM stream. Each source names the true original row
and the sorted side that reaches the physical raw socket. All fields of a dormant row vanish.
The width expression is read before touching either of its two potentially vacant sockets. -/
theorem scatter_field_all (field : RoleField) (base scratch sink : ℕ) (size number : Expr)
    (chart : Chart) (self peer : Socket) (siteTable : Bank) (m : Memory native)
    (qty id : Fin N→ℕ) (source : Fin count → Option (Fin N×Bool))
    (covers : ∀i b,0<qty i → ∃j,source j=some (i,b))
    (qtyFit : ∀i,qty i<2^native) (idFit : ∀i,id i<2^native)
    (sitesFit : siteLast h (2^W) k<2^native)
    (sizeRead : ∀j,size.eval m (j.val:Word native)=((source j).elim 0 (fun z=>qty z.1):ℕ))
    (idRead : ∀j i side,source j=some (i,side) → 0<qty i → number.eval m (j.val:Word native)=(id i:Word native))
    (selfRead : ∀j i side,source j=some (i,side) → 0<qty i →
      Resolved S chart self m (j.val:Word native) (port (i,side)))
    (peerRead : ∀j i side,source j=some (i,side) → 0<qty i →
      Resolved S chart peer m (j.val:Word native) (port (i,!side)))
    (mounted : ∀p : Public S h W k attempts,
      siteTable.read m ((name (site S p)).val:Word native)=
        (((name (site S p)).val*stride k S.degree attempts:ℕ):Word native))
    (fit : (field.expr size number (socketSite chart peer)).Fits native base)
    (addrFit : (RoleWidths.destination base sink (field.expr size number (socketSite chart peer))
      (RoleWidths.offset siteTable (socketSite chart self) (socketCode chart self))).Fits native base)
    (space : base+Nport ≤ scratch) (word : scratch+count+count<2^native) (sinkLow : sink<base) :
    let val := field.expr size number (socketSite chart peer)
    let addr := RoleWidths.destination base sink val (RoleWidths.offset siteTable (socketSite chart self) (socketCode chart self))
    let data := field.data (fun ib : Fin N×Bool=>qty ib.1) (fun ib=>id ib.1) (fun ib=>(name (site S (port (ib.1,!ib.2)))).val)
    ∃ out,(ProtocolRAMTurnReplay.program native base Nport scratch count addr val).Exec m out
        (ProtocolRAMTurnReplay.work Nport count addr val) ∧
      (∀t : Fin Nport,out (base+t.val)=(RoleWidths.shelf port (shelfSlot S) data t:Word native)) ∧
      ∀t,(t<base ∨ base+Nport ≤ t) → (t<scratch ∨ scratch+count+count ≤ t) → t≠sink → out t=m t := by
  intro val addr data
  let widthAt (ib : Fin N × Bool) := qty ib.1
  let ordinalAt (ib : Fin N × Bool) := id ib.1
  let oppositeAt (ib : Fin N × Bool) := (name (site S (port (ib.1, !ib.2)))).val
  have live (i : Fin N × Bool) (hi : 0 < data i) : 0 < qty i.1 :=
    field.positive_width widthAt ordinalAt oppositeAt i hi
  apply RoleWidths.run_all port (shelfSlot S) data base scratch sink val
    (RoleWidths.offset siteTable (socketSite chart self) (socketCode chart self)) m source
  · rintro ⟨i,b⟩ hi
    exact covers i b (live (i,b) hi)
  · intro ib
    have sFit : (name (site S (port (ib.1,!ib.2)))).val<2^native :=
      (Nat.le_of_lt_succ (Fin.isLt _)).trans_lt sitesFit
    exact field.below widthAt ordinalAt oppositeAt ib (2^native) (Nat.two_pow_pos _) (qtyFit _) (idFit _) sFit
  · exact fit
  · exact addrFit
  · exact space
  · exact word
  · exact sinkLow
  · intro j
    cases found : source j with
    | none=>
      have wr := sizeRead j
      simp only [found,Option.elim_none] at wr
      exact field.zero_read size number (socketSite chart peer) m _ wr
    | some ib=>
      obtain ⟨i,b⟩ := ib
      have wr := sizeRead j
      simp only [found,Option.elim_some] at wr
      change (field.expr size number (socketSite chart peer)).eval m (j.val:Word native) =
        (field.data widthAt ordinalAt oppositeAt (i,b) : Word native)
      rw [field.at_unit widthAt ordinalAt oppositeAt (i,b)]
      exact field.read size number (socketSite chart peer) m (j.val:Word native)
        (qty i) (id i) (name (site S (port (i,!b)))).val (qtyFit i) wr
        (idRead j i b found) (fun h=>(peerRead j i b found h).1)
  · intro j ib found hi
    have resolved := selfRead j ib.1 ib.2 found (live ib hi)
    rw [shelf_index]
    apply RoleWidths.offset_at
    · rw [resolved.1]
      exact mounted _
    · exact resolved.2

theorem scatter_field (field : RoleField) (base scratch sink : ℕ) (size number : Expr)
    (chart : Chart) (self peer : Socket) (siteTable : Bank) (m : Memory native)
    (qty id : Fin N→ℕ) (source : Fin count → Option (Fin N×Bool))
    (covers : ∀i b,0<qty i → ∃j,source j=some (i,b))
    (qtyFit : ∀i,qty i<2^native) (idFit : ∀i,id i<2^native)
    (sitesFit : siteLast h (2^W) k<2^native)
    (sizeRead : ∀j,size.eval m (j.val:Word native)=((source j).elim 0 (fun z=>qty z.1):ℕ))
    (idRead : ∀j i side,source j=some (i,side) → 0<qty i → number.eval m (j.val:Word native)=(id i:Word native))
    (selfRead : ∀j i side,source j=some (i,side) → 0<qty i →
      Resolved S chart self m (j.val:Word native) (port (i,side)))
    (peerRead : ∀j i side,source j=some (i,side) → 0<qty i →
      Resolved S chart peer m (j.val:Word native) (port (i,!side)))
    (mounted : ∀p : Public S h W k attempts,
      siteTable.read m ((name (site S p)).val:Word native)=
        (((name (site S p)).val*stride k S.degree attempts:ℕ):Word native))
    (fit : (field.expr size number (socketSite chart peer)).Fits native base)
    (addrFit : (RoleWidths.destination base sink (field.expr size number (socketSite chart peer))
      (RoleWidths.offset siteTable (socketSite chart self) (socketCode chart self))).Fits native base)
    (space : base+Nport ≤ scratch) (word : scratch+count+count<2^native) (sinkLow : sink<base) :
    let val := field.expr size number (socketSite chart peer)
    let addr := RoleWidths.destination base sink val (RoleWidths.offset siteTable (socketSite chart self) (socketCode chart self))
    let data := field.data (fun ib : Fin N×Bool=>qty ib.1) (fun ib=>id ib.1) (fun ib=>(name (site S (port (ib.1,!ib.2)))).val)
    ∃ out,(ProtocolRAMTurnReplay.program native base Nport scratch count addr val).Exec m out
        (ProtocolRAMTurnReplay.work Nport count addr val) ∧
      (∀q : Public S h W k attempts,out (base+(shelfSlot S q).val)=(RoleWidths.shelf port (shelfSlot S) data ((shelfSlot S) q):Word native)) ∧
      ∀t,(t<base ∨ base+Nport ≤ t) → (t<scratch ∨ scratch+count+count ≤ t) → t≠sink → out t=m t := by
  dsimp only
  obtain ⟨out,exec,each,frame⟩:=scatter_field_all S π depth mark unique rows field base scratch sink size number
    chart self peer siteTable m qty id source covers qtyFit idFit sitesFit sizeRead idRead selfRead peerRead
    mounted fit addrFit space word sinkLow
  exact ⟨out,exec,fun q=>each (shelfSlot S q),frame⟩

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end
end OAI
