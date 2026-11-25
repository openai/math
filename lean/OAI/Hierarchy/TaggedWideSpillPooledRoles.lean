import OAI.Hierarchy.TaggedWideSpillPooledSnapshot
import OAI.Hierarchy.ProtocolRAMDateSpillPaidHalves
import OAI.Hierarchy.TaggedWireLiveRoleSides

namespace OAI
/-! # Native role and orientation readbacks for the dated pooled row -/
noncomputable section
namespace Hierarchy.ProtocolRAM.DateSpill
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard WireTelescope HistoryRoles RoleProgram
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open ProtocolRAM.Calendar ProtocolRAMTurnItinerary ProtocolRAMTurnSnapshot
open scoped Classical Fin.CommRing
set_option quotPrecheck false

variable {h W k w attempts : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (board : RoleProgram.Board) (B : Mount (S:=S) π (name (h:=h) (W:=W) (k:=k)) board.edges)
    (pad : Chord (siteLast h (2^W) k+1))
local notation "P" => Public S h W k attempts
local notation "G" => Commodity (Fin (2^h)) (Stages h (2^W)) k
local notation "inj" => (siteNumber h (2^W) k).injective
local notation "D" => B.datedLayout inj pad

private theorem natural_word {m : Word w} {n : ℕ} (h : m=(n:Word w)) (small : n<2^w) : m.val=n :=
  (congrArg Fin.val h).trans (Fin.val_cast_of_lt small)

/-- Original directed sites and the two old sorted role words all come from
the original commodity row. Its width at the end of the computation can be zero. -/
theorem original_good_roles (key rank : Bank) (m : Memory w) (i : Fin board.old) (g : G)
    (pay : Fin board.edges→Bool→P) (sites : siteLast h (2^W) k+1≤2^w)
    (fields : ∀b,let p:=publicRoleFor S π pay (.inr (.inl g))
      (board.forwardSite b).read m (i.val:Word w)=((name (HistoryRoles.site S (p b))).val:Word w) ∧
      (board.oldRole b).read m (i.val:Word w)=(ProtocolRAMTurnOperands.printed S false p b false:Word w))
    (roleFit : ∀b,ProtocolRAMTurnOperands.printed S false (publicRoleFor S π pay (.inr (.inl g))) b false<2^w) :
    let v:=values (board.itinerary key rank) m
    let p:=publicRoleFor S π pay (.inr (.inl g))
    decide (¬((board.forwardSite false).read m (i.val:Word w)).val<((board.forwardSite true).read m (i.val:Word w)).val)
      =ProtocolRAMTurnStepOrder.reverse B inj pad (.inr (.inl g)) ∧
    v.oldSource i.val=ProtocolRAMTurnOperands.printed S false p false false ∧
      v.oldTarget i.val=ProtocolRAMTurnOperands.printed S false p true false := by
  intro v p
  have side (b : Bool) : name (HistoryRoles.site S (p b))=(D).data.goods.vertex g b := by
    change name (goodsSite (goods π (g,b)))=_
    rw [goods_site]
    cases b <;>rfl
  have raw (b : Bool) := natural_word (fields b).1 ((name (HistoryRoles.site S (p b))).isLt.trans_le sites)
  refine ⟨?_,natural_word (fields false).2 (roleFit false),natural_word (fields true).2 (roleFit true)⟩
  rw [raw false,raw true,side false,side true]
  rfl

/-- Every live dated use of a settled paid row reads both printed role IDs
and the lower physical endpoint in the same finite-field RAM image. -/
theorem paid_hop_roles (depth : ℕ) (mark : ReportSockets.Marks h W k attempts) (unique : ReportSockets.Exclusive mark)
    (key rank : Bank) (m : Memory w) (beforeWidth : Fin board.old→ℕ) (total : Fin board.edges→ℕ)
    (before : ∀i,0<beforeWidth i→Bool→P) (after : ∀e,0<total e→Bool→P)
    (auth : board.LiveReads S beforeWidth total before after m)
    (id : {e:Fin board.edges // 0<total e}→Catalogue S π depth mark)
    (aligned : ∀e,filledChord B.actual pad e.val=sorted S π depth mark (.inl (id e)))
    (ports : ∀e on b,after e on b=.inl (paid S π depth mark unique (id ⟨e,on⟩,b)))
    (e : Fin board.edges) (positive : 0<total e) (sites : siteLast h (2^W) k+1≤2^w)
    (roleFit : ∀b,ProtocolRAMTurnOperands.printed S true (after e positive) b false<2^w) :
    let v:=values (board.itinerary key rank) m
    let roles:=ProtocolRAMTurnStepOrder.liveCode S true total after e
    v.tailSite e.val=((D).edge e).val.1.val ∧ v.tailRole e.val=roles false ∧ v.headRole e.val=roles true := by
  intro v roles
  have ends:=ProtocolRAMPaidTurnPlacement.paid_printed_ends S π depth mark unique B pad e (id ⟨e,positive⟩)
    (after e positive) (aligned ⟨e,positive⟩) (ports e positive)
  have low : ProtocolRAMTurnOperands.printed S true (after e positive) false true=((D).edge e).val.1.val:=ends.1
  have tail:=ProtocolRAMTurnSnapshot.reported_site S board auth key rank e positive (low.trans_lt (((D).edge e).val.1.isLt.trans_le sites))
  refine ⟨tail.trans low,?_,?_⟩
  · simpa [roles,ProtocolRAMTurnStepOrder.liveCode,positive] using
      ProtocolRAMTurnSnapshot.reported_role S board auth key rank e positive false (roleFit false)
  · simpa [roles,ProtocolRAMTurnStepOrder.liveCode,positive] using
      ProtocolRAMTurnSnapshot.reported_role S board auth key rank e positive true (roleFit true)
end Hierarchy.ProtocolRAM.DateSpill
end

end OAI
