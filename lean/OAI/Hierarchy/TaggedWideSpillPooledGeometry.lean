import OAI.Hierarchy.TaggedWideSpillPooledChart
import OAI.Hierarchy.TaggedWideSpillPooledSnapshot

namespace OAI
/-! # Canonical sparse boundary registers for the active dated commodity rows -/
noncomputable section
namespace Hierarchy.ProtocolRAMDateSpillPosition
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles WireTelescope SettledMatrix
open ProtocolRAMPaidTurnPlacement ProtocolRAMTurnOrder ProtocolRAMTurnChart ProtocolRAMDateSpillRank
open scoped Classical
set_option quotPrecheck false
variable {h W k edges : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (B : Mount (S:=S) π (name (h:=h) (W:=W) (k:=k)) edges) (pad : Chord (siteLast h (2^W) k+1))
local notation "Gd" => Commodity (Fin (2^h)) (Stages h (2^W)) k
local notation "Full" => SettledMatrix.Source edges Gd (Columns h (2^W)×Fin k)
local notation "names" => (ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k).symm
local notation "inj" => (siteNumber h (2^W) k).injective
local notation "D" => B.datedLayout inj pad
local notation "len" => ProtocolRAMTurnGeometry.length ∘ names
local notation "small" => Fintype.card (TurnShelf.Positions (D).routes)
local notation "order" => positionOrder S π B pad
variable (o : ProtocolRAM.Calendar.CoreRoute.Orders h (2^W) k) (base : ℕ) (w : Words)
local notation "visit" => ProtocolRAMVisitAdjacency.vertex len (fun a=>ProtocolRAMTurnEdges.visit B inj pad (names a))
local notation "turn" i => record (ProtocolRAMTurnGeometry.header o base names) w visit (chartReal S π B pad i)

theorem registered_fields (i : Fin small)
    (observed : rev w (ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k (source ((D).num (order i).1))).val =
      ProtocolRAMTurnStepOrder.reverse B inj pad (source ((D).num (order i).1))) :
    let x:=source (C:=Columns h (2^W)×Fin k) ((D).num (order i).1)
    let t:=turn i
    t.item=(ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k x).val ∧ t.origin=ProtocolRAMTurnGeometry.origin o x ∧
    t.length=ProtocolRAMTurnGeometry.length x ∧ t.reverse=ProtocolRAMTurnStepOrder.reverse B inj pad x ∧
    t.position=(order i).2.val ∧ t.site=((sparseSpine S π B pad ((D).num (order i).1)).visit (order i).2).val := by
  intro x t
  let a:=Canonical.posn B inj pad (chartReal S π B pad i)
  have named:names a.1=x:=chart_source S π B pad i
  have idx:a.1=(ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k) x:=by rw [show x=names a.1 from named.symm];exact ((ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k).apply_symm_apply a.1).symm
  have atPhase:a.2.val=(order i).2.val:=
    congrArg (fun p:ProtocolRAMLiveTurnOrder.Boundaries S π B pad=>p.2.val) (chart_registered S π B pad i)
  have revAt:rev w a.1.val=ProtocolRAMTurnStepOrder.reverse B inj pad (names a.1) := by rw [named,idx];exact observed
  obtain ⟨item,origin,length,direction,position,_⟩:=
    Canonical.fields B inj pad o base w (chartReal S π B pad i) revAt
  exact ⟨item.trans (congrArg Fin.val idx),origin.trans (congrArg _ named),length.trans (congrArg _ named),
    direction.trans (congrArg _ named),position.trans atPhase,chart_site S π B pad i⟩

/-- Numerical predecessor and successor addresses are those written by the
actual truncated rank traversal. -/
theorem neighbor_addresses (g : Gd) (t : ProtocolRAMTurnItinerary.Turn)
    (j : Fin (((D).data.steps (.inr (.inl g))).length+1))
    (origin : t.origin=ProtocolRAMTurnGeometry.origin (edges:=edges) o (.inr (.inl g)))
    (length : t.length=ProtocolRAM.Calendar.CoreRoute.arity g)
    (reversed : t.reverse=ProtocolRAMTurnStepOrder.reverse B inj pad (.inr (.inl g)))
    (position : t.position=j.val) :
    ∀q : Fin ((D).data.steps (.inr (.inl g))).length,
      (q.succ=j → t.occurrence false=edges+(goodIndex B inj pad o g q).val) ∧
      (q.castSucc=j → t.occurrence true=edges+(goodIndex B inj pad o g q).val) := by
  intro q
  have count : ((D).data.steps (.inr (.inl g))).length=ProtocolRAM.Calendar.CoreRoute.arity g:=
    ProtocolRAMTurnEdges.canonical_length B inj pad (.inr (.inl g))
  have paid:q.val<t.length:=q.isLt.trans_le (count.trans length.symm).le
  have emitted:=goodIndex_word B inj pad o g q
  constructor
  · intro eq
    exact (ProtocolRAMTurnStepOrder.previous t q.val ((congrArg Fin.val eq).trans position.symm) paid).trans (by
      rw [origin,length,reversed];exact emitted.symm)
  · intro eq
    exact (ProtocolRAMTurnStepOrder.next t q.val ((congrArg Fin.val eq).trans position.symm) paid).trans (by
      rw [origin,length,reversed];exact emitted.symm)

end Hierarchy.ProtocolRAMDateSpillPosition
end

end OAI
