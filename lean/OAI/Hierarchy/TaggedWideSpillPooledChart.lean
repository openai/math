import OAI.Hierarchy.TaggedWideSpillPooledPosition
import OAI.Hierarchy.ProtocolRAMTurnCanonicalGeometry
import OAI.Hierarchy.ProtocolRAMDateSpillTurnInputs

namespace OAI
/-! # The actual stored turn count and register-ordered sparse geometry -/
noncomputable section
namespace Hierarchy.ProtocolRAMDateSpillPosition
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe ProbeStage CoreBoard ReportSockets HistoryRoles WireTelescope SettledMatrix
open ProtocolRAMPaidTurnPlacement ProtocolRAMTurnOrder ProtocolRAMTurnShelf
open scoped Classical
set_option quotPrecheck false
variable {h W k edges : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (B : Mount (S:=S) π (name (h:=h) (W:=W) (k:=k)) edges) (pad : Chord (siteLast h (2^W) k+1))
local notation "Gd" => Commodity (Fin (2^h)) (Stages h (2^W)) k
local notation "Full" => SettledMatrix.Source edges Gd (Columns h (2^W)×Fin k)
local notation "Sub" => SettledMatrix.Source edges Gd Empty
local notation "names" => (ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k).symm
local notation "inj" => (siteNumber h (2^W) k).injective
local notation "L" => B.matrixLayout inj pad
local notation "D" => B.datedLayout inj pad
local notation "len" => ProtocolRAMTurnGeometry.length ∘ names
local notation "small" => Fintype.card (TurnShelf.Positions (D).routes)
local notation "order" => positionOrder S π B pad

def chartBoundary : Fin (turns len) ≃ ProtocolRAMLiveTurnOrder.Boundaries S π B pad :=
  (Canonical.posn B inj pad).trans
    (Equiv.sigmaCongrLeft (β:=fun t:Full=>Fin (((L).steps t).length+1)) names)

def chartReal : Fin small ↪ Fin (turns len) :=
  (order).toEmbedding.trans ((boundaryOrder S π B pad).toEmbedding.trans
    ((boundary S π B pad).trans (chartBoundary S π B pad).symm.toEmbedding))

theorem chart_registered (i : Fin small) :
    chartBoundary S π B pad (chartReal S π B pad i)=
      boundary S π B pad (boundaryOrder S π B pad (order i)) :=
  (chartBoundary S π B pad).apply_symm_apply _

theorem chart_source (i : Fin small) :
    names (Canonical.posn B inj pad (chartReal S π B pad i)).1=source ((D).num (order i).1) :=
  congrArg Sigma.fst (chart_registered S π B pad i)

theorem chart_covers (col : Fin (turns len)→Fin 7→ℕ)
    (goods : ∀i,col i 4≠0→∃g,names (raw len i).1=.inr (.inl g))
    (i : Fin (turns len)) (positive : col i 4≠0) : i∈Set.range (chartReal S π B pad) := by
  let b:=chartBoundary S π B pad i
  obtain ⟨g,hg⟩:=goods i positive
  let x : Sub:=.inr (.inl g)
  have eqn : source x=b.1:=hg.symm
  let u:=b.2.cast (congrArg (fun t:Full=>((L).steps t).length+1) eqn.symm |>.trans
    (congrArg (fun l=>l.length+1) (steps S π B pad x)))
  let c:=(boundaryOrder S π B pad).symm ⟨x,u⟩
  refine ⟨(order).symm c,(chartBoundary S π B pad).injective ?_⟩
  rw [chart_registered,Equiv.apply_symm_apply]
  change boundary S π B pad (boundaryOrder S π B pad ((boundaryOrder S π B pad).symm ⟨x,u⟩))=b
  rw [Equiv.apply_symm_apply]
  exact Sigma.ext eqn ((Fin.heq_ext_iff (congrArg (fun t:Full=>((L).steps t).length+1) eqn)).mpr rfl)

theorem chart_site (i : Fin small) :
    ProtocolRAMVisitAdjacency.vertex len (fun a=>ProtocolRAMTurnEdges.visit B inj pad (names a)) (chartReal S π B pad i)=
      ((sparseSpine S π B pad ((D).num (order i).1)).visit (order i).2).val := by
  let r:=chartReal S π B pad i
  have fromBank : atBoundary S π B pad (chartBoundary S π B pad r)=
      (Canonical.spines B inj pad (Canonical.posn B inj pad r).1).visit (Canonical.posn B inj pad r).2 := rfl
  exact (Canonical.visit_at B inj pad r).symm.trans (congrArg Fin.val
    (fromBank.symm.trans ((congrArg (atBoundary S π B pad) (chart_registered S π B pad i)).trans
      (registered_visit S π B pad _))))

/-- Only spill weights on ordinary, live source rows are read; every
other raw chart width is forced to zero by the calibrated rank publisher. -/
theorem chart_widths (o : ProtocolRAM.Calendar.CoreRoute.Orders h (2^W) k) (base : ℕ)
    (w : ProtocolRAMTurnChart.Words) (vals : ProtocolRAMTurnItinerary.Values) (oldBase newBase : ℕ→ℕ)
    (spill : Gd→ℕ) (weight : ∀g,w.width (ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k (.inr (.inl g))).val=spill g)
    (goods : ∀x:Full,0<w.width (ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k x).val→∃g,x=.inr (.inl g))
    (i : Fin small) :
    let q:=chartReal S π B pad i
    let t:=ProtocolRAMTurnChart.record (ProtocolRAMTurnGeometry.header o base names) w
      (ProtocolRAMVisitAdjacency.vertex len (fun a=>ProtocolRAMTurnEdges.visit B inj pad (names a))) q
    ProtocolRAM.DateSpill.Turns.fieldWords t vals oldBase newBase 4=(D).bits spill (order i).1 := by
  intro q t
  let wfull:=Layout.available (fun _:Fin edges=>0) spill (fun _:Columns h (2^W)×Fin k=>0) (fun _=>0)
  have all (x:Full) : w.width (ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k x).val=wfull x := by
    rcases x with e|g|c
    · apply Nat.eq_zero_of_not_pos
      intro on
      obtain ⟨_,bad⟩:=goods (.inl e) on
      cases bad
    · exact weight g
    · apply Nat.eq_zero_of_not_pos
      intro on
      obtain ⟨_,bad⟩:=goods (.inr (.inr c)) on
      cases bad
  have h:=Canonical.widths B inj pad o base w vals (fun t=>wfull (names t)) (fun t=>by
    simpa only [Equiv.apply_symm_apply] using all (names t)) q
  change ProtocolRAM.DateSpill.Turns.fieldWords t vals oldBase newBase 4=wfull (names (Canonical.posn B inj pad q).1) at h
  rw [h,chart_source]
  change wfull (source ((D).num (order i).1))=
    Layout.available (fun _:Fin edges=>0) spill (fun _:Empty=>0) (fun _=>0) ((D).num (order i).1)
  rcases (D).num (order i).1 with e|g|dead
  · rfl
  · rfl
  · exact dead.elim

/-- A seven-field page with its genuine live register indices has the exact
same five shelf words after removing dormant rows, at *every* physical seat. -/
theorem chart_word (col : Fin (turns len)→Fin 7→ℕ)
    (goods : ∀i,col i 4≠0→∃g,names (raw len i).1=.inr (.inl g))
    {sites slots w : ℕ} (put : Live col ↪ Seats sites slots) (f : Fin 5) (a : Seats sites slots) :
    entry (W:=w) col put f a=entry (col ∘ chartReal S π B pad)
      ((restrictedLive col (chartReal S π B pad)).trans put) f a :=
  entry_restrict col (chartReal S π B pad) (chart_covers S π B pad col goods) put f a

end Hierarchy.ProtocolRAMDateSpillPosition
end

end OAI
