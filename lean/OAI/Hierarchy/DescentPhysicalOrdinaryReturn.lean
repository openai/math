import OAI.Hierarchy.DescentVenueMetadataPaidField
import OAI.Hierarchy.DescentOrdinaryArgumentsAfter
import OAI.Hierarchy.DescentDatedOrdinaryNodeBanks
import OAI.Hierarchy.DescentOrdinaryFinalCount

namespace OAI
/-! # The original compact successor and its source metadata before the pair-count store -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
open scoped Fin.CommRing
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (floor : ℕ) (B : StageVenueTail.Sources)
local notation "start" => v.rasterEnd floor
local notation "s₂" => v.metaStart floor
local notation "s₃" => v.metaEnd floor
local notation "stop" => v.operandEnd floor
local notation "c" => v.nodeChart
local notation "pb" => v.metadata.paidBits
local notation "sb" => v.resolver.size+2
local notation "p" => (fun x:Fin (c).blocks=>v.venue.metadataPaid B x.val)
local notation "spanSource" => v.spanVectors floor
local notation "venuePhase" => v.venue.phase B start
local notation "fieldSource" => v.finalSources floor
private def resultCode (w : ℕ) :=
  (((venuePhase w).program.seq ((c).ordinaryProgram s₂ pb sb w p spanSource)).seq (v.finalChart.program fieldSource s₃ w))
private def resultTime (w : ℕ) := ((venuePhase w).ticks+(c).ordinaryTime s₂ pb sb p spanSource)+v.finalChart.ticks fieldSource s₃
private def resultState {w : ℕ} (m : Memory w) :=
  v.finalChart.image fieldSource s₃ ((c).ordinaryImage s₂ pb sb p spanSource ((venuePhase w).image m))

structure ResultRoom (w : ℕ) : Prop where
  chart : v.metadata.chart=c
  digit : v.metadata.spanBits=sb
  geometry : v.operandBook=v.finalChart
  venue : v.venue.Space B start w
  paid : ∀x,(p x).Fits w s₂
  spans : ∀x j,(spanSource x j).Fits w s₂
  operands : v.finalChart.Early fieldSource s₃ w
  limit : stop< 2^w

theorem result_run {w : ℕ} (m : Memory w) (room : v.ResultRoom floor B w) :
    (v.resultCode floor B w).Exec m (v.resultState floor B m) (v.resultTime floor B w) ∧
    CheapCode (v.resultCode floor B w) ∧
    ∀j,j< start ∨ stop≤ j→v.resultState floor B m j=m j:=by
  have s : start≤ s₂:=by change start≤ v.venue.endAddress start;rw [v.venue.translates];omega
  have t : s₂≤ s₃:=by rw [metaEnd,v.metadata.ordinary_translate];omega
  have u : s₃≤ stop:=by rw [operandEnd,v.operandBook.affine];omega
  have nodeEndAt : (c).ordinaryEnd s₂ pb sb=s₃:=by
    change (c).ordinaryEnd s₂ pb sb=v.metadata.chart.ordinaryEnd s₂ pb v.metadata.spanBits
    rw [room.chart,room.digit]
  have end_:=(v.after_end floor room.geometry)
  have mounted:=v.venue.any B start m room.venue
  have nodes:=(c).ordinaryAny s₂ pb sb p spanSource ((venuePhase w).image m) room.paid room.spans
    (nodeEndAt.le.trans_lt (u.trans_lt room.limit))
  have copied:=v.finalChart.any fieldSource s₃ ((c).ordinaryImage s₂ pb sb p spanSource ((venuePhase w).image m)) room.operands (end_.le.trans_lt room.limit)
  refine ⟨?_,cheap_seq (cheap_seq (venuePhase w).cheap nodes.2.2) copied.2.1,?_⟩
  · intro P R K machine
    exact Procedure.Exec.then (Procedure.Exec.then mounted.1 nodes.1) copied.1 machine
  · intro j h
    exact (copied.2.2 _ (h.imp (fun x=>x.trans_le (s.trans t)) (fun x=>end_.le.trans x))).trans
      ((nodes.2.1 _ (h.imp (fun x=>x.trans_le s) (fun x=>nodeEndAt.le.trans (u.trans x)))).trans
      (mounted.2 _ (h.imp_right (fun x=>t.trans (u.trans x)))))

def returnPhase (w : ℕ) (room : v.ResultRoom floor B w) : NativePhase w :=
  ⟨v.resultCode floor B w,v.resultTime floor B w,v.resultState floor B,(v.result_run floor B (fun _=>0) room).2.1⟩

theorem returnPhase_run (w : ℕ) (room : v.ResultRoom floor B w) (m : Memory w) :
    (v.returnPhase floor B w room).Runs m ∧
    ∀a,a< start ∨ stop≤ a→(v.returnPhase floor B w room).image m a=m a :=
  ⟨(v.result_run floor B m room).1,(v.result_run floor B m room).2.2⟩

/-- Output metadata and all seven new pointer planes occupy fresh banks after the venue. -/
theorem return_below_venue (w : ℕ) (room : v.ResultRoom floor B w) (m : Memory w)
    {a : ℕ} (low : a< s₂) : (v.returnPhase floor B w room).image m a=(venuePhase w).image m a :=by
  have above : s₂≤ s₃:=by rw [metaEnd,v.metadata.ordinary_translate];omega
  have stop_ : s₃≤ stop:=by rw [operandEnd,v.operandBook.affine];omega
  have nodeEndAt : (c).ordinaryEnd s₂ pb sb=s₃:=by
    change _=v.metadata.chart.ordinaryEnd s₂ pb v.metadata.spanBits
    rw [room.chart,room.digit]
  have nodes:=(c).ordinaryAny s₂ pb sb p spanSource ((venuePhase w).image m) room.paid room.spans
    (nodeEndAt.le.trans_lt (stop_.trans_lt room.limit))
  have copied:=v.finalChart.any fieldSource s₃ ((c).ordinaryImage s₂ pb sb p spanSource ((venuePhase w).image m)) room.operands ((v.after_end floor room.geometry).le.trans_lt room.limit)
  exact (copied.2.2 a (.inl (low.trans_le above))).trans (nodes.2.1 a (.inl low))

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
