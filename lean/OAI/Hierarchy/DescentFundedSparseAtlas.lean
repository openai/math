import OAI.Hierarchy.DescentIssuedQuantityPlanes
import OAI.Hierarchy.DescentFundedRosterInput

namespace OAI
/-! # Coordinates of every real and vacant funded reset row -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentGL DescentColonies DescentDenseHostOrder DescentPaidResidentCount
open DescentSIMDLookup DescentPackedZip DescentFundedCensus DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 16000
set_option maxHeartbeats 1000000
variable {F P:Type} [Field F] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ} {ctl:ResetRates G S k D n h C f g cut tail}
  {cap:Reached W G q ε S k i z D wire hist} (B:ClosedReset cap ctl)
  {p b H M w:ℕ} (r:B.Recorded p) (oldRoom:Fintype.card cap.V≤H)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans cap.vertex
local notation "rank" => (vertex).trans (Fin.castLEEmb oldRoom)
local notation "rawID" => (Z).rawHostRank T rank
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cc" => (T).commonDepth
local notation "dep" => GroupStage.depthBound D n f g
local notation "pool" => DescentDenseHostOrder.roster (Z).graph ((Z).k-cc) dep
local notation "lit" => Recorded.realActor (reset:=B) (shapes B) (rack B oldRoom)
local notation "coords" v:arg => (Z).hostFields T rank ((Z).placed T v)

theorem funded_present (u:(coarse).graph.Site) :
    lit (coords u).2 (coords u).1 ((Z).blockId T u)=1 :=by
  rw [old_sheet]
  change (Z).sparseActor T rank (rawID ((Z).placed T u)) ((Z).blockId T u)=1
  rw [ResetInput.sparse_known]
  split
  · rfl
  · next absent => exact (absent (((Z).reset_occupied T _ _).mp ⟨u,rfl,rfl⟩)).elim

theorem funded_occupied (v:Fin H) (j:Fin (pool).card) (hi:DescentColonies.Block cc) :
    lit j v hi≠0 ↔ ∃u:(coarse).graph.Site,rawID ((Z).placed T u)=finProdFinEquiv (v,j) ∧ (Z).blockId T u=hi :=by
  constructor
  · rw [old_sheet]
    intro occupied
    obtain ⟨host,matched⟩:=((Z).rack_flag T rank _).mp ⟨hi,occupied⟩
    rw [←matched,ResetInput.sparse_known] at occupied
    have active : ResetInput.emits (Z) T host.val hi:=by by_contra inactive;simp [inactive] at occupied
    obtain ⟨u,location,block⟩:=((Z).reset_occupied T host.val hi).mpr active
    have same:(Z).placed T u=host:=Subtype.ext location
    exact ⟨u,(congrArg rawID same).trans matched,block⟩
  · rintro ⟨u,e,b₀⟩
    have id:(coords u)=(v,j):=finProdFinEquiv.injective e
    have occupied := funded_present B oldRoom u
    rw [id,b₀] at occupied
    rw [occupied]
    decide

theorem funded_shape (u:(coarse).graph.Site) : shapes B (coords u).2=
    DescentDenseHostOrder.shape (Z).graph ((Z).commonName T u) :=by
  change (((Z).shapeOrder T).symm ((Z).shapeOrder T ((Z).localShape T ((Z).placed T u)))).val=_
  rw [Equiv.symm_apply_apply]
  rfl

/-- Writing the real-site charges at their issued host and shape together
with the geometric occupancy bit determines every padded word. -/
theorem funded_complete (val : Fin (pool).card→Fin H→DescentColonies.Block cc→Cell b)
    (actual : ∀u : (coarse).graph.Site,val (coords u).2 (coords u).1 ((Z).blockId T u)=
      ((Reset.payee B r ((Z).resetNames T u):ℕ):Cell b))
    (empty : ∀j v hi,lit j v hi=0→val j v hi=0) (j : Fin (pool).card) (v : Fin H) (hi : DescentColonies.Block cc) :
    val j v hi=payable B r oldRoom (finProdFinEquiv (v,j)) hi :=by
  by_cases used:lit j v hi=0
  · rw [empty j v hi used,payable,dite_eq_right (by simp [←funded_occupied B oldRoom,used])]
  · obtain ⟨u,addr,block⟩:=(funded_occupied B oldRoom v j hi).mp used
    have same : coords u=(v,j):=finProdFinEquiv.injective addr
    calc
      val j v hi=val (coords u).2 (coords u).1 ((Z).blockId T u):=by rw [same,block]
      _ = _:=actual u
      _ = _:=by rw [←payable_at B r oldRoom u,addr,block]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
