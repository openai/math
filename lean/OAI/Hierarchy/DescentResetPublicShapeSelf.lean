import OAI.Hierarchy.DescentResetCompactGeometryPosted
import OAI.Hierarchy.DescentResetCompactGeometryRead
import OAI.Hierarchy.DescentResetStemHalo

namespace OAI
/-! # Both authentic trunk inputs on the compact actor raster -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentSIMDLookup DescentPackedZip
open DescentCommonHost DescentResetCompactGeometry DescentActorRaster DescentResetStemCompactOrder DescentParallelBase
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "rad" => (Z).k-(T).commonDepth
local notation "height" => GroupStage.depthBound D n f g
local notation "pal" => DescentDenseHostOrder.roster (Z).graph rad height
local notation "used" => Fintype.card B.next.V
local notation "groups" => S.groupCount (i+1)
variable {H0 H : ℕ} (prev : Fintype.card input.V≤H0) (next : Fintype.card B.next.V≤H)
local notation "oldRank" => (vertex).trans (Fin.castLEEmb prev)
local notation "raw" => (Z).rawHostRank T oldRank
local notation "dense" => (Z).denseHostRank T oldRank
local notation "size" => H0*(pal).card

def publicGeometry (H0 H M b : ℕ) (st : Store) (ranks : Bank) (base geom : ℕ) (self : Bank) (broadcast : ℕ) : Chart:=
  ⟨st.inverse,st.count (H0*(pal).card),ranks,base,geom,self,broadcast,H,H0,(pal).card,groups,M,b⟩

/-- The upstream scalar ranks here are the actual old roster self column.
The compact→raw directory is the one retained by successor_actors_directory. -/
theorem public_shape_self {b M bw base geom broadcast : ℕ} (st : Store) (ranks selfBank : Bank)
    (m : Memory bw) (self : Fin H0→Cell b)
    (rr : (publicGeometry B H0 H M b st ranks base geom selfBank broadcast).Room bw)
    (count : m (st.ranks.base+size)=(used:Word bw))
    (inverse : ∀v:B.next.V,m (st.inverse.base+(dense v).val)=((raw v).val:Word bw))
    (ranked : ∀j,m (ranks.base+j.val)=((self j).val:Word bw))
    (selfRank : ∀v:B.reset.V,(self (oldRank v)).val=compress (hostDomain input.placement input.vertex (B.frame.host.symm v))
      (input.vertex (B.frame.host.symm v)).val)
    (width : (pal).card≤2^b) (space : used≤ st.inverse.size) (oldSpace : H0≤ranks.size) :
    let chart:=publicGeometry B H0 H M b st ranks base geom selfBank broadcast
    ∃shape halo : Fin H→Cell b,
      (chart.native rr).Runs m ∧
      Source (chart.port 0) (fun v (_ : Fin groups)=>shape v) M (chart.finalMem m) ∧
      Source (chart.port 1) (fun v (_ : Fin groups)=>halo v) M (chart.finalMem m) ∧
      (∀v:B.next.V,∀g x,
        (shape ((dense v).castLE next)).val=((Z).rawHostRank T vertex v).val%(pal).card ∧
        (halo ((dense v).castLE next)).val=haloNumber B ((g,v),x) (receiverRoot B ((g,v),x)).1) ∧
      ∀h,used≤h.val→shape h=0 ∧ halo h=0:=by
  intro chart
  let e:=compactActorOrder B prev
  let name:=compactActorName B prev
  let root (i : Fin used):=oldRank (position (Z).graph (e.symm i).val)
  have pos (i : Fin used) : 0<(pal).card:=lt_of_le_of_lt (Nat.zero_le _) ((Z).hostFields T oldRank (e.symm i)).2.isLt
  let chip (i : Fin used):Cell b:=⟨(name i).val%(pal).card,(Nat.mod_lt _ (pos i)).trans_le width⟩
  have actual (j : Fin used) : m (st.inverse.base+j.val)=((name j).val:Word bw):=by
    have seen:=inverse (e.symm j)
    change m (st.inverse.base+(e (e.symm j)).val)=_ at seen
    rw [e.apply_symm_apply] at seen
    exact seen
  have proved:=chart.posted rr m used name root chip self next actual count ranked space oldSpace
    (fun i=>(compact_host_fields B prev (e.symm i)).2) (fun _=>rfl)
  have occupied (f₀ : Fin used → Cell b) (v : B.next.V) :
      chart.onHost f₀ ((dense v).castLE next) = f₀ (e v) := by
    unfold Chart.onHost
    exact dite_eq_left (show ((dense v).castLE next).val < used from (dense v).isLt)
  refine ⟨chart.onHost chip,chart.onHost (fun i=>self (root i)),chart.runs rr m,?_,?_,?_,?_⟩
  · exact (proved 0).2
  · exact (proved 1).2
  · intro v g x
    constructor
    · refine (congrArg Fin.val (occupied chip v)).trans ?_
      change (raw (e.symm (e v))).val % (pal).card = _
      rw [e.symm_apply_apply]
      exact (compact_host_fields B prev v).1
    · refine (congrArg Fin.val (occupied (fun i => self (root i)) v)).trans ?_
      change (self (oldRank (position (Z).graph (e.symm (e v)).val))).val = _
      rw [e.symm_apply_apply]
      exact (selfRank _).trans (halo_old_rank B ((g,v),x) _).symm
  · intro h high
    have vacant (f₀ : Fin used → Cell b) : chart.onHost f₀ h = 0 := by
      unfold Chart.onHost
      exact dite_eq_right (Nat.not_lt.mpr high)
    exact ⟨vacant _,vacant _⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
