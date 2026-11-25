import OAI.Hierarchy.DescentResetPeerActorChart
import OAI.Hierarchy.DescentCompactRankPeers
import OAI.Hierarchy.DescentPhysicalOrder
import OAI.Hierarchy.DescentResetPeerUnionRAM

namespace OAI
/-! # The four physical rank ports in the actual reached reset placement -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentDenseHostOrder DescentCommonHost
open DescentGroupPeerOrder DescentPacking.PackedMatch.Local.Stage DescentColonies.DynamicSplit
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ} {input : Reached W G q ε S k i z D w hist}
  {ctl : ResetRates G S k D n h C f g cut tail} (B : ClosedReset input ctl)
set_option hygiene false
set_option quotPrecheck false
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "r" => (Z).k-(T).commonDepth
local notation "Ht" => GroupStage.depthBound D n f g
local notation "pal" => DescentDenseHostOrder.roster (Z).graph r Ht
local notation "used" => Fintype.card B.next.V
variable {H0 : ℕ} (previous : Fintype.card input.V≤H0)
local notation "hosts" => input.vertex.trans (Fin.castLEEmb previous)
local notation "adj" => hostRotor hosts (hostRoster A ((hosts).trans Fin.valEmbedding))
local notation "oldRank" => (vertex).trans (Fin.castLEEmb previous)
local notation "real" => (Z).rawHostRank T oldRank
local notation "dense" => (Z).denseHostRank T oldRank
local notation "rawSize" => H0*(pal).card


open DescentSortedRoster DescentResetPeerUnionRAM
def compactRankName : Fin used ↪ Fin rawSize:=(compactActorOrder B previous).symm.toEmbedding.trans real

private theorem compactRankName_apply (v : B.next.V) :
    compactRankName B previous (compactActorOrder B previous v) = real v := by
  change (real) ((compactActorOrder B previous).symm (compactActorOrder B previous v)) = _
  rw [Equiv.symm_apply_apply]

theorem compactRank_strict : StrictMono (compactRankName B previous):=by
  let number:=(real).trans Fin.valEmbedding
  have same (v : B.next.V) : (compactActorOrder B previous v).val=(DescentPhysicalOrder.physical number v).val:=by
    change ((Z).denseHostRank T oldRank v).val=_
    exact ((Z).denseHostRank_read T oldRank v).trans (DescentPhysicalOrder.physical_val number v).symm
  intro i j lt
  let a:=(compactActorOrder B previous).symm i
  let b:=(compactActorOrder B previous).symm j
  have indexed_ : (compactActorOrder B previous a).val<(compactActorOrder B previous b).val:=by simpa [a,b] using lt
  rw [same,same] at indexed_
  exact (DescentPhysicalOrder.physical_lt_iff number a b).mp indexed_

variable (found : Fin rawSize→Fin 3→Option (Fin rawSize))
  (four : ∀v:B.next.V,present (selfPeers found) (real v)=
      (insert v ((Z).emittedNear T v)).map real)

include four in
theorem compactRank_closed (u : Fin used) (y : Fin rawSize)
    (h : y∈present (selfPeers found) (compactRankName B previous u)):
    ∃z,compactRankName B previous z=y:=by
  let v:=(compactActorOrder B previous).symm u
  change y∈present (selfPeers found) (real v) at h
  rw [four v] at h
  obtain ⟨x,_,rfl⟩:=Finset.mem_map.mp h
  exact ⟨compactActorOrder B previous x,compactRankName_apply B previous x⟩

variable {H : ℕ} (size : used≤H)
local notation "view" => DescentSortedRoster.Compact.pull (compactRankName B previous) size (selfPeers found)
local notation "post" => (dense).trans (Fin.castLEEmb size)

theorem compactRank_order (x y : B.next.V) :
    post x<post y ↔ (Z).rawHostRank T vertex x<(Z).rawHostRank T vertex y:=by
  let ix:=compactActorOrder B previous
  have comp:=compactRank_strict B previous
  have a : compactRankName B previous (ix x)=real x:=by simp only [ix,compactRankName_apply]
  have b : compactRankName B previous (ix y)=real y:=by simp only [ix,compactRankName_apply]
  change ix x< ix y ↔ _
  have same : real x<real y ↔ (Z).rawHostRank T vertex x<(Z).rawHostRank T vertex y:=by rfl
  rw [←same,←a,←b]
  exact comp.lt_iff_lt.symm

include four in
/-- Padded compact rows have no physical ports. At a real receiver the set
is exactly the emitted four-slot neighborhood, with its compact names. -/
theorem compactRank_present (v : B.next.V) :
    present view (post v)=(insert v ((Z).emittedNear T v)).map post:=by
  classical
  let ix:=compactActorOrder B previous
  change present view ((ix v).castLE size)=_
  rw [DescentSortedRoster.Compact.current_set]
  ext x
  simp only [Finset.mem_map,Finset.mem_filter,Finset.mem_univ,true_and]
  have source : compactRankName B previous (ix v)=real v:=by simp only [ix,compactRankName_apply]
  rw [source,four]
  constructor
  · rintro ⟨z,atZ,hit⟩
    obtain ⟨t,atT,same⟩:=Finset.mem_map.mp atZ
    have physical : t=ix.symm z:=(real).injective same
    refine ⟨t,atT,?_⟩
    rw [physical]
    change (ix (ix.symm z)).castLE size=x
    simpa using hit
  · rintro ⟨t,atT,hit⟩
    exact ⟨ix t,Finset.mem_map.mpr ⟨t,atT,(compactRankName_apply B previous t).symm⟩,hit⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
