import OAI.Hierarchy.DescentDatedTerrainAnchor
import OAI.Hierarchy.DescentDatedSelectedAnchor
import OAI.Hierarchy.DescentDonorNativeParts

namespace OAI
/-! # The source terrain lookup and the original issued matcher agree at every physical field -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentSixParty DescentStageEdgeReceipt DescentRawCablePanel DescentSharedCableNames
open DescentHostDirectory DescentCableDonorNames DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H Z w M : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (groups : J≃Fin Z) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
    (he : 0≤ε) (hm : 0<M) (profile dest : ℕ) (m : Memory w) (hub : V→Bool) (lay : Bool) (bytes slots : ℕ)
local notation "rank" => groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "near" => hostRotor hosts (DescentGroupPeerOrder.hostRoster A (hosts.trans Fin.valEmbedding))
local notation "fmt" => shapeOf (short:=short) A bytes
local notation "scene" => nativeParts (short:=short) A native S ready rank win groups hosts hm profile dest m near hub lay bytes
local notation "terrain₀" => terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank)
local notation "real" => spread groups.toEmbedding hosts terrain₀
local notation "s" => shape (2^k) A.degree (2*A.cap) profile
local notation "fieldsAt" => Gather.flat (Gather.descriptorInputs (K:=2^(k+1)) s A.cap real)
local notation "seat" => slot he A groups.toEmbedding hosts hm
open DescentOperandPriorIncidence

theorem native_terrain_records (u : W.graph.Site) (b : ℕ) (log : Memory w)
    (fit : ∀v,(win (A.pos v) (A.block v)).val<2^short)
    (winner : ∀v,(win (A.pos v) (A.block v)).val=1+2*heap (addr (home v)).2+(color v).toNat)
    (lim : (s).outputBits*M≤w) (stored : ∀i,log (b+i.val)=((topologyWords (M:=M) s fieldsAt i).val:Word w)) :
    TerrainAnchor.records fmt profile (A.block u) (scene (hosts (A.pos u).2) (groups (A.pos u).1))=
      donorWord s log b (seat (home u)) := by
  have terrainAt :
      (scene (hosts (A.pos u).2) (groups (A.pos u).1)).terrain=Owners.register lay (terrain₀ (A.pos u)) := by
    change Owners.register lay (real (hosts (A.pos u).2) (groups (A.pos u).1))=_
    exact congrArg (Owners.register lay) (spread_hit groups.toEmbedding hosts terrain₀ (A.pos u))
  have cut:=winner_leaf A native S ready (cableNames k rank) win (rotor A rank) he fit winner u
  have atSite := source_host A he u
  funext j f
  rw [observed_field A native S ready rank win he groups.toEmbedding hosts hm profile b log lim stored (home u) j f]
  dsimp only [TerrainAnchor.records, shapeOf]
  rw [terrainAt]
  rw [ParentIncidence.split_register lay (terrain₀ (A.pos u))]
  dsimp only
  rw [cut, atSite]

theorem native_terrain_field (u : W.graph.Site) (b : ℕ) (log : Memory w)
    (fit : ∀v,(win (A.pos v) (A.block v)).val<2^short)
    (winner : ∀v,(win (A.pos v) (A.block v)).val=1+2*heap (addr (home v)).2+(color v).toNat)
    (lim : (s).outputBits*M≤w) (stored : ∀i,log (b+i.val)=((topologyWords (M:=M) s fieldsAt i).val:Word w))
    (old : Fin A.cap) (target : Bool) (outBits : ℕ) (i : Fin 5) :
    let previous:=scene (hosts (A.pos u).2) (groups (A.pos u).1)
    TerrainAnchor.field fmt profile outBits (A.block u) i (DepotRAM.combine fmt previous) (TerrainAnchor.ticket fmt old target)=
      (anchorColumns A.cap (retarget (donorWord s log b (seat (home u))) target ((A.block u).val*(2*A.cap)+old.val)) i:Cell outBits) := by
  dsimp only
  refine (TerrainAnchor.field_read fmt profile outBits (A.block u) i
    (scene (hosts (A.pos u).2) (groups (A.pos u).1)) old target).trans ?_
  rw [native_terrain_records A native S ready groups hosts win he hm profile dest m hub lay bytes u b log fit winner lim stored]
  rfl

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
