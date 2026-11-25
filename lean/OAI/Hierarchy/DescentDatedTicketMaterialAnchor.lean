import OAI.Hierarchy.DescentDatedTerrainAnchorRead
import OAI.Hierarchy.DescentDatedOperandPages

namespace OAI
/-! # The physical matcher page for untreated, redirected and newborn sockets -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentSixParty DescentStageEdgeReceipt DescentRawCablePanel DescentSharedCableNames
open DescentHostDirectory DescentCableDonorNames DescentHaloWalkRAM ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1400000
set_option quotPrecheck false
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a H Z w M : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (groups : J≃Fin Z) (hosts : V↪Fin H) (win : J×V→Fin (2^k)→Cell a)
    (he : 0≤ε) (hm : 0<M) (profile dest : ℕ) (m : Memory w) (hub : V→Bool) (lay : Bool) (bytes : ℕ)
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

open DescentPacking DescentSixParty.StarKeys
local notation "N" => W.graph
local notation "out" => DescentSharedCableNames.Stage.outgoing A native S ready
local notation "handle" => donorAddress A native S ready
local notation "positive" => DescentSharedCableNames.Stage.Positive A
local notation "T" => nativeTraffic N W.core home
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding)))
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (b : ℕ) (log : Memory w) (room : (shape (2^k) A.degree (2*A.cap) profile).outputBits*M≤w)
    (stored : ∀i,log (b+i.val)=((topologyWords (M:=M) (shape (2^k) A.degree (2*A.cap) profile) (Gather.flat (Gather.descriptorInputs (K:=2^(k+1)) (shape (2^k) A.degree (2*A.cap) profile) A.cap (spread groups.toEmbedding hosts (terrain (short:=short) A native S ready (cableNames k (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding))) win (rotor A (groupRank (groups.toEmbedding.trans Fin.valEmbedding) (hosts.trans Fin.valEmbedding))))))) i).val:Word w))
local notation:max "previous" u:max => scene (hosts (A.pos u).2) (groups (A.pos u).1)
variable (c : ScanColonies he A.stage)
local notation "Pair" => Matched T A.cap (thinList home color c) (thickList home color c)
local notation:max "member" e:max side:max => (⟨(picked A he c e side).val,
  A.quantum_positive _ (picked A he c e side).property.1⟩ : positive)
local notation:max "source_" q:max => (N).src (q).val
local notation:max "slot_" q:max => A.block (source_ q)
variable (outBits : ℕ)
local notation:max "ordinaryPage" q:max side:max f:max => DescentDatedOperandPages.law fmt profile outBits
  (DescentDatedOperandPages.anchor fmt (slot_ q) (out q) side f).val (DepotRAM.combine fmt (previous (source_ q)))

include fit winner room stored in
theorem native_source_page (q : positive) (f : Fin 5) :
    ordinaryPage q 0 f=(anchorColumns A.cap (handle q,0) f:Cell outBits) := by
  refine (DescentDatedOperandPages.anchor_value fmt profile outBits (slot_ q) (out q) 0 f (previous (source_ q))).trans ?_
  exact native_terrain_field A native S ready groups hosts win he hm profile dest m hub lay bytes
    (source_ q) b log fit winner room stored (out q) false outBits f

include coord named fit winner df edgeOrder room stored in
theorem native_target_pair_page (e : Pair) (side : Bool) (f : Fin 5) :
    ordinaryPage (member e side) 1 f=
      (anchorColumns A.cap (handle (member e true),if side then (1:ℕ) else 2) f:Cell outBits) := by
  let q:positive:=member e side
  have home_ : home (source_ q)=c:=(picked A he c e side).property.2.1
  have ret:=retarget_matched A native S ready rank win he groups.toEmbedding hosts hm coord named fit winner df edgeOrder
    profile b log room stored c side e
  simp only [source_handle_eq A native S ready rank he] at ret
  refine (DescentDatedOperandPages.anchor_value fmt profile outBits (slot_ q) (out q) 1 f (previous (source_ q))).trans ?_
  change TerrainAnchor.field fmt profile outBits (slot_ q) f (DepotRAM.combine fmt (previous (source_ q)))
    (TerrainAnchor.ticket fmt (out q) true)=_
  rw [native_terrain_field A native S ready groups hosts win he hm profile dest m hub lay bytes (source_ q)
    b log fit winner room stored (out q) true outBits f,home_]
  exact congrArg (fun a=>(anchorColumns A.cap a f:Cell outBits)) ret

include coord named fit winner df edgeOrder room stored in
theorem native_target_old_page (q : positive)
    (miss : ∀ (u : Matched T A.cap (thinList home color (home (source_ q)))
      (thickList home color (home (source_ q)))) (side : Bool),
      (picked A he (home (source_ q)) u side).val≠q.val) (f : Fin 5) :
    ordinaryPage q 1 f=(anchorColumns A.cap (handle q,0) f:Cell outBits) := by
  have ret:=retarget_unreplaced A native S ready rank win he groups.toEmbedding hosts hm coord named fit winner df edgeOrder
    profile b log room stored (home (source_ q)) q (source_host A he (source_ q)) miss
  refine (DescentDatedOperandPages.anchor_value fmt profile outBits (slot_ q) (out q) 1 f (previous (source_ q))).trans ?_
  change TerrainAnchor.field fmt profile outBits (slot_ q) f (DepotRAM.combine fmt (previous (source_ q)))
    (TerrainAnchor.ticket fmt (out q) true)=_
  rw [native_terrain_field A native S ready groups hosts win he hm profile dest m hub lay bytes (source_ q)
    b log fit winner room stored (out q) true outBits f]
  exact congrArg (fun a=>(anchorColumns A.cap a f:Cell outBits)) ret

include coord named fit winner df edgeOrder room stored in
/-- The third matcher page uses the real first member as the lookup key and
returns the second member's old block and outgoing seat. -/
theorem native_birth_sibling_page (e : Pair) (f : Fin 5) :
    let q : positive:=member e true
    DescentDatedOperandPages.law fmt profile outBits (DescentDatedOperandPages.sibling fmt (slot_ q) (out q) f).val
      (DepotRAM.combine fmt (previous (source_ q)))=(anchorColumns A.cap (handle (member e false),0) f:Cell outBits) := by
  intro q
  have home_ : home (source_ q)=c:=(picked A he c e true).property.2.1
  have recorded:=native_terrain_records A native S ready groups hosts win he hm profile dest m hub lay bytes (source_ q)
    b log fit winner room stored
  rw [home_] at recorded
  have found:=selected_sibling A native S ready rank win he groups.toEmbedding hosts hm coord named fit winner df edgeOrder
    profile b log room stored c e
  simp only [source_handle_eq A native S ready rank he] at found
  refine (DescentDatedOperandPages.sibling_value fmt profile outBits (slot_ q) (out q) f (previous (source_ q))).trans ?_
  apply TerrainAnchor.sibling_read
  rw [recorded]
  exact found


end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
