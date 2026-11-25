import OAI.Hierarchy.DescentDatedTicketMaterialAnchor
import OAI.Hierarchy.DescentDatedTicketSocketCore

namespace OAI
/-! # Original matching and sibling rows for the selected cable operand -/
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
local notation "matchShape" => shape (2^k) A.degree (2*A.cap) profile
local notation "fieldsAt" => Gather.flat (Gather.descriptorInputs (K:=2^(k+1)) matchShape A.cap real)
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
local notation:max "member" base:max e:max side:max => (⟨(picked A he base e side).val,
  A.quantum_positive _ (picked A he base e side).property.1⟩ : positive)
local notation:max "source_" q:max => (N).src (q).val
local notation:max "slot_" q:max => A.block (source_ q)
variable (outBits : ℕ)
local notation:max "ordinaryPage" q:max side:max f:max => DescentDatedOperandPages.law fmt profile outBits
  (DescentDatedOperandPages.anchor fmt (slot_ q) (out q) side f).val (DepotRAM.combine fmt (previous (source_ q)))


/-- The four possible original matcher reads. The indices contain the genuine
selected pair when an old operand is redirected or a newborn uses its second source. -/
inductive CablePort : positive → Fin 3 → positive → Fin 11 → Prop where
  | source (q : positive) : CablePort q 0 q 0
  | kept (q : positive)
      (miss : ∀(m : Matched T A.cap (thinList home color (home (source_ q)))
        (thickList home color (home (source_ q)))) (s : Bool),
        (picked A he (home (source_ q)) m s).val ≠ q.val) : CablePort q 1 q 0
  | redirected (c : ScanColonies he A.stage) (m : Matched T A.cap (thinList home color c) (thickList home color c))
      (s : Bool) : CablePort (member c m s) 1 (member c m true) (if s then 1 else 2)
  | sibling (c : ScanColonies he A.stage) (m : Matched T A.cap (thinList home color c) (thickList home color c)) :
      CablePort (member c m true) 2 (member c m false) 0

/-- Every retained input or output port has a unique original case distinction
between the unredirected wire and one of the two selected sides. -/
theorem CablePort.of_previous (q : positive) (target : Bool) :
    ∃ q' role,CablePort A he q (if target then 1 else 0) q' role :=by
  classical
  cases target with
  | false => exact ⟨q,0,.source q⟩
  | true =>
    let c:=home (source_ q)
    by_cases found : ∃(m : Matched T A.cap (thinList home color c) (thickList home color c)) (s : Bool),
        (picked A he c m s).val=q.val
    · obtain ⟨m,s,hit⟩:=found
      have eqn : (member c m s)=q:=Subtype.ext hit
      exact ⟨_,_,eqn ▸ CablePort.redirected c m s⟩
    · exact ⟨q,0,.kept q (fun m s hit=>found ⟨m,s,hit⟩)⟩

/-- In a redirected operand both selected sources lie at the same old host and group.
The block and outgoing ordinal can change at that host. -/
theorem CablePort.same_position {q q' : positive} {mode : Fin 3} {role : Fin 11}
    (C : CablePort A he q mode q' role) : A.pos (source_ q)=A.pos (source_ q') :=by
  cases C with
  | source | kept => rfl
  | redirected c m s =>
    calc
      _=(addr c).1:=by rw [← source_host A he (source_ (member c m s)),(picked A he c m s).property.2.1]
      _=_:=by rw [← source_host A he (source_ (member c m true)),(picked A he c m true).property.2.1]
  | sibling c m =>
    calc
      _=(addr c).1:=by rw [← source_host A he (source_ (member c m true)),(picked A he c m true).property.2.1]
      _=_:=by rw [← source_host A he (source_ (member c m false)),(picked A he c m false).property.2.1]

include coord named fit winner df edgeOrder room stored in
theorem CablePort.page {q q' : positive} {mode : Fin 3} {role : Fin 11}
    (C : CablePort A he q mode q' role) (f : Fin 5) :
    let i:=if live : mode.val<2 then DescentDatedOperandPages.anchor fmt (slot_ q) (out q) ⟨mode.val,live⟩ f
      else DescentDatedOperandPages.sibling fmt (slot_ q) (out q) f
    DescentDatedOperandPages.law fmt profile outBits i.val (DepotRAM.combine fmt (previous (source_ q)))=
      (anchorColumns A.cap (handle q',role.val) f:Cell outBits) :=by
  cases C with
  | source q =>
    exact native_source_page A native S ready groups hosts win he hm profile dest m hub lay bytes
      fit winner b log room stored outBits q f
  | kept q miss =>
    exact native_target_old_page A native S ready groups hosts win he hm profile dest m hub lay bytes
      coord named fit winner df edgeOrder b log room stored outBits q miss f
  | redirected c pair s =>
    cases s <;> exact native_target_pair_page A native S ready groups hosts win he hm profile dest m hub lay bytes
      coord named fit winner df edgeOrder b log room stored c outBits pair _ f
  | sibling c pair =>
    exact native_birth_sibling_page A native S ready groups hosts win he hm profile dest m hub lay bytes
      coord named fit winner df edgeOrder b log room stored c outBits pair f

private theorem page_for_terrain (layout : DepotRAM.Shape) (profile_ width : ℕ)
    (x : Fin layout.blocks) (old : Fin layout.cap) (mode : Fin 3) (j : Fin 5)
    (v u : DepotRAM.Parts layout) (eq_ : v.terrain=u.terrain) :
    let index := if live : mode.val<2 then DescentDatedOperandPages.anchor layout x old ⟨mode.val,live⟩ j
      else DescentDatedOperandPages.sibling layout x old j
    DescentDatedOperandPages.law layout profile_ width index.val (DepotRAM.combine layout v) =
      DescentDatedOperandPages.law layout profile_ width index.val (DepotRAM.combine layout u) := by
  have same : TerrainAnchor.records layout profile_ x v=TerrainAnchor.records layout profile_ x u := by
    simp only [TerrainAnchor.records,eq_]
  dsimp only
  split
  · simp only [DescentDatedOperandPages.anchor_value, TerrainAnchor.field, DepotRAM.separate_combine, same]
  · simp only [DescentDatedOperandPages.sibling_value, TerrainAnchor.siblingField, DepotRAM.separate_combine, same]

include coord named fit winner df edgeOrder room stored in
/-- The matcher and sibling rows only read the terrain word; changing external
halo ranks and reverse paths leaves every selected catalogue field unchanged. -/
theorem CablePort.page_at {q q' : positive} {mode : Fin 3} {role : Fin 11}
    (C : CablePort A he q mode q' role) (v : DepotRAM.Parts fmt)
    (terrainEq : v.terrain=(previous (source_ q)).terrain) (f : Fin 5) :
    let i:=if live : mode.val<2 then DescentDatedOperandPages.anchor fmt (slot_ q) (out q) ⟨mode.val,live⟩ f
      else DescentDatedOperandPages.sibling fmt (slot_ q) (out q) f
    DescentDatedOperandPages.law fmt profile outBits i.val (DepotRAM.combine fmt v)=
      (anchorColumns A.cap (handle q',role.val) f:Cell outBits) :=by
  exact (page_for_terrain fmt profile outBits (slot_ q) (out q) mode f
    v (previous (source_ q)) terrainEq).trans
    (CablePort.page A native S ready groups hosts win he hm profile dest m hub lay bytes
      coord named fit winner df edgeOrder b log room stored outBits C f)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
