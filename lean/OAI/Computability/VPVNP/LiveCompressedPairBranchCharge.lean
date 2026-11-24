import OAI.Computability.VPVNP.LiveCompressedPairFiveCaps
import OAI.Computability.VPVNP.LiveCompressedPairVertexAssembly
import OAI.Computability.VPVNP.LiveCompressedPairPreludeCosts

/-! # Charging the descriptor and terminal reports of one physical pair path -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM Compression CursorNetwork CompressorRecords NetworkKernel PairSimulation LocalHistory
open PairStages.Group.CompressedPaths CompressorRecords.Schedule LiveStageLink
open private probes_le_length from OAI.Computability.VPVNP.LiveCompressedPairCursorStartup

variable {a g a' g' : ℕ}

variable {d initial phases : ℕ} {C : Catalog d} {b : Bootstrap} {plan : Online.Config C initial phases}
    {shape : DescriptorSpace.Shape} {limit : ℕ} {segments : VertexImage.Part → VertexImage.Segment}
    {G : PairStages.Group} {B n base : ℕ} {m : Memory G.w}

local notation "ports" => publicWords G
local notation "fuel₀" => fuel G
local notation "start" => cursorStartupLogs b ports B n base m initial phases d
local notation "entry" => after m (eventLog start)
local notation "table₀" => terminalBody shape limit segments

variable {Z : Type*} {R : Type*} [CommRing R] {L : Type} [Fintype L] {κ : L → R} {net : Z → Network}
    {arc : (z : Z) → ScanPhase (net z)} {sites : (z : Z) → SiteParsers κ (net z)}
    (descriptor : Z ≃ StagePaths b plan (terminalBody shape limit segments) (publicWords G) (fuel G) Stage.online
      (after m (eventLog (cursorStartupLogs b (publicWords G) B n base m initial phases d))))
    (branches : ∀ z, TerminalBranch (G := G) (B := B) (n := n) (base := base) (m := m)
      (b := b) (plan := plan) (shape := shape) (limit := limit) (segments := segments) descriptor (arc z) (sites z) z)

/-- The actual five-phase trace selected by a terminal wire and vertex assignment. -/
noncomputable abbrev TerminalBranchData.chosenTrace {w : ℕ} {workers : TerminalLink.Stage → PairTable}
    {pub : Fin 11 → Word w} {cap : ℕ} {mem : Memory w} {N : Network} {sc : ScanPhase N}
    {P : SiteParsers κ N} (s : TerminalBranchData workers pub cap mem sc P) (x : TerminalData sc P) :=
  s.setup.trace (s.bitPaths x.arcs) (s.vertexPaths x.arcs x.choices)

/-- The resource field consumed by the live group uses the actual reports of
its descriptor, wire assignment and terminal witnesses. The only dynamic
charges are the source calendar rows and the individual native vertex calls. -/
theorem branchReports_caps (z : Z) (x : TerminalData (arc z) (sites z))
    (X : State a g) (Y : State a' g') (chain : TermChain R X.network Y.network)
    (R₀ H steps T site q bootBound : ℕ) (hR : 128 ≤ R₀) (hH : 16 ≤ H) (clock : 136 ≤ fuel₀)
    (startup : StartupResult b plan table₀ ports B n base m fuel₀)
    (burst : ∀ i, sourceFuel b initial phases n i+5 ≤ H) (privateRoom : ∀ i, sourceFuel b initial phases n i+77 ≤ fuel₀)
    (online : List (Report G.w)) (source : ordinaryReports (descriptor z) = OnlineWorkspace.framed (ports 2) entry online)
    (onlineRow : ∀ r ∈ online, r.probes+11 ≤ H ∧ r.events.length+101 ≤ fuel₀)
    (onlineTotal : 64*RAMBuckets.cost Report.probes online ≤ R₀*H)
    (prelude : PreludeCosts X Y ports ((branches z).chosenTrace x) steps limit T bootBound)
    (bootCap : bootBound+9 ≤ H ∧ bootBound+107 ≤ fuel₀)
    (arenaCap : TraversalController.callFuel limit+9 ≤ H ∧ TraversalController.callFuel limit+107 ≤ fuel₀)
    (bitMemory last : Memory G.w) (bits : Fin Y.totalWidth → Bool)
    (bitRows : ((branches z).chosenTrace x).sharedBits.logs.map Prod.snd = FinalBits.Worker.reports ports 0 bitMemory bits)
    (vertex : Y.network.Site → Report G.w)
    (vertexRows : ((branches z).chosenTrace x).vertices.logs.map Prod.snd = (List.ofFn fun i => vertex ((siteOrder Y).entries i)) ++
      [VertexImage.closingReport ports last])
    (hq : 1 ≤ q) (hT : T ≤ n.log2+1)
    (siteRow : ∀ v, 1+(vertex v).probes ≤ siteAccesses Y chain site q n v ∧ (vertex v).events.length+107 ≤ fuel₀)
    (allSites : ∀ v, siteAccesses Y chain site q n v+9 ≤ H)
    (share : 320*branchAccesses X Y chain (terminalCoefficient (2^a') steps limit bootBound 1 site) q n ≤ R₀*H) :
    let rs := start ++ (onlineReports (descriptor z) ++
      (TerminalLink.reports (TerminalLink.header ports) ((branches z).chosenTrace x).logs).map (report ports Stage.terminal))
    (∀ r ∈ rs, r.events.length+4 ≤ fuel₀) ∧ 4*RAMBuckets.cost Report.probes rs ≤ R₀*H ∧
      ∀ r ∈ rs, 3+r.probes ≤ H := by
  intro rs
  have bootProbes := (probes_le_length prelude.boot.events).trans prelude.bootWork
  have closeProbes : (VertexImage.closingReport ports last).probes = 1 := rfl
  have closeWork : (VertexImage.closingReport ports last).events.length = 14 := rfl
  have clocked := five_execution_caps X Y chain ports b B n base m initial phases d (ports 2) entry online
    ((branches z).chosenTrace x) R₀ H fuel₀ hR hH clock startup.sourceCost burst privateRoom onlineRow onlineTotal
    prelude.boot (VertexImage.closingReport ports last) bootBound 1 prelude.initialRow
    ⟨bootProbes, (Nat.add_le_add_right bootProbes _).trans bootCap.1,
      (Nat.add_le_add_right prelude.bootWork _).trans bootCap.2⟩
    ⟨closeProbes.le, by omega, by omega⟩ prelude.scan steps limit T prelude.arenaTotal
    (fun r hr => by obtain ⟨p,t⟩ := prelude.arenaRow r hr; omega)
    bitMemory bits bitRows vertex vertexRows site q hq hT siteRow allSites share
  dsimp only [rs,onlineReports]
  rw [source]
  exact clocked

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
