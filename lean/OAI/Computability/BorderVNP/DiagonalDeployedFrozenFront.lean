import OAI.Computability.BorderVNP.DiagonalFrozenSignedDeployment
import OAI.Computability.BorderVNP.DiagonalFrozenStartupOperands
import OAI.Computability.BorderVNP.PackedHistoryGeometryBranch

/-! # The actual deployed site as the chosen positive geometry reader -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Branch Cover Packing Packing.DeckGrid CellEntries ExternalSew ExternalSew.RowTrace
open VPVNP BurstRAM VerifierNetwork ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open TeamContraction TeamContraction.ProcessorSlots RoutingISA RoutingISA.Pins RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit TeamScales MvPolynomial
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins
open scoped Classical BigOperators

set_option maxRecDepth 6000
set_option maxHeartbeats 1200000

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {paid : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField paid aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r rw pinWidth pc a link ec axes d : ℕ}
    (reader : ChosenReader chart (R+1) r rw rw rw pinWidth) (physical : UniversalMachine.Program)
    (P : TeamOpcode.Program pc 64 32 8) (S : SiteData R r 64 32 rw a)
    (fit : fitsWith physical 64 32 r rw a R link (k+1) ec)
local notation "indexWidth" => (pairedTableParameters (k+1) s+2)*pinWidth
local notation "tail" => setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)

variable {gridOrder : Fin (GridHosts.tileCount axes d) ≃ (Fin axes → Deck (d+2))}
    (W : WiredWitness (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1)
        (k:=k) (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a))
        physical fit ((pairedTableParameters (k+1) s+2)*pinWidth)) (Fin.last k) D axes d gridOrder
        (0 : ParseTable.State (Fin (k+1) × Bool) s))
    (pos : (Fin axes → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {ns ne np : ℕ}
    (sites : (W.routedFine pos).Site ↪ Fin ns) (edges : (W.routedFine pos).Edge ↪ Fin ne)
    (ports : Fin r × Fin (publicWidth (tapeTemplate (R:=R) (r:=r) (link:=link) (regs:=64) (w:=rw) (e:=ec) (width:=rw+1)
      (k:=k) (a:=setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a)) physical fit
      ((pairedTableParameters (k+1) s+2)*pinWidth))) ↪ Fin np)
    (copies bundles headerFactor : ℕ)
    (L : Routing.WireLayout (R+1) r link) {reserve o field : ℕ}
    (t : Table (Fin reserve ⊕ Fin 0) o field) (task : SignedTaskArena.Layout) (exteriorBudget : ℕ)

local notation "tiles" => GridHosts.tileCount axes d
local notation "capacity" => seedBoxCapacity (k+1) r axes d (Fintype.card (Direction axes))
local notation "desc" => seedDescriptionWidth (k+1) r axes d (headerFactor*logWidth r (k+1)) (BottomGridBank.bodyBudget capacity)
local notation3 (prettyPrint := false) "A₀" => reader.startupArenaWith (n:=k+1) (reg:=64) physical a link L.header
local notation "dir" => freeDirectory R r (StartupArena.literal A₀) link tiles
  (GridHosts.inputBlockWidth r (k+1) axes d) (bundles*tiles) desc
local notation "gap" => 7*(Directory.Layout.candidates dir)
local notation "fresh" => StartupArena.next A₀+gap
local notation "origin" => Allocation.dest fresh reserve (Table.size t) o field
local notation "query" => Fintype.card (Board.Physical (pairedTableParameters (k+1) s) pinWidth rw (paid.Entry ⊕ ι))
local notation "guesses" => Fintype.card (Guess (Fin (pairedTableParameters (k+1) s)) reader.gridRank
  (Nat.clog 2 C.p+1) (Nat.clog 2 C.p))
local notation3 (prettyPrint := false) "ordinary" => SignedTaskArena.withOrdinary S (fun _ => task) A₀
  (fun _ => origin) (fun _ => 0) (fun _ => query) (fun _ => guesses) (fun _ => reader.gates)
local notation3 (prettyPrint := false) "routed" => routingExtension (signedBudgetWords rw exteriorBudget)
  dir origin task.cube.cables task.cube.cells
local notation3 (prettyPrint := false) "places" u => reader.frozenTaskPlacement task A₀ u routed
local notation3 (prettyPrint := false) "pinned" u => CubeHeaderInstall.pinFields (places u).extension
  (Allocation.stop fresh reserve (Table.size t) o field rw) task.cube.header.d (task.cube.n+1)
  (task.cube.h*task.cube.b) task.cube.header.blocks reserve
  (BorderVNP.Cube.Physical.declarationCap task.cube.n task.cube.header.d task.cube.header.blocks task.cube.b task.cube.h task.cube.s)
local notation "first" => freeStartWith physical r 32 64 rw (k+1)


local notation "off" => StartupArena.literal A₀/4
local notation "ell" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve (Table.size t) o field*rw) r
local notation3 (prettyPrint := false) "sitePlace" => fun u : Fin (R+1) => ReaderPlacement.inArena A₀
  (places u).valuation (places u).entry (places u).totals (Allocation.fields (pinned u) fresh reserve (Table.size t) o field off ell)
local notation3 (prettyPrint := false) "geo" => fun _ : Fin (R+1) => GeometryAdvice.serialized (GeometryAdvice.packet (w:=rw)
  fresh (Allocation.packed fresh reserve (Table.size t) o field rw) t (fun i => (A₀).broadcastBase+1+i.val))
local notation3 (prettyPrint := false) "strings" => W.seedLiteralMatrix pos (ParseTable.signedLiteralCode ord) sites edges ports
  copies bundles (headerFactor*logWidth r (k+1))
local notation3 (prettyPrint := false) "deployed" => reader.deployedFrozenSites physical P S fit W pos sites edges ports
  copies bundles headerFactor L t task exteriorBudget

/-- Use the installed table directly in the chosen profile geometry, including
its actual allocated reader placement, signed descriptions and exterior budget. -/
theorem ChosenReader.deployedFrozenSites_eq_startup :
    deployed = reader.startupSitesWith physical P ordinary sitePlace fit dir (signedBootStripe first)
      (Allocation.stripe fresh reserve (Table.size t) o field off ell) (fun _ => []) geo strings L.header := rfl

/-- The true deployed pin operands have exactly the sizes and broadcast pointer
in the charged startup. The returned packet and native route loop use the same
physical word width and literal count. -/
theorem ChosenReader.deployedFrozenSites_frontOperands (u : Fin (R+1)) :
    let G := wiringWith physical P deployed indexWidth link (k+1) ec fit
    let packet := reader.packetAt (sitePlace u)
    let slot := adviceOffsetWith physical r 32 64 rw (k+1)
    let args := (A₀).unitAddresses slot packet
    let op := reader.siteOperandsWith physical P ordinary sitePlace fit L.header u
    let f := G.transferFrame u args.header args.dst
    packet.bits.length=reader.packetBitCount ∧ rw≤packet.bits.length ∧ args.header=L.header ∧
      args.dst=(A₀).broadcastBase ∧ f.literal=(A₀).literal ∧ op.layout.count=f.processors*f.literal :=
  reader.frozenSignedData_frontOperands physical P ordinary fit W pos sites edges ports copies bundles headerFactor
    (fun v => (places v).valuation) (fun v => (places v).entry) (fun v => (places v).totals) (fun v => pinned v)
    L t (signedBootStripe first) (fun _ => []) gap u

open RoutingISA.Evaluator RoutingISA.CompactMachine CellMacro.Generator

/-- The witness for the particular profile returned by the actual deployed
site can be reused in its entire pin-indexed equivalence. This keeps the
subsequent placement and its public schedule at precisely that returned state. -/
theorem ChosenReader.deployedFrozenSites_profile_charge (u : Fin (R+1)) (pin : Fin indexWidth → Bool)
    (exterior : Exterior R r link → Bool) :
    let G := wiringWith physical P deployed indexWidth link (k+1) ec fit
    let packet := reader.packetAt (sitePlace u)
    let slot := adviceOffsetWith physical r 32 64 rw (k+1)
    let args := fun v => (A₀).unitAddresses slot (reader.packetAt (sitePlace v))
    let op := reader.siteOperandsWith physical P ordinary sitePlace fit L.header u
    let f := G.transferFrame u L.header (A₀).broadcastBase
    let F := G.processorFields u pin exterior (args u).ibase (args u).hbase (args u).starbase
    let init := processorMemory F rw
    let pub := (deployed).publicWords u
    let bank := (deployed).registers u
    let cost := jointBudget packet.bits.length rw+f.readTicks+2+
      ((pinSetup.slots+17*op.layout.count+1)+GeometryAdviceRate.ticks (Table.size t) reserve o field rw)
    ∀ (B : BootedPinStart SparseExterior.driver G (deployed).publicWords (deployed).registers args pin exterior u),
      let mac := install SparseExterior.driver (k+1) B.start.routines
      ∀ {dest : ℕ} {words : Fin o → ℕ} {resident : (Fin B.start.guessWidth → Bool) → Memory rw → Prop},
        ProfilePaths (withStartup pinGeometry) B.start.guessWidth pub mac bank init True cost dest words resident →
        ∀ (v : Fin B.start.guessWidth → Bool) (run : Returns (withStartup pinGeometry) pub mac bank init),
          run.val.1.flatMap TeamRAM.Event.choices=List.ofFn v →
          ∃ profile : (Fin B.start.guessWidth → Bool) ≃ Returns (withStartup pinGeometry) pub mac bank init,
            (∀ bits, (profile bits).val.1.flatMap TeamRAM.Event.choices=List.ofFn bits) ∧ profile v=run ∧
            traceCost run.val.1 ≤ jointBudget packet.bits.length rw+f.readTicks+2+
              (pinSetup.slots+17*(f.processors*f.literal)+1)+GeometryAdviceRate.ticks (Table.size t) reserve o field rw := by
  intro G packet slot args op f F init pub bank cost B mac dest words resident paths v run read
  obtain ⟨profile,actual⟩ := paths.outputs True.intro
  have given := (actual (profile.symm run)).1
  rw [Equiv.apply_symm_apply,read] at given
  have digit : profile.symm run=v := (List.ofFn_inj.mp given).symm
  have same : profile v=run := by rw [←digit,Equiv.apply_symm_apply]
  refine ⟨profile,fun g => (actual g).1,same,?_⟩
  have paid := (actual v).2.1
  rw [same] at paid
  have count : op.layout.count=f.processors*f.literal :=
    (reader.deployedFrozenSites_frontOperands physical P S fit W pos sites edges ports copies bundles headerFactor
      L t task exteriorBudget u).2.2.2.2.2
  dsimp only [cost] at paid
  rw [count] at paid
  simpa only [Nat.add_assoc] using paid


end Diagonal

end BorderVNP
end Computability
end OAI
