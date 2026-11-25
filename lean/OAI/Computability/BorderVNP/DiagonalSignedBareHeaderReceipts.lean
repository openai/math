import OAI.Computability.BorderVNP.DiagonalDeployedSharedHeaderBoot
import OAI.Computability.BorderVNP.CubeScatterTransmissionRecovery

/-! # The actual header-copy subtraces of the deployed signed reader -/

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


open RoutingISA.Evaluator JointHeader BorderVNP.Cube RoutingISA.CompactMachine

local notation3 (prettyPrint := false) "actual" => reader.deployedFrozenSites physical P S fit W pos sites edges ports copies bundles
  headerFactor L t task exteriorBudget
local notation3 (prettyPrint := false) "sewn" => SewnTape.wiring (regs:=64) (w:=rw) (ec:=ec) (width:=rw+1) physical fit
  ((actual).enrichedFree physical P (k+1) ec link) indexWidth
local notation3 (prettyPrint := false) "adOff" => adviceOffsetWith physical r 32 64 rw (k+1)
local notation3 (prettyPrint := false) "rawBase" => SignedTaskArena.rawAddress A₀ task.cube.header.profile task.cube.n
  task.cube.header.d task.cube.header.cap
local notation3 (prettyPrint := false) "off" => (A₀).literal/4
local notation3 (prettyPrint := false) "ell" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve (Table.size t) o field*rw) r
local notation3 (prettyPrint := false) "st" => Allocation.stripe fresh reserve (Table.size t) o field off ell
local notation3 (prettyPrint := false) "installed" u => Allocation.fields (pinned u) fresh reserve (Table.size t) o field off ell
local notation3 (prettyPrint := false) "loc" u => ReaderPlacement.inArena A₀ (places u).valuation (places u).entry (places u).totals (installed u)
local notation3 (prettyPrint := false) "pk" u => reader.packetAt (loc u)
local notation3 (prettyPrint := false) "args" => fun u : Fin (R+1) => (A₀).unitAddresses adOff (pk u)
local notation3 (prettyPrint := false) "geomBits" => GeometryAdvice.serialized (GeometryAdvice.packet (w:=rw) fresh
  (Allocation.packed fresh reserve (Table.size t) o field rw) t (fun i => (A₀).broadcastBase+1+Fin.val i))
local notation3 (prettyPrint := false) "strings" => W.seedLiteralMatrix pos (ParseTable.signedLiteralCode ord) sites edges ports
  copies bundles (headerFactor*logWidth r (k+1))
local notation3 (prettyPrint := false) "frame" u => (sewn).transferFrame u L.header (A₀).broadcastBase
local notation3 (prettyPrint := false) "full" u => signedProfileExtension task (signedBudgetWords rw exteriorBudget) dir origin
  task.cube.cables task.cube.cells rawBase (Fin.val u) rw fresh reserve (Table.size t) o field off ell

set_option maxRecDepth 12000 in
set_option maxHeartbeats 4500000 in
/-- On every exterior with this copied header, split the real boot of each team at
the native read instruction. The startup frame, copied words and event lists all
belong to the same execution, before any routing or private calls. -/
theorem ChosenReader.deployed_header_receipts (fixed : Routing.Block (R+1))
    (regions : JointRoom dir first a (signedBootStripe first) st) (copiesFit : reader.packetBitCount≤r)
    (memFit : (A₀).next<2^rw) (hw : 0<rw) (three : 2<R+1) (hdr : 0<L.header) (cap : L.header≤r*link)
    (clock : ∀ u, packetUnitBudget ((args) u).advice.count rw (frame u)
      ((sewn).pinLayout u ((args) u).ibase ((args) u).hbase ((args) u).starbase)≤S.limit.val)
    (headerWidth : L.header = JointHeader.PositiveFields.width reserve task.cube.n task.cube.header.d
      task.cube.header.cap (R+1) task.dim rw)
    (pin : Fin indexWidth → Bool)
    (p : JointHeader.PositiveFields reserve task.cube.n task.cube.header.d task.cube.header.cap (R+1) task.dim rw)
    (wire : HeaderExterior L p.bits) :
    let chosen := reader.deployedFrozenSites_boots physical P S fit W pos sites edges ports copies bundles headerFactor
      L t task exteriorBudget fixed regions copiesFit memFit hw three hdr cap clock
    ∃ (positive : PositiveExterior sewn args pin rw wire.val) (h : ReturnedHeaders sewn pin wire.val L rw),
      h.ibase=(fun u => ((args) u).ibase) ∧ h.hbase=(fun u => ((args) u).hbase) ∧
      h.starbase=(fun u => ((args) u).starbase) ∧ h.dest=(fun u => ((args) u).dst) ∧
      ∀ u, let b := chosen.2.choose pin ⟨wire.val,positive⟩ u
        ∃ before : List (TeamRAM.Event rw), Runs ((actual).publicWords u)
          (TeamSiteEvents.macros (w:=rw) (siteLibrary SparseExterior.driver) (nativeClock (k+1))) unitStartup
          ((actual).registers u) (processorMemory ((sewn).processorFields u pin wire.val ((args) u).ibase
            ((args) u).hbase ((args) u).starbase) rw) before (h.regs u) (h.input u) ∧
          b.trace = before++(h.returned u).val.1 ∧
          (h.returned u).val.2=(b.out,b.memory) ∧ FlatAt (h.returned u).val.2.2 ((args) u).dst p.bits := by
  classical
  intro chosen
  obtain ⟨positive,truth⟩ := reader.deployed_header_boot physical P S fit W pos sites edges ports copies bundles headerFactor
    L t task exteriorBudget fixed regions copiesFit memFit hw three hdr cap clock headerWidth pin p wire
  let b := fun u => chosen.2.choose pin ⟨wire.val,positive⟩ u
  let mac := TeamSiteEvents.macros (w:=rw) (siteLibrary SparseExterior.driver) (nativeClock (k+1))
  have lane (u : Fin (R+1)) :
      ∃ (z : Bank rw) (m : Memory rw) (ret : Returns readBroadcast ((actual).publicWords u) mac z m),
        ((sewn).processorFields u pin wire.val ((args) u).ibase ((args) u).hbase ((args) u).starbase).ContainsInput m ∧
        (frame u).At (readings ((actual).publicWords u)) (readings m) ∧
        (∃ before : List (TeamRAM.Event rw), Runs ((actual).publicWords u) mac unitStartup ((actual).registers u)
          (processorMemory ((sewn).processorFields u pin wire.val ((args) u).ibase ((args) u).hbase
            ((args) u).starbase) rw) before z m ∧ (b u).trace=before++ret.val.1) ∧ ret.val.2=((b u).out,(b u).memory) := by
    obtain ⟨z,m,front,readEvents,chron,boot,copy⟩ := Runs.seq_iff.mp (b u).boot
    have fitted := (chosen.1 u).1
    obtain ⟨_,z',m',run,_,_,input,fields,_⟩ := jointPacket_run_coreWith physical P actual (fun u => pk u) link (k+1) ec
      fit u pin wire.val ((args) u).ibase ((args) u).hbase ((args) u).starbase ((actual).publicWords u) mac
      ((actual).registers u) (frame u) ((args) u).advice fitted.operands fitted.physical fitted.gather fitted.extended
      fitted.literalOffset fitted.packet fitted.reference
    obtain ⟨_,_,same⟩ := boot.unique_of_deterministic (by decide) run
    exact ⟨z,m,⟨(readEvents,(b u).out,(b u).memory),copy⟩,same.symm ▸ input,same.symm ▸ fields.broadcast,⟨front,boot,chron⟩,rfl⟩
  choose reg mem ret good resident front done using lane
  let h : ReturnedHeaders sewn pin wire.val L rw := ⟨(fun u => ((args) u).ibase),(fun u => ((args) u).hbase),
    (fun u => ((args) u).starbase),(fun u => ((args) u).dst),(actual).publicWords,(fun _ => mac),reg,mem,good,resident,
    (fun u => (chosen.1 u).1.physical),ret⟩
  refine ⟨positive,h,rfl,rfl,rfl,rfl,fun u => ?_⟩
  obtain ⟨ev,startup,time⟩ := front u
  refine ⟨ev,startup,time,done u,?_⟩
  change FlatAt (ret u).val.2.2 _ _
  rw [done u]
  exact (truth u).2.1.header

/-- The actual frozen operands put both pin arrays below the first cube header,
and the free directory uses the same literal and team dimensions as the sewn wiring. -/
theorem ChosenReader.deployed_route_bounds (room : (A₀).next+7*(dir).candidates≤task.cube.header.header) :
    (∀ u : Fin (R+1), (A₀).frame+13 < ((args) u).ibase ∧
      ((args) u).ibase+((sewn).pinLayout u ((args) u).ibase ((args) u).hbase ((args) u).starbase).count ≤
        task.cube.header.header) ∧
    (dir).processors=r ∧ (dir).literal=(sewn).program.length+(cutWidth (k+1)+
      (setupWidth (rw+1) (k+1)+(prefixCapacity r 32 64 rw (k+1)+1+a))) ∧ (dir).teams=R+1 := by
  refine ⟨?_,rfl,rfl,rfl⟩
  intro u
  change (A₀).frame+13<(A₀).ibase ∧ (A₀).ibase+(A₀).count≤task.cube.header.header
  have before : (A₀).ibase+(A₀).count≤(A₀).next := by
    unfold StartupArena.next StartupArena.hbase
    omega
  refine ⟨?_,by omega⟩
  unfold StartupArena.ibase StartupArena.broadcastBase StartupArena.dense
  omega

end Diagonal

end BorderVNP
end Computability
end OAI
