import OAI.Computability.BorderVNP.DiagonalDeployedFrozenBoots
import OAI.Computability.BorderVNP.DiagonalDeployedLeadClock
import OAI.Computability.BorderVNP.DiagonalJointPhysicalPost
import OAI.Computability.BorderVNP.DiagonalSupportedPrefixDomain

/-! # The original supported native team clocks on the deployed signed site -/

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


open RoutingISA.Evaluator.ScheduleClock RoutingISA.SignedTaskArena CellMacro.Generator

/-- Every actual supported boot runs with the same length-only phase budget.
The local observations concern arbitrary pre-call prefixes and native finish
returns, before checking their signed reports. The lead reader is charged
from the actual installed chosen packet, and every nonlead reads its retained
team word and exits. -/
theorem ChosenReader.deployedFrozenSites_joint_clock (fixed : Routing.Block (R+1))
    (regions : JointRoom dir first a (signedBootStripe first) st) (copiesFit : reader.packetBitCount≤r)
    (memFit : (A₀).next<2^rw) (hw : 0<rw) (three : 2<R+1) (hdr : 0<L.header) (cap : L.header≤r*link)
    (clock : ∀ u, packetUnitBudget ((args) u).advice.count rw (frame u)
      ((sewn).pinLayout u ((args) u).ibase ((args) u).hbase ((args) u).starbase)≤S.limit.val)
    (param : task.p.parameters=pairedTableParameters (k+1) s)
    (gadgets : Fintype.card (paid.Entry ⊕ ι)=task.p.report.gadgets) (teams : task.cube.teams=R+1)
    (teamFit : R+1<2^rw) (position : (A₀).next≤task.cube.header.header)
    (endRoom : task.endAddress rw query guesses reader.gates < 2^rw)
    (rectangle : 512*((R+1)+1)*(pairedTableParameters (k+1) s+Fintype.card (paid.Entry ⊕ ι)+1)*(rw+1)+
      (7+reader.charge) ≤ r)
    (global localRoom routeK fixedTicks emitted visits : ℕ) :
    let chosen := reader.deployedFrozenSites_boots physical P S fit W pos sites edges ports copies bundles headerFactor L
      t task exteriorBudget fixed regions copiesFit memFit hw three hdr cap clock
    let cost := uniformWindows r (R+1) exteriorBudget global localRoom routeK fixedTicks emitted visits
    ∀ (pin : Fin indexWidth → Bool)
        (x : {z // PositiveExterior sewn args pin rw z ∧
          PinStart.preCallSupport (fun y u => (chosen.2.choose pin y u).start) task.id z}),
      let B := chosen.2.choose pin ⟨x.val,x.property.1⟩
      let U := fun u => (B u).start
      (∀ (a : PinStart.JointPrefix task.id U) u, let v := PinStart.visits task.id U (a u)
        (B u).used+traceCost ((B u).pins (a u).1).val.1+traceCost v.profile.val.1+traceCost v.routing.val.1 ≤
          cost.core+cost.before) →
      (∀ (a : PinStart.JointPrefix task.id U) u, let input := PinStart.afterRoute task.id U (a u)
        traceCost input.val.1+privateDirectoryTicks ((actual).publicWords u) input.val.2.2 ≤ cost.argumentsCalls) →
      (∀ (a : PinStart.JointPrefix task.id U) u, let p := a u
        let mac := install SparseExterior.driver (k+1) (U u).routines
        ReaderKept A₀ (6+3*reader.gates+query) indexWidth (B u).memory ((B u).pins p.1).val.2.2 p.2.val.2.2 ∧
        ∀ call : Returns callOwnedCells ((actual).publicWords u) mac p.2.val.2.1 p.2.val.2.2,
          ∀ z : Returns (finishExpansion signedOccurrences) ((actual).publicWords u) mac call.val.2.1 call.val.2.2,
            Nonempty (PinStart.PhysicalPost (teams:=R+1) (d:=pairedTableParameters (k+1) s+Fintype.card (paid.Entry ⊕ ι))
              (width:=rw) u task global localRoom emitted visits ((actual).publicWords u) mac call.val.2.1 call.val.2.2 z)) →
      PinStart.JointClock task.id U (fun u => (B u).used) cost := by
  intro chosen cost pin x B U early arguments post
  have base (u : Fin (R+1)) : ((actual).publicWords u 0).val=(A₀).frame :=
    (reader.siteOperandsWith physical P ordinary (fun v => loc v) fit L.header u).frameBase_word
      ((ordinary).publicWords u)
      (reader.arena_fitsWith physical P ordinary fit (fun v => (places v).valuation)
        (fun v => (places v).entry) (fun v => (places v).totals) (fun v => installed v) L u hdr copiesFit memFit).1
  refine PinStart.JointClock.ofPhysicalPost task.id U (fun u => (B u).used) (fun _ => task) (fun _ => A₀)
    r exteriorBudget global localRoom fixedTicks routeK emitted visits
    (pairedTableParameters (k+1) s+Fintype.card (paid.Entry ⊕ ι)) rw reader.charge early arguments
    (fun a u => (post a u).2) base (fun _ => position) ?_ rectangle ?_
  · intro a u p call
    rw [CellDispatch.memory_after_owned_calls call.property]
    exact ((post a u).1).teamAt (base u) (chosen.2.choose_spec pin ⟨x.val,x.property.1⟩ u).2.1.frame.pins
  · intro a p call z receipt ret
    exact reader.deployedLeadClock physical P S fit W pos sites edges ports copies bundles headerFactor L t task
      exteriorBudget fixed regions hdr copiesFit memFit hw teamFit param gadgets teams position endRoom clock
      pin ⟨x.val,x.property.1⟩ (B 0) (a 0) (post a 0).1 call z receipt ret


set_option maxRecDepth 7000 in
set_option maxHeartbeats 2400000 in
/-- The joint clock problem on the chosen all-pin boot. Keeping this type named
prevents the full physical history and evaluator from expanding during installation. -/
def ChosenReader.DeployedClockRequest (fixed : Routing.Block (R+1))
    (regions : JointRoom dir first a (signedBootStripe first) st) (copiesFit : reader.packetBitCount≤r)
    (memFit : (A₀).next<2^rw) (hw : 0<rw) (three : 2<R+1) (hdr : 0<L.header) (cap : L.header≤r*link)
    (clock : ∀ u, packetUnitBudget ((args) u).advice.count rw (frame u)
      ((sewn).pinLayout u ((args) u).ibase ((args) u).hbase ((args) u).starbase)≤S.limit.val)
    (global localRoom routeK fixedTicks emitted visits : ℕ) : Prop :=
    let chosen := reader.deployedFrozenSites_boots physical P S fit W pos sites edges ports copies bundles headerFactor L
      t task exteriorBudget fixed regions copiesFit memFit hw three hdr cap clock
    let cost := uniformWindows r (R+1) exteriorBudget global localRoom routeK fixedTicks emitted visits
    ∀ (pin : Fin indexWidth → Bool)
        (x : {z // PositiveExterior sewn args pin rw z ∧
          PinStart.preCallSupport (fun y u => (chosen.2.choose pin y u).start) task.id z}),
      let B := chosen.2.choose pin ⟨x.val,x.property.1⟩
      let U := fun u => (B u).start
      (∀ (a : PinStart.JointPrefix task.id U) u, let v := PinStart.visits task.id U (a u)
        (B u).used+traceCost ((B u).pins (a u).1).val.1+traceCost v.profile.val.1+traceCost v.routing.val.1 ≤
          cost.core+cost.before) →
      (∀ (a : PinStart.JointPrefix task.id U) u, let input := PinStart.afterRoute task.id U (a u)
        traceCost input.val.1+privateDirectoryTicks ((actual).publicWords u) input.val.2.2 ≤ cost.argumentsCalls) →
      (∀ (a : PinStart.JointPrefix task.id U) u, let p := a u
        let mac := install SparseExterior.driver (k+1) (U u).routines
        ReaderKept A₀ (6+3*reader.gates+query) indexWidth (B u).memory ((B u).pins p.1).val.2.2 p.2.val.2.2 ∧
        ∀ call : Returns callOwnedCells ((actual).publicWords u) mac p.2.val.2.1 p.2.val.2.2,
          ∀ z : Returns (finishExpansion signedOccurrences) ((actual).publicWords u) mac call.val.2.1 call.val.2.2,
            Nonempty (PinStart.PhysicalPost (teams:=R+1) (d:=pairedTableParameters (k+1) s+Fintype.card (paid.Entry ⊕ ι))
              (width:=rw) u task global localRoom emitted visits ((actual).publicWords u) mac call.val.2.1 call.val.2.2 z)) →
      PinStart.JointClock task.id U (fun u => (B u).used) cost

set_option maxRecDepth 7000 in
set_option maxHeartbeats 2400000 in
/-- The original joint-clock proof with its full dependent output kept as
the named request until a concrete prefix is supplied. -/
theorem ChosenReader.deployedFrozenSites_clockRequest (fixed : Routing.Block (R+1))
    (regions : JointRoom dir first a (signedBootStripe first) st) (copiesFit : reader.packetBitCount≤r)
    (memFit : (A₀).next<2^rw) (hw : 0<rw) (three : 2<R+1) (hdr : 0<L.header) (cap : L.header≤r*link)
    (clock : ∀ u, packetUnitBudget ((args) u).advice.count rw (frame u)
      ((sewn).pinLayout u ((args) u).ibase ((args) u).hbase ((args) u).starbase)≤S.limit.val)
    (param : task.p.parameters=pairedTableParameters (k+1) s)
    (gadgets : Fintype.card (paid.Entry ⊕ ι)=task.p.report.gadgets) (teams : task.cube.teams=R+1)
    (teamFit : R+1<2^rw) (position : (A₀).next≤task.cube.header.header)
    (endRoom : task.endAddress rw query guesses reader.gates < 2^rw)
    (rectangle : 512*((R+1)+1)*(pairedTableParameters (k+1) s+Fintype.card (paid.Entry ⊕ ι)+1)*(rw+1)+
      (7+reader.charge) ≤ r)
    (global localRoom routeK fixedTicks emitted visits : ℕ) :
    reader.DeployedClockRequest physical P S fit W pos sites edges ports copies bundles headerFactor L
      t task exteriorBudget fixed regions copiesFit memFit hw three hdr cap clock global localRoom routeK fixedTicks emitted visits := by
  unfold DeployedClockRequest
  exact @ChosenReader.deployedFrozenSites_joint_clock K _ D m ι _ paid aux q k s ord C chart _ _
    R r rw pinWidth pc a link ec axes d reader physical P S fit gridOrder W pos ns ne np sites edges ports
    copies bundles headerFactor L reserve o field t task exteriorBudget fixed regions copiesFit memFit hw three hdr cap clock
    param gadgets teams teamFit position endRoom rectangle global localRoom routeK fixedTicks emitted visits

end Diagonal

end BorderVNP
end Computability
end OAI
