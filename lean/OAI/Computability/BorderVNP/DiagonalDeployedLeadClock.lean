import OAI.Computability.BorderVNP.DiagonalFrozenSignedDeployment
import OAI.Computability.BorderVNP.DiagonalBootedLeadPacket
import OAI.Computability.BorderVNP.DiagonalDeployedReaderHeader
import OAI.Computability.BorderVNP.DiagonalBootedSupportedReaderClock
import OAI.Computability.BorderVNP.DiagonalUniformPostReceipt

/-! # The lead reader clock on the physically installed frozen signed tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Crossing Branch Cover Packing Packing.DeckGrid CellEntries ExternalSew ExternalSew.RowTrace
open VPVNP BurstRAM VerifierNetwork ParseBatch ParseBatchVerifier Prewire VPVNP.ParseGrammar
open TeamContraction TeamContraction.ProcessorSlots RoutingISA RoutingISA.Pins RoutingISA.Transmission
open GeometryAdvice GeometryFrameEncoding PackedHistoryCircuit TeamScales MvPolynomial
open DiagonalResidueRAM ResidueEntryInput ResidueRates ResiduePins RoutingISA.Evaluator CompactMachine CellMacro.Generator JointHeader
open scoped Classical BigOperators

set_option maxRecDepth 6000
set_option maxHeartbeats 3500000

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


local notation3 (prettyPrint := false) "held" => reader.deployedFrozenSites physical P S fit W pos sites edges ports
  copies bundles headerFactor L t task exteriorBudget
local notation3 (prettyPrint := false) "off" => StartupArena.literal A₀/4
local notation3 (prettyPrint := false) "ell" => GeometryAdviceRate.stripeWidth (GeometryOutput.packetCount reserve t.size o field*rw) r
local notation3 (prettyPrint := false) "wordExt" u => Allocation.fields (pinned u) fresh reserve t.size o field off ell
local notation3 (prettyPrint := false) "payloads" => fun _ : Fin (R+1) =>
  GeometryAdvice.serialized (GeometryAdvice.packet (w:=rw) fresh (Allocation.packed fresh reserve t.size o field rw) t
    (fun i => StartupArena.broadcastBase A₀+1+Fin.val i))
local notation3 (prettyPrint := false) "strings" => W.seedLiteralMatrix pos (ParseTable.signedLiteralCode ord) sites edges ports
  copies bundles (headerFactor*logWidth r (k+1))

/-- The actual ordinary operand bank in the signed frozen literal is the
startup allocator's unit, including its exact dense advice count. -/
theorem ChosenReader.deployed_publicOperands (u : Fin (R+1)) :
    let A := A₀
    let packet := reader.nativePacket (task.valuation rw) (task.entry rw query guesses reader.gates)
      A.ibase A.hbase task.tallyBits (wordExt u)
    (held).publicWords u=(A.operands u (adviceOffsetWith physical r 32 64 rw (k+1)) packet).bank
      ((ordinary).publicWords u) := by
  intro A packet
  let vals := fun _ : Fin (R+1) => task.valuation rw
  let entries := fun _ : Fin (R+1) => task.entry rw query guesses reader.gates
  let totals := fun _ : Fin (R+1) => task.tallyBits
  let extensions := fun v : Fin (R+1) => wordExt v
  exact congrArg (fun o : PacketOperands => o.bank ((ordinary).publicWords u))
    (reader.siteOperands_arenaWith physical P ordinary fit vals entries totals extensions L u)

/-- The chosen deployed literal bounds every returning lead reader before
any later machine acceptance is known. The local receipt can contain
arbitrary declared subtotals. -/
theorem ChosenReader.deployedLeadClock
    (fixed : Routing.Block (R+1))
    (regions : JointRoom dir first a (signedBootStripe first) (Allocation.stripe fresh reserve t.size o field off ell))
    (positive : 0 < L.header) (copiesFit : reader.packetBitCount ≤ r)
    (ceiling : (A₀).next < 2^rw) (hw : 0<rw) (teamFit : R+1<2^rw)
    (param : task.p.parameters=pairedTableParameters (k+1) s)
    (gadgets : Fintype.card (paid.Entry ⊕ ι)=task.p.report.gadgets) (teams : task.cube.teams=R+1)
    (position : (A₀).next ≤ task.cube.header.header) (endRoom : task.endAddress rw query guesses reader.gates < 2^rw) :
    let A := A₀
    let z := held
    let wire := wiringWith physical P z indexWidth link (k+1) ec fit
    let pack := fun v : Fin (R+1) => reader.nativePacket (task.valuation rw) (task.entry rw query guesses reader.gates)
      A.ibase A.hbase task.tallyBits (wordExt v)
    let off₀ := adviceOffsetWith physical r 32 64 rw (k+1)
    let args := fun v : Fin (R+1) => A.unitAddresses off₀ (pack v)
    let frame := fun u => wire.transferFrame u (args u).header (args u).dst
    let loc := fun u => wire.pinLayout u (args u).ibase (args u).hbase (args u).starbase
    (∀ u, packetUnitBudget (args u).advice.count rw (frame u) (loc u) ≤ z.limit.val) →
    ∀ (col : Fin indexWidth → Bool) (x : {e // PositiveExterior wire args col rw e})
      (B : BootedPinStart SparseExterior.driver wire z.publicWords z.registers args col x.val 0)
      (p : B.start.Prefix task.id),
      ReaderKept A (6+3*reader.gates+query) indexWidth B.memory (B.pins p.1).val.2.2 p.2.val.2.2 →
      let mac := install SparseExterior.driver (k+1) B.start.routines
      ∀ call : Returns callOwnedCells (z.publicWords 0) mac p.2.val.2.1 p.2.val.2.2,
      ∀ finish : Returns (finishExpansion signedOccurrences) (z.publicWords 0) mac call.val.2.1 call.val.2.2,
      ∀ {P₀ L₀ F H : ℕ},
        PinStart.PhysicalPost (teams:=R+1) (d:=pairedTableParameters (k+1) s+Fintype.card (paid.Entry ⊕ ι))
          (width:=rw) 0 task P₀ L₀ F H (z.publicWords 0) mac call.val.2.1 call.val.2.2 finish →
        ∀ ret : Returns leadEntry (z.publicWords 0) mac finish.val.2.1 finish.val.2.2, traceCost ret.val.1 ≤ 7+reader.charge := by
  intro A z wire pack off₀ args frame loc clock col x B p kept mac call finish P₀ L₀ F H post ret
  let edge : Routing.Block (R+1) := ⟨(⟨0,by have h := L.three; omega⟩,⟨1,by have h := L.three; omega⟩),Nat.zero_lt_one⟩
  have headerCap : L.header≤r*link := by have h := L.fits edge; omega
  have ready (u : Fin (R+1)) : (args u).Fitted wire u (pack u) (z.publicWords u) off₀ ∧
      packetUnitBudget (args u).advice.count rw (frame u) (loc u) ≤ z.limit.val := by
    refine ⟨?_,clock u⟩
    rw [show z.publicWords u=_ from reader.deployed_publicOperands physical P S fit W pos sites edges ports copies bundles headerFactor L t task exteriorBudget u]
    exact fitted_programArena physical P z fit L.header reader.packetBitCount u (pack u) ((ordinary).publicWords u)
      L.three positive headerCap (reader.packetAt_length (ReaderPlacement.inArena A (task.valuation rw)
        (task.entry rw query guesses reader.gates) task.tallyBits (wordExt u))).le copiesFit ceiling
  have loaded := (reader.deployed_boot_reader physical P S fit W pos sites edges ports copies bundles headerFactor L t task
    exteriorBudget fixed regions copiesFit ceiling hw teams teamFit position endRoom ready col x 0 B).2.1
  let values := fun _ : Fin (R+1) => task.valuation rw
  let starts := fun _ : Fin (R+1) => task.entry rw query guesses reader.gates
  let totals := fun _ : Fin (R+1) => task.tallyBits
  let extensions := fun u : Fin (R+1) => wordExt u
  let place := fun u : Fin (R+1) => ReaderPlacement.inArena A (values u) (starts u) (totals u) (extensions u)
  let ops := reader.siteOperandsWith physical P ordinary place fit L.header
  have geom := reader.chosen_packet_pin_bounds physical P z fit values starts totals extensions L 0 positive copiesFit ceiling
  have base := (ops 0).frameBase_word ((ordinary).publicWords 0)
    (reader.arena_fitsWith physical P ordinary fit values starts totals extensions L 0 positive copiesFit ceiling).1
  have receipt := SignedTaskArena.joint_ordinary S (fun _ => task) A (fun _ => origin) (fun _ => 0)
    (fun _ => query) (fun _ => guesses) (fun _ => reader.gates) ops dir first pack
    (signedBootStripe first) (Allocation.stripe fresh reserve t.size o field off ell) (fun _ => []) payloads strings 0
  have length : (pack 0).entry.length=6+3*reader.gates+query := DiagonalResidueRAM.payload_length ..
  exact B.supported_lead_ticks reader p task A param gadgets teams rw (extensions 0) (JointHeader.observed L x.val fixed) rfl rfl rfl base
    geom.1 geom.2.1 geom.2.2.1 geom.2.2.2.1 geom.2.2.2.2.1 position geom.2.2.2.2.2.1
    call finish post.receipt post.location post.retained loaded receipt.2.2.2.2.2
    (length.symm ▸ geom.2.2.2.2.2.2) endRoom (length.symm ▸ kept) ret


end Diagonal

end BorderVNP
end Computability
end OAI
