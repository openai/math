import OAI.Computability.BorderVNP.DiagonalBootedLeadPacket

/-! # The pin reader specialized at a returned physical boot -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier ResidueRates
open DiagonalResidueRAM VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena
open TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader RoutingISA.Evaluator
open CompactMachine CellMacro.Generator BorderVNP.Cube DiagonalTallyCellReports
open scoped Classical BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {e : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField e aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult w psize pc routines a link n ec : ℕ} (reader : ChosenReader chart (R+1) r mult w w psize)
    (physical : UniversalMachine.Program) (P : TeamOpcode.Program pc 64 32 routines)
    (S : SiteData R r 64 32 w a) (fit : fitsWith physical 64 32 r w a R link n ec)
    (L : Routing.WireLayout (R+1) r link)
    (sa : Fin (R+1) → SignedTaskArena.Layout) (cable plan : Fin (R+1) → ℕ)
    (extension : Fin (R+1) → Fin 81 → Word w)
    (dir : Packing.Directory.Layout) (bootStripe geom : GeometryAdvice.Stripe)
    (bootBits geomBits : Fin (R+1) → List Bool) (strings : Fin dir.entries → Fin dir.description → Bool)
local notation "bits" => (pairedTableParameters (k+1) s+2)*psize
local notation "Q" => Fintype.card (Board.Physical (pairedTableParameters (k+1) s) psize w (e.Entry ⊕ ι))
local notation3 (prettyPrint := false) "N" => Fintype.card (Guess (Fin (pairedTableParameters (k+1) s)) reader.gridRank
  (Nat.clog 2 C.p+1) (Nat.clog 2 C.p))

/-- The supported lead reader on one concrete boot, after the physical
startup evidence and all address bounds have been checked. -/
def ChosenReader.ProtectedReader {sites t inner n : ℕ} {Edge : Type}
    (l : SignedTaskArena.Layout) (A : StartupArena) (G : Wiring R sites t bits link inner n Edge)
    {gen : Fragment IO} {pub : Fin (R+1) → Arg → Word w} {regs : Fin (R+1) → Bank w}
    {args : Fin (R+1) → UnitAddresses} {col : Fin bits → Bool} {ext : Exterior R sites link → Bool}
    (B : BootedPinStart gen G pub regs args col ext 0)
    (limit burst : ℕ) (cap : TeamScales.width n (1/2) ≤ burst) : Type :=
  ∀ next : PositiveContinuation l.id gen n (pub 0) B.start.routines B.start.bank B.memory B.pins B.used limit,
    let team := next.team burst cap B.frameFit
    ∀ p : team.Prefix, ReaderKept A (6+3*reader.gates+Q) bits B.memory (B.pins p.1).val.2.2 p.2.val.2.2 →
      reader.LeadPacketAt l A G team p p.1 col

/-- First specialize to the physical startup and its recovered
common header. Its resulting input operation works simultaneously
for every returning continuation and every later pin. -/
noncomputable def ChosenReader.leadPacketAfterBoot {x b h j z : ℕ}
    (id : TableEntry x b h j z → ℕ) (gen : Fragment IO) (col : Fin bits → Bool)
    (ext : Exterior R r link → Bool) (header : List Bool) (positiveHeader : 0 < L.header)
    (copies : reader.packetBitCount ≤ r) (limit burst : ℕ) (cap : TeamScales.width n (1/2) ≤ burst) :
    let A := reader.startupArenaWith (n:=n) (reg:=64) physical a link L.header
    let starts := fun u : Fin (R+1) => (sa u).entry w Q N reader.gates
    let values := fun u : Fin (R+1) => (sa u).valuation w
    let totals := fun u : Fin (R+1) => (sa u).tallyBits
    let place := fun u : Fin (R+1) => ReaderPlacement.inArena A (values u) (starts u) (totals u) (extension u)
    let ordinary := withOrdinary S sa A cable plan (fun _ => Q) (fun _ => N) (fun _ => reader.gates)
    let site := reader.startupSitesWith physical P ordinary place fit dir bootStripe geom bootBits geomBits strings L.header
    let W := wiringWith physical P site bits link n ec fit
    let pack := fun u : Fin (R+1) => reader.packetAt (place u)
    let off := adviceOffsetWith physical r 32 64 w n
    let args := fun u : Fin (R+1) => A.unitAddresses off (pack u)
    let star := (args 0).starbase
    let f := W.transferFrame 0 L.header A.broadcastBase
    ∀ B : BootedPinStart gen W site.publicWords site.registers args col ext 0,
      BootHeaderState (W.processorFields 0 col ext A.ibase A.hbase star) f (args 0).advice (pack 0)
        (site.publicWords 0) header B.out B.memory →
      A.next < 2^w → (sa 0).endAddress w Q N reader.gates < 2^w →
      ∀ next : PositiveContinuation id gen n (site.publicWords 0) B.start.routines B.start.bank B.memory B.pins B.used limit,
      let T := next.team burst cap B.frameFit
      ∀ p : T.Prefix, ReaderKept A (6+3*reader.gates+Q) bits B.memory (B.pins p.1).val.2.2 p.2.val.2.2 →
        reader.LeadPacketAt (sa 0) A W T p p.1 col := by
  intro A starts values totals place ordinary site W pack off args star f B stored ceiling endRoom next T p kept
  exact reader.leadPacketOfBootedSource physical P S fit L sa cable plan extension dir bootStripe geom bootBits geomBits
    strings id gen col ext header positiveHeader copies limit burst cap B next p stored ceiling endRoom kept

end Diagonal

end BorderVNP
end Computability
end OAI
