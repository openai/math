import OAI.Computability.BorderVNP.DiagonalCompletedReader
import OAI.Computability.BorderVNP.DiagonalLeadPacketPinBounds
import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart
import OAI.Computability.BorderVNP.RoutingISASignedSiteOperands
import OAI.Computability.BorderVNP.DiagonalNativeTimedArena
import OAI.Computability.BorderVNP.DiagonalTeamPinChoices

/-! # Lead reader input at the actual joint-header boot and supported positive prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader

open VPVNP.BurstRAM RoutingISA RoutingISA.Pins ProcessorSlots

/-- Selecting the positive branch updates register ten. Every saved
register read by the broadcast frame and the full boot memory agree. -/
theorem BootHeaderState.branchRegister {w d : ℕ} {l : Pins.Layout} {F : ProcessorFields l} {f : BroadcastFrame}
    {A : AdviceLayout} {ref : ReferencePacket w d} {pub : Arg → Word w} {hdr : List Bool} {s : Bank w} {m : Memory w}
    (h : BootHeaderState F f A ref pub hdr s m) (flag : Word w) :
    BootHeaderState F f A ref pub hdr (Function.update s 10 flag) m := by
  refine ⟨h.input,h.frame,h.core,h.extension,h.entry,h.reference,h.header,?_⟩
  simpa [BroadcastFrame.Stable,readings,Function.update] using h.registers

end TeamContraction.JointHeader

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

/-- Install the ordinary and packed operands first, then read the packet at
the actual positive program's memory. The selected row is the spelling of
this native prefix's own pin guesses. -/
noncomputable def ChosenReader.leadPacketOfBootedSource {x b h j z : ℕ}
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
      ∀ next : PositiveContinuation id gen n (site.publicWords 0) B.start.routines B.start.bank B.memory B.pins B.used limit,
      let T := next.team burst cap B.frameFit
      ∀ p : T.Prefix,
      BootHeaderState (W.processorFields 0 col ext A.ibase A.hbase star) f (args 0).advice (pack 0)
        (site.publicWords 0) header B.out B.memory →
      A.next < 2^w → (sa 0).endAddress w Q N reader.gates < 2^w →
      ReaderKept A (6+3*reader.gates+Q) bits B.memory (B.pins p.1).val.2.2 p.2.val.2.2 →
      reader.LeadPacketAt (sa 0) A W T p p.1 col := by
  intro A starts values totals place ordinary site W pack off args star f B next T p stored ceiling endRoom kept
  have bounds := reader.chosen_packet_pin_bounds physical P site fit values starts totals extension L 0 positiveHeader copies ceiling
  have boot := stored.branchRegister (B.memory (W.transferFrame 0 (args 0).header (args 0).dst).dst)
  have inputs := SignedTaskArena.joint_ordinary S sa A cable plan (fun _ => Q) (fun _ => N) (fun _ => reader.gates)
    (reader.siteOperandsWith physical P ordinary place fit L.header) dir (freeStartWith physical r 32 64 w n)
    pack bootStripe geom bootBits geomBits strings 0
  exact ⟨extension 0,star,ext,f,off,A.copied,header,boot,(B.outputs p.1).1,inputs.2.2.2.2.2,
    bounds.1,bounds.2.1,bounds.2.2.1,bounds.2.2.2.1,bounds.2.2.2.2.1,bounds.2.2.2.2.2.1,
    bounds.2.2.2.2.2.2,endRoom,kept⟩


/-- Transport the real lead packet across the decoded pin spelling of a
reconstructed physical prefix. Only the lead team chooses these bits, so
applying the joint pin wiring to its inverse yields exactly the requested row. -/
def ChosenReader.LeadPacketAt.decodedRow {x b h j z sites t wires length : ℕ} {Edge : Type}
    {id : TableEntry x b h j z → ℕ} {gen : Fragment IO} {team : PositiveTeam id gen n w} {phase : team.Prefix}
    {l : SignedTaskArena.Layout} {A : StartupArena} {W : Wiring R sites t bits link wires length Edge}
    {row src col : Fin bits → Bool} (data : reader.LeadPacketAt l A W team phase row col)
    (ib hb sb : Fin (R+1) → ℕ)
    (digits : List.ofFn row=List.ofFn ((W.jointGuess ib hb sb).symm src 0)) :
    reader.LeadPacketAt l A W team phase src col := by
  have lead : (W.jointGuess ib hb sb).symm src 0=src := (W.jointGuess ib hb sb).apply_symm_apply src
  exact (List.ofFn_injective digits |>.trans lead) ▸ data

end Diagonal

end BorderVNP
end Computability
end OAI
