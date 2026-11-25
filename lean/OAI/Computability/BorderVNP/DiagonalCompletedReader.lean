import OAI.Computability.BorderVNP.DiagonalChosenFinishReceipt
import OAI.Computability.BorderVNP.DiagonalPositiveCoreReadback

/-! # Native team and reader readback on the accepted report candidate -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.UncheckedCandidate

open VPVNP.BurstRAM TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader
open CompactMachine CellMacro.Generator _root_.OAI.Computability.BorderVNP.Cube DiagonalTallyCellReports

variable {axes box lanes selectors symbols teams n w reserve groups cap dim digits : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO}
    {fields : PositiveFields reserve axes groups cap teams dim digits}
    (X : UncheckedCandidate id gen n w teams dim digits) (H : X.Completion fields)
    (reports : NativeReports X.assigned) (raw : Fin (teams*dim*digits) → Bool)
    (ok : positivePass (X.team reports raw) (X.joined reports raw) (X.candidate reports raw))
    (u : Fin teams)
local notation3 (prettyPrint := false) "canonical" => canonicalReports X.assigned H.core
local notation3 (prettyPrint := false) "S₀" => X.team canonical raw u
local notation3 (prettyPrint := false) "p₀" => (X.candidate canonical raw).1 u

/-- The operand ledger and shared low-address placement for a guarded
source at one team. The projected ledger is the one constructed from its
real selected rows, including choices whose later matrix entry vanishes. -/
structure Completion.Protected (X : UncheckedCandidate id gen n w teams dim digits)
    (H : X.Completion fields) (raw : Fin (teams*dim*digits) → Bool) (u : Fin teams)
    (l : SignedTaskArena.Layout) (A : StartupArena) : Prop where
  post : (H.input raw u).post = l.after
  retained : ∀ j<l.after.start, j≠((X.team (canonicalReports X.assigned H.core) raw u).pub 0).val+35 →
    (H.input raw u).selected j=((X.candidate (canonicalReports X.assigned H.core) raw).1 u).2.val.2.2 j
  frame : ((X.team (canonicalReports X.assigned H.core) raw u).pub 0).val = A.frame
  placement : A.next ≤ l.cube.header.header

/-- The branch selector retained the actual numbered team on any passing
candidate. The local call directory is read on this very execution. -/
theorem Completion.teamAt (l : SignedTaskArena.Layout) (A : StartupArena)
    (kept : H.Protected X raw u l A) :
    (((X.team reports raw u).finish ((X.candidate reports raw).1 u) (ok.2 u)).val.2.2
      ((X.team reports raw u).pub 0).val).val=u.val := by
  have eq := (((X.completed H).pass_iff reports raw).mp ok).1
  subst reports
  exact (S₀).teamOfFinishReceipt p₀ (ok.2 u) l A (H.input raw u) kept.post kept.retained kept.frame
    kept.placement ((X.joined canonical raw (X.candidate canonical raw).1).teamAt u)

end RoutingISA.Evaluator.UncheckedCandidate

namespace Diagonal

open Branch Crossing ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier ResidueRates
open DiagonalResidueRAM VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena
open TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader RoutingISA.Evaluator
open CompactMachine CellMacro.Generator BorderVNP.Cube DiagonalTallyCellReports
open scoped Classical BigOperators
set_option maxHeartbeats 950000
set_option synthInstance.maxSize 3000

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {R : CommonField G aux q k s ord} {chart : AdvisedBranch R}
    [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
    {T r mult w pin : ℕ} (reader : ChosenReader chart (T+1) r mult w w pin)
local notation "par" => pairedTableParameters (k+1) s
local notation "J" => G.Entry ⊕ ι
local notation "query" => Board.Physical par pin w J
local notation "guess" => Guess (Fin par) reader.gridRank (Nat.clog 2 R.p+1) (Nat.clog 2 R.p)
local notation "bits" => (par+2)*pin
local notation "dim" => par+Fintype.card J

variable {axes box lanes selectors symbols n sites time link inner length : ℕ}
    {id : TableEntry axes box lanes selectors symbols → ℕ} {gen : Fragment IO} {Edge : Type}
    (l : SignedTaskArena.Layout) (A : StartupArena)
    (W : Wiring T sites time ((pairedTableParameters (k+1) s+2)*pin) link inner length Edge)

/-- Physical chart inputs on the single selected lead-team execution. These
are local address and memory observations before subtotal verification. -/
structure ChosenReader.LeadPacketAt
    (S : PositiveTeam id gen n w) (p : S.Prefix) (row col : Fin bits → Bool) where
  /-- The complete extension of the installed reference packet. -/
  extension : Fin 81 → Word w
  /-- Address of the reference pin array. -/
  star : ℕ
  /-- The shared exterior words of the positive branch. -/
  exterior : Exterior T sites link → Bool
  /-- The actual destination and sources of the shared-header copy. -/
  frame : BroadcastFrame
  /-- Offset of the copied entry stripe in each literal. -/
  offset : ℕ
  /-- Number of advice bits available to the public copy. -/
  copied : ℕ
  /-- The full chronological header carried by the boot. -/
  header : List Bool
  boot : let start := l.entry w (Fintype.card query) (Fintype.card guess) reader.gates
    let packet := reader.nativePacket (l.valuation w) start A.ibase A.hbase l.tallyBits extension
    BootHeaderState (W.processorFields 0 col exterior A.ibase A.hbase star) frame ⟨offset,copied,A.dense⟩
      packet S.pub header S.bank S.memory
  tape : (S.pins p.1).val.1.flatMap TeamRAM.Event.choices=List.ofFn row
  operand : S.pub 20=word w (l.entry w (Fintype.card query) (Fintype.card guess) reader.gates)
  stride : (W.pinLayout 0 A.ibase A.hbase star).stride<2^w
  extent : sites*(W.program.length+time)<2^w
  pins : bits ≤ sites*(W.program.length+time)
  loops : Pins.LoopFits w (W.pinLayout 0 A.ibase A.hbase star)
  separated : Pins.Separated (W.pinLayout 0 A.ibase A.hbase star)
  indexRoom : bits ≤ A.count
  packetRoom : (6+3*reader.gates+Fintype.card query)*w ≤ A.copied
  endRoom : l.endAddress w (Fintype.card query) (Fintype.card guess) reader.gates < 2^w
  kept : ReaderKept A (6+3*reader.gates+Fintype.card query) bits S.memory (S.pins p.1).val.2.2 p.2.val.2.2

variable {reserve groups cap digits B : ℕ}
  {fields : PositiveFields reserve axes groups cap (T+1) (pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)) digits}
  (X : UncheckedCandidate id gen n w (T+1) (pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)) digits)
  (H : X.Completion fields)
  (reports : NativeReports X.assigned)
  (raw : Fin ((T+1)*(pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*digits) → Bool)
  (ok : positivePass (X.team reports raw) (X.joined reports raw) (X.candidate reports raw))
local notation3 (prettyPrint := false) "canonical" => canonicalReports X.assigned H.core
local notation3 (prettyPrint := false) "lead" => X.team canonical raw 0
local notation3 (prettyPrint := false) "chosen" => (X.candidate canonical raw).1 0

/-- On a physically accepted candidate the guarded source uniquely fixes
the report bits and shared substotals. The native reader at its actual
finishing memory therefore sees the decoded path's original total powers
and scalar multiplicities. -/
noncomputable def readerAtCompletedCandidate
    (pdim : l.p.parameters=par) (gdim : Fintype.card J=l.p.report.gadgets) (teamCount : l.cube.teams=T+1)
    (row col : Fin bits → Bool) (tally : Tally (Fin (T+1)) (Fin par) J B)
    (protectedWords : H.Protected X raw 0 l A) (input : reader.LeadPacketAt l A W lead chosen row col)
    (columns : ∀ c, (∑ i,H.rows i c)=∑ i,DiagonalTallyRAM.tallyRow (tally.numberScalars (Fintype.equivFin J)) i c) :
    ReaderImage reader (X.team reports raw 0).pub
      ((X.team reports raw 0).finish ((X.candidate reports raw).1 0) (ok.2 0)).val.2.2 row col
      tally.exponents (fun x => ∑ a : Fin (T+1),tally.counts a x) := by
  obtain ⟨eq,claim⟩ := ((X.completed H).pass_iff reports raw).mp ok
  subst reports
  let start := l.entry w (Fintype.card query) (Fintype.card guess) reader.gates
  let packet := reader.nativePacket (l.valuation w) start A.ibase A.hbase l.tallyBits input.extension
  have len : packet.entry.length=6+3*reader.gates+Fintype.card query := payload_length ..
  exact readerImageOfReceipt reader lead chosen (ok.2 0) l A pdim gdim teamCount (fields.withSubtotals raw)
    H.rows (H.input raw 0) protectedWords.post protectedWords.retained input.extension W input.star input.exterior row col
    input.frame input.offset input.copied input.header tally input.boot input.tape input.operand protectedWords.frame
    input.stride input.extent input.pins input.loops input.separated protectedWords.placement input.indexRoom
    (len ▸ input.packetRoom) input.endRoom (len ▸ input.kept) claim H.rowFit H.sumFit columns

/-- Physical inputs belonging to the exact canonical inverse of the report
check. Each local ledger retains the low fields of the same selected
processor; the lead packet carries its own true pin choice and advice. -/
structure ChosenReader.CompletedPacket (X : UncheckedCandidate id gen n w (T+1)
    (pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι)) digits)
    (H : X.Completion fields) (row col : Fin bits → Bool) where
  /-- The local post-call task allocation used by each returning team. -/
  layout : Fin (T+1) → SignedTaskArena.Layout
  /-- The length allocation holding each team’s startup operands and pins. -/
  arena : Fin (T+1) → StartupArena
  protectedWords : ∀ t, H.Protected X (PositiveFields.canonicalSubtotals digits H.rows) t (layout t) (arena t)
  parameters : (layout 0).p.parameters=par
  gadgets : Fintype.card J=(layout 0).p.report.gadgets
  teams : (layout 0).cube.teams=T+1
  /-- The live pin and field-reader copy on the canonical lead execution. -/
  leadPacket : let reports := canonicalReports X.assigned H.core
    let claim := PositiveFields.canonicalSubtotals digits H.rows
    reader.LeadPacketAt (layout 0) (arena 0) W (X.team reports claim 0)
      ((X.candidate reports claim).1 0) row col

end Diagonal

end BorderVNP
end Computability
end OAI
