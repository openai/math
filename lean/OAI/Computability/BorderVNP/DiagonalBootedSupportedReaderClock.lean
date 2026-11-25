import OAI.Computability.BorderVNP.DiagonalSupportedReaderClock
import OAI.Computability.BorderVNP.DiagonalNativeBootPinStart

/-! # The charged lead reader on a booted positive prefix and returning private calls -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open Branch Crossing ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier Diagonal
open DiagonalResidueRAM ResidueRates VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena
open TeamContraction TeamContraction.JointHeader RoutingISA.Evaluator RoutingISA.CompactMachine CellMacro.Generator
open BorderVNP.Cube
open scoped Classical BigOperators

variable {K : Type} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {e : PaidIdentity K D m}
    {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
    {C : CommonField e aux q k s ord} {chart : AdvisedBranch C}
    [Fact C.p.Prime] [Algebra (ZMod C.p) chart.E]
    {R r mult w pin : ℕ} (reader : ChosenReader chart (R+1) r mult w w pin)
local notation "par" => pairedTableParameters (k+1) s
local notation "J" => e.Entry ⊕ ι
local notation "bits" => (par+2)*pin
local notation "query" => Board.Physical par pin w J
local notation "guesses" => Guess (Fin par) reader.gridRank (Nat.clog 2 C.p+1) (Nat.clog 2 C.p)

variable {sites t link inner n : ℕ} {Edge : Type} {gen : Fragment IO}
    {W : Wiring R sites t ((pairedTableParameters (k+1) s+2)*pin) link inner n Edge}
    {pub : Fin (R+1) → Arg → Word w} {reg : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    {col : Fin ((pairedTableParameters (k+1) s+2)*pin) → Bool} {ext : Exterior R sites link → Bool}
    (B : BootedPinStart gen W pub reg args col ext 0)
local notation3 (prettyPrint := false) "ad" => args 0
local notation3 (prettyPrint := false) "fr" => W.transferFrame 0 (args 0).header (args 0).dst
local notation3 (prettyPrint := false) "loc" => W.pinLayout 0 (args 0).ibase (args 0).hbase (args 0).starbase
local notation3 (prettyPrint := false) "src" => W.processorFields 0 col ext (args 0).ibase (args 0).hbase (args 0).starbase
local notation3 (prettyPrint := false) "mac" => install gen n B.start.routines

/-- Starting before the local deadline is assigned, every returning team-zero
reader uses at most its seven guard instructions and the charged chosen
circuit. The loaded registers and the branch-updated pin registers are read
at their own physical stages. -/
theorem BootedPinStart.supported_lead_ticks {dim box lanes sels syms : ℕ} {id : TableEntry dim box lanes sels syms → ℕ}
    (p : B.start.Prefix id) (l : SignedTaskArena.Layout) (A : StartupArena) (pdim : l.p.parameters=par)
    (gdim : Fintype.card J=l.p.report.gadgets) (teams : l.cube.teams=R+1)
    (subt : ℕ) (extension : Fin 81 → Word w) (hdr : List Bool)
    (iBase : (args 0).ibase=A.ibase) (hBase : (args 0).hbase=A.hbase) (dst : (args 0).advice.dst=A.dense)
    (frame : (pub 0 0).val=A.frame) (stride : (loc).stride<2^w)
    (total : sites*(W.program.length+t)<2^w) (width : bits ≤ sites*(W.program.length+t))
    (loop : Pins.LoopFits w loc) (sep : Pins.Separated loc)
    (geometry : A.next≤l.cube.header.header) (index : bits ≤ A.count)
    (call : Returns callOwnedCells (pub 0) mac p.2.val.2.1 p.2.val.2.2)
    (z : Returns (finishExpansion signedOccurrences) (pub 0) mac call.val.2.1 call.val.2.2)
    {claim : List (List Bool)} {rows : Fin (R+1) → Fin (par+Fintype.card J) → ℕ}
    (receipt : PositiveFields.FinishInput 0 rows subt (pub 0) mac call.val.2.1 call.val.2.2 claim)
    (placed : receipt.post=l.after)
    (protect : ∀ a<l.after.start, a≠(pub 0 0).val+35 → receipt.selected a=call.val.2.2 a) :
    let u := Fintype.card query
    let v := Fintype.card guesses
    let start := l.entry w u v reader.gates
    let packet := reader.nativePacket (l.valuation w) start A.ibase A.hbase l.tallyBits extension
    BootHeaderState src fr (ad).advice packet (pub 0) hdr B.out B.memory →
    pub 0 20=word w start → packet.entry.length*w ≤ A.copied → l.endAddress w u v reader.gates<2^w →
    ReaderKept A packet.entry.length bits B.memory (B.pins p.1).val.2.2 p.2.val.2.2 →
    ∀ ret : Returns leadEntry (pub 0) mac z.val.2.1 z.val.2.2, traceCost ret.val.1 ≤ 7+reader.charge := by
  intro u v start packet loaded op advice endFit before ret
  have same : (loc).guessWidth=bits := by simp [Pins.Layout.guessWidth,Wiring.pinLayout]
  let row : Fin bits → Bool := fun j => p.1 (Fin.cast same.symm j)
  have spell : (B.pins p.1).val.1.flatMap TeamRAM.Event.choices=List.ofFn row := by
    have castTape {a b : ℕ} (e : a=b) (g : Fin a → Bool) :
        List.ofFn g=List.ofFn (fun i : Fin b => g (Fin.cast e.symm i)) := by
      subst b
      rfl
    exact (B.outputs p.1).1.trans (castTape same p.1)
  have atCall := CellDispatch.memory_after_owned_calls call.property
  have carried : ReaderKept A packet.entry.length bits B.memory (B.pins p.1).val.2.2 call.val.2.2 := atCall.symm ▸ before
  rw [iBase,hBase] at loaded loop sep stride
  have adviceEq : (ad).advice=⟨(ad).advice.offset,(ad).advice.count,A.dense⟩ := by
    rcases h : (ad).advice with ⟨o,c,v⟩
    have eq := h ▸ dst
    exact congrArg (fun d => AdviceLayout.mk o c d) eq
  rw [adviceEq] at loaded
  exact reader.leadTicks_after_finish l A pdim gdim teams subt extension W (ad).starbase ext row col fr
    (ad).advice.offset (ad).advice.count (pub 0) mac hdr B.start.bank B.memory (B.pins p.1) spell claim rows receipt placed z
    loaded op frame stride total width loop sep geometry index advice endFit protect carried ret

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
