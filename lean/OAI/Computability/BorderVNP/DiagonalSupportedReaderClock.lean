import OAI.Computability.BorderVNP.DiagonalReturnedReaderClock
import OAI.Computability.BorderVNP.RoutingISASignedReaderKeepActual
import OAI.Computability.BorderVNP.RoutingISASignedReaderRoom

/-! # Charging the actual lead reader before agreement of all shared tallies -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier
open DiagonalResidueRAM ResidueRates VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena
open TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader
open RoutingISA.Evaluator DiagonalTallyRAM
open scoped Classical BigOperators

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

/-- On a returning lead-team finish the serialized sums of the actual common
claims supply binary inputs to this chosen reader. Its charged clock covers
every return, including a subtotal which a different team rejects. -/
theorem ChosenReader.leadTicks_after_finish {sites t link inner length : ℕ} {Edge : Type}
    (l : SignedTaskArena.Layout) (A : StartupArena) (pdim : l.p.parameters=par)
    (gdim : Fintype.card J=l.p.report.gadgets) (teams : l.cube.teams=T+1)
    (subt : ℕ) (extension : Fin 81 → Word w)
    (W : Wiring T sites t bits link inner length Edge) (star : ℕ) (ext : Exterior T sites link → Bool)
    (row col : Fin bits → Bool) (f : BroadcastFrame) (off copied : ℕ) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (hdr : List Bool) (bank : Bank w) {loadedBank : Bank w} (boot : Memory w)
    (selected : Pins.Return pub mac bank boot) (tape : selected.val.1.flatMap TeamRAM.Event.choices=List.ofFn row)
    {pre : Bank w} {postCells : Memory w} (claims : List (List Bool))
    (rows : Fin (T+1) → Fin (par+Fintype.card J) → ℕ)
    (h : PositiveFields.FinishInput 0 rows subt pub mac pre postCells claims) (arena : h.post=l.after)
    (z : Returns (finishExpansion signedOccurrences) pub mac pre postCells) :
    let u := Fintype.card query
    let v := Fintype.card guess
    let start := l.entry w u v reader.gates
    let packet := reader.nativePacket (l.valuation w) start A.ibase A.hbase l.tallyBits extension
    let source := W.processorFields 0 col ext A.ibase A.hbase star
    let pins := W.pinLayout 0 A.ibase A.hbase star
    BootHeaderState source f ⟨off,copied,A.dense⟩ packet pub hdr loadedBank boot →
    pub 20=word w start → (pub 0).val=A.frame →
    pins.stride<2^w → sites*(W.program.length+t)<2^w → bits ≤ sites*(W.program.length+t) →
    Pins.LoopFits w pins → Pins.Separated pins →
    A.next ≤ l.cube.header.header → bits ≤ A.count → packet.entry.length*w ≤ A.copied →
    l.endAddress w u v reader.gates < 2^w →
    (∀ k < l.after.start, k≠(pub 0).val+35 → h.selected k=postCells k) →
    ReaderKept A packet.entry.length bits boot selected.val.2.2 postCells →
    ∀ ret : Returns leadEntry pub mac z.val.2.1 z.val.2.2, traceCost ret.val.1 ≤ 7+reader.charge := by
  intro u v start packet source pins loaded op frame stride total width fits sep geometry index advice endFit protect before ret
  have packetLen : packet.entry.length=6+3*reader.gates+u := payload_length ..
  have room := l.reader_room A geometry index (packetLen ▸ advice) endFit
  have alloc := h.allocation
  have cap := h.capacity
  rw [arena] at alloc cap
  have kept := ReaderKept.after_finish A packet.entry.length bits l h.raw (par+Fintype.card J) (T+1) 0 subt pub mac pre h.bank
    boot selected.val.2.2 postCells h.selected h.earlier h.operands claims h.prepare protect alloc z.property frame advice
    index geometry cap before
  have dimEq : l.dim=par+Fintype.card J := by rw [Layout.dim,pdim,←gdim]
  exact reader.returnedClaimTicks l A pdim gdim extension W star ext row col f off copied pub mac hdr bank boot
    z.val.2.2 selected tape h z rfl loaded op frame room.1 stride total width fits sep kept room.2.1 room.2.2.1
    room.2.2.2 endFit (by rw [arena,Layout.tallyBits,dimEq,teams]) ret

end Diagonal

end BorderVNP
end Computability
end OAI
