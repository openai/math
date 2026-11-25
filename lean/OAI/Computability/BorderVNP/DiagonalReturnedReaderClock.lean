import OAI.Computability.BorderVNP.RoutingISASignedReaderSources
import OAI.Computability.BorderVNP.RoutingISASignedReaderKeep
import OAI.Computability.BorderVNP.DiagonalJointReaderValue
import OAI.Computability.BorderVNP.DiagonalReturnedClaimClock
import OAI.Computability.BorderVNP.DiagonalNativeReaderClock

/-! # Native reader time on a lead-team return with arbitrary other claims -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier
open DiagonalResidueRAM ResidueRates VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena RoutingISA.Evaluator
open TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader
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

/-- Charge the true immutable gate table on the memory of any returning signed
finish. The lead pin run supplies the row and column bits, and the returned
allocator supplies the possibly wrapped words from the other teams' claims. -/
theorem ChosenReader.returnedClaimTicks {sites t link inner length : ℕ} {Edge : Type}
    (l : SignedTaskArena.Layout) (A : StartupArena) (pdim : l.p.parameters=par)
    (gdim : Fintype.card J=l.p.report.gadgets) (extension : Fin 81 → Word w)
    (W : Wiring T sites t bits link inner length Edge) (star : ℕ) (ext : Exterior T sites link → Bool)
    (row col : Fin bits → Bool) (f : BroadcastFrame) (off copied : ℕ) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (hdr : List Bool) (bank : Bank w) {loadedBank : Bank w} (boot out : Memory w)
    (selected : Pins.Return pub mac bank boot) (tape : selected.val.1.flatMap TeamRAM.Event.choices=List.ofFn row)
    {startBank : Bank w} {startMem : Memory w} {claim : List (List Bool)} {claimWidth : ℕ}
    {rows : Fin (T+1) → Fin (par+Fintype.card J) → ℕ}
    (receipt : PositiveFields.FinishInput 0 rows claimWidth pub mac startBank startMem claim)
    (finish : Returns (Evaluator.finishExpansion Evaluator.signedOccurrences) pub mac startBank startMem)
    (bankOut : finish.val.2.2=out) :

    let u := Fintype.card query
    let v := Fintype.card guess
    let start := l.entry w u v reader.gates
    let packet := reader.nativePacket (l.valuation w) start A.ibase A.hbase l.tallyBits extension
    let source := W.processorFields 0 col ext A.ibase A.hbase star
    let pins := W.pinLayout 0 A.ibase A.hbase star
    BootHeaderState source f ⟨off,copied,A.dense⟩ packet pub hdr loadedBank boot →
    pub 20=word w start → (pub 0).val=A.frame → A.frame+30<2^w →
    pins.stride<2^w → sites*(W.program.length+t)<2^w → bits ≤ sites*(W.program.length+t) →
    Pins.LoopFits w pins → Pins.Separated pins →
    ReaderKept A packet.entry.length bits boot selected.val.2.2 out →
    A.ibase+bits ≤ l.tallyBits → A.hbase+bits ≤ l.tallyBits →
    A.dense+(6+3*reader.gates+u)*w ≤ l.tallyBits → l.endAddress w u v reader.gates < 2^w →
    receipt.post.localBase+(par+Fintype.card J)+(T+1)*(par+Fintype.card J)+(par+Fintype.card J)+(par+Fintype.card J)+1=l.tallyBits →
    ∀ next : Returns Evaluator.leadEntry pub mac finish.val.2.1 out, traceCost next.val.1 ≤ 7+reader.charge := by
  intro u v start packet source pins loaded op frame fr stride total room fits sep kept rowRoom colRoom denseRoom endRoom output next
  have pklen : packet.entry.length = 6+3*reader.gates+u := payload_length ..
  have small : readings pub 0+24<2^w := by change (pub 0).val+24<2^w; omega
  have pinSource := SignedTaskArena.lead_pin_words W col row ext A.ibase A.hbase star pub mac boot bank
    loaded.input loaded.frame.pins small stride total room fits sep selected tape
  have control := SignedTaskArena.reader_packet_after loaded op
    (fun k hk ↦ frame ▸ kept.control k (List.mem_cons_of_mem 0 hk)) (fun j hj ↦ kept.dense j hj)
  have addr := l.reader_layout (w:=w) (pin:=pin) (row:=A.ibase) (col:=A.hbase) (dense:=A.dense)
    (v:=v) (k:=reader.gates) gdim (by simpa only [pdim] using rowRoom) (by simpa only [pdim] using colRoom)
  rw [pdim] at addr
  apply reader.leadTicks_le pub mac finish.val.2.1 out (l.valuation w) start A.dense A.ibase A.hbase l.tallyBits
    extension _ next
  intro _
  refine ⟨addr denseRoom endRoom,frame ▸ fr,pklen ▸ control.1,control.2,?_⟩
  let a := receipt.post.arenaFor receipt.operands.length receipt.raw (par+Fintype.card J) (T+1) (0 : Fin (T+1)).val claimWidth
  let value (c : Fin (par+Fintype.card J)) := (∑ i : Fin (T+1), DiagonalTallyRAM.claimWord (w:=w) a.frame claim i.val c.val).val
  let power (i : Fin par) := value (Fin.castAdd (Fintype.card J) i)
  let gadget (g : J) := value (Fin.natAdd par (Fintype.equivFin J g))
  refine ⟨_,sourceAddress_value out A.ibase A.hbase l.tallyBits row col power gadget
    (fun j => (kept.row j.val j.isLt).trans (pinSource.1 j)) (fun j => (kept.col j.val j.isLt).trans (pinSource.2 j)) ?_ ?_⟩
  · intro i j
    have bit := (receipt.returned finish).2 (Fin.castAdd (Fintype.card J) i) j.val j.isLt
    rw [output,bankOut] at bit
    simpa only [power,value,a,Fin.val_zero,Fin.val_castAdd,Nat.add_assoc,word,wordBit] using bit
  · intro g j
    have bit := (receipt.returned finish).2 (Fin.natAdd par (Fintype.equivFin J g)) j.val j.isLt
    rw [output,bankOut] at bit
    simpa only [gadget,value,a,Fin.val_zero,Fin.val_natAdd,Nat.add_assoc,word,wordBit] using bit

end Diagonal

end BorderVNP
end Computability
end OAI
