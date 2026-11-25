import OAI.Computability.BorderVNP.RoutingISASignedReaderChosen
import OAI.Computability.BorderVNP.DiagonalCanonicalFinishImage

/-! # Reading the actual signed finish on supported paths -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.PositiveTeam

open VPVNP.BurstRAM CompactMachine CellMacro.Generator BorderVNP.Cube SignedTaskArena
open TeamContraction TeamContraction.ProcessorSlots JointHeader.PositiveFields

variable {axes b h K s n w : ℕ} {id : TableEntry axes b h K s → ℕ} {gen : Fragment IO}
    (S : PositiveTeam id gen n w) (prep : S.Prefix) (ok : S.tallyReturns prep)
    (l : SignedTaskArena.Layout) (A : StartupArena)
    {T dim width : ℕ} {team : Fin T} {rows : Fin T → Fin dim → ℕ} {xs : List (List Bool)}
local notation "mac" => install gen n S.routines
local notation3 (prettyPrint := false) "before" => prep.2.val.2.2
local notation3 (prettyPrint := false) "regs" => cellBank S.pub mac prep.2.val.2.1 before

/-- On any locally successful suffix, the selected operands and aligned
allocation suffice to preserve the physical reader bank. The transmitted
subtotal bits may be arbitrary at every other team. -/
theorem readerKeptOfReceipt (receipt : FinishInput team rows width S.pub mac regs before xs)
    (post : receipt.post=l.after)
    (selected : ∀ k<l.after.start, k≠(S.pub 0).val+35 → receipt.selected k=before k)
    {entries pins : ℕ} (frame : (S.pub 0).val=A.frame) (packet : entries*w ≤ A.copied)
    (index : pins ≤ A.count) (placement : A.next ≤ l.cube.header.header)
    (kept : ReaderKept A entries pins S.memory (S.pins prep.1).val.2.2 before) :
    ReaderKept A entries pins S.memory (S.pins prep.1).val.2.2 (S.finish prep ok).val.2.2 := by
  have alloc := receipt.allocation
  have room := receipt.capacity
  rw [post] at alloc room
  exact ReaderKept.after_finish A entries pins l receipt.raw dim T team.val width S.pub mac regs receipt.bank
    S.memory (S.pins prep.1).val.2.2 before receipt.selected receipt.earlier receipt.operands xs
    receipt.prepare selected alloc (S.finish prep ok).property frame packet index placement room kept

/-- The final branch instruction consults the same team number as the
checked private-call directory. Other teams require no pin or reader
certificate for this test. -/
theorem teamOfFinishReceipt (receipt : FinishInput team rows width S.pub mac regs before xs)
    (post : receipt.post=l.after)
    (selected : ∀ k<l.after.start, k≠(S.pub 0).val+35 → receipt.selected k=before k)
    (frame : (S.pub 0).val=A.frame) (placement : A.next ≤ l.cube.header.header)
    (teamAt : (CellDispatch.Frame.ofMemory S.pub before).team=team.val) :
    ((S.finish prep ok).val.2.2 (S.pub 0).val).val=team.val := by
  have alloc := receipt.allocation
  have room := receipt.capacity
  rw [post] at alloc room
  have reflKeep : ReaderKept A 0 0 before before before := ⟨fun _ _ => rfl,fun _ _ => rfl,
    fun _ _ => rfl,fun _ _ => rfl⟩
  have keep := ReaderKept.after_finish A 0 0 l receipt.raw dim T team.val width S.pub mac regs receipt.bank
    before before before receipt.selected receipt.earlier receipt.operands xs receipt.prepare selected alloc
    (S.finish prep ok).property frame (by simp) (Nat.zero_le _) placement room reflKeep
  have same := keep.control 0 (by decide)
  rw [Nat.add_zero,←frame] at same
  exact (congrArg Fin.val same).trans teamAt

end RoutingISA.Evaluator.PositiveTeam

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier
open DiagonalResidueRAM ResidueRates VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena
open TeamContraction TeamContraction.ProcessorSlots TeamContraction.JointHeader
open RoutingISA.Evaluator CompactMachine CellMacro.Generator BorderVNP.Cube DiagonalTallyMaterialize
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

/-- The lead reader receives the signed mathematical path's operands and
counts from the actual completed physical ledger and the copied chart packet.
The decoders address the bank written by this very suffix. -/
noncomputable def readerImageOfReceipt {dim b h C z n sites t link inner length B : ℕ}
    {id : TableEntry dim b h C z → ℕ} {gen : Fragment IO} {Edge : Type}
    (S : PositiveTeam id gen n w) (p : S.Prefix) (ok : S.tallyReturns p)
    (l : SignedTaskArena.Layout) (A : StartupArena) (pdim : l.p.parameters=par)
    (gdim : Fintype.card J=l.p.report.gadgets) (teams : l.cube.teams=T+1)
    {reserve axes groups cap subt : ℕ} (fields : PositiveFields reserve axes groups cap (T+1) (par+Fintype.card J) subt)
    (rows : Fin (T+1) → Fin (par+Fintype.card J) → ℕ)
    (receipt : PositiveFields.FinishInput (0 : Fin (T+1)) rows subt S.pub (install gen n S.routines)
      (cellBank S.pub (install gen n S.routines) p.2.val.2.1 p.2.val.2.2) p.2.val.2.2 fields.tallyWords)
    (post : receipt.post=l.after)
    (saved : ∀ k<l.after.start, k≠(S.pub 0).val+35 → receipt.selected k=p.2.val.2.2 k)
    (extension : Fin 81 → Word w) (W : Wiring T sites t bits link inner length Edge)
    (star : ℕ) (ext : Exterior T sites link → Bool) (row col : Fin bits → Bool)
    (f : BroadcastFrame) (off copied : ℕ) (hdr : List Bool)
    (tally : Tally (Fin (T+1)) (Fin par) J B) :
    let u := Fintype.card query
    let v := Fintype.card guess
    let start := l.entry w u v reader.gates
    let packet := reader.nativePacket (l.valuation w) start A.ibase A.hbase l.tallyBits extension
    let pins := W.pinLayout 0 A.ibase A.hbase star
    BootHeaderState (W.processorFields 0 col ext A.ibase A.hbase star) f ⟨off,copied,A.dense⟩
      packet S.pub hdr S.bank S.memory →
    (S.pins p.1).val.1.flatMap TeamRAM.Event.choices=List.ofFn row →
    S.pub 20=word w start → (S.pub 0).val=A.frame →
    pins.stride<2^w → sites*(W.program.length+t)<2^w → bits ≤ sites*(W.program.length+t) →
    Pins.LoopFits w pins → Pins.Separated pins →
    A.next ≤ l.cube.header.header → bits ≤ A.count → packet.entry.length*w ≤ A.copied →
    l.endAddress w u v reader.gates < 2^w →
    ReaderKept A packet.entry.length bits S.memory (S.pins p.1).val.2.2 p.2.val.2.2 →
    fields.subtotals=PositiveFields.canonicalSubtotals subt rows →
    (∀ i c, rows i c<2^subt) → (∀ c, ∑ i,rows i c<2^w) →
    (∀ c, (∑ i,rows i c)=∑ i, DiagonalTallyRAM.tallyRow (tally.numberScalars (Fintype.equivFin J)) i c) →
    ReaderImage reader S.pub (S.finish p ok).val.2.2 row col tally.exponents (fun x ↦ ∑ a : Fin (T+1), tally.counts a x) := by
  intro u v start packet pins boot tape op frame stride extent total fit sep placed index advice endFit keep canonical small sumFit columns
  have claims : fields.tallyWords = DiagonalTallyRAM.broadcast subt rows := by
    change splitFields subt ((T+1)*(par+Fintype.card J)) (List.ofFn fields.subtotals)=_
    rw [canonical,PositiveFields.ofFn_canonicalSubtotals,splitFields_broadcast]
  have alloc := receipt.allocation
  have counts := receipt.counts
  have capacity := receipt.capacity
  rw [post] at alloc
  have aligned := (congrArg (fun fields₀ : List (List Bool) =>
    DiagonalTallyRAM.AlignedAllocationInput (l.after.arenaFor receipt.operands.length receipt.raw
      (par+Fintype.card J) (T+1) 0 subt) S.pub receipt.selected receipt.operands fields₀ l.after.descriptors) claims).mp alloc
  rw [post] at counts capacity
  exact readerImageOfPacketFinish reader S p ok l A pdim gdim teams receipt.raw subt extension W star ext row col f off copied
    hdr receipt.operands rows receipt.bank receipt.selected receipt.earlier tally boot tape op frame stride extent total fit sep
    placed index advice endFit capacity keep receipt.prepare saved aligned counts small sumFit columns

end Diagonal

end BorderVNP
end Computability
end OAI
