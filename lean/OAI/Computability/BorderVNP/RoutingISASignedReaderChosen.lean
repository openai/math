import OAI.Computability.BorderVNP.RoutingISASignedReaderFinish
import OAI.Computability.BorderVNP.DiagonalTypedTallyReader

/-! # The chosen lead team's typed chart entry on a genuine signed prefix -/

namespace OAI
namespace Computability
namespace BorderVNP

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

/-- Build the typed chart receipt on the lead team's actual chosen finish,
starting at its real boot, its real pin choice and its checked operand rows.
Only the column sums are identified with the mathematical path tally: a
routing assignment can change which team carries an individual power bit. -/
noncomputable def readerImageOfPacketFinish {dim b h C z n sites t link inner length B : ℕ}
    {id : TableEntry dim b h C z → ℕ} {gen : Fragment IO} {Edge : Type}
    (S : PositiveTeam id gen n w) (p : S.Prefix) (ok : S.tallyReturns p)
    (l : SignedTaskArena.Layout) (A : StartupArena) (pdim : l.p.parameters=par)
    (gdim : Fintype.card J=l.p.report.gadgets) (teams : l.cube.teams=T+1)
    (raw subt : ℕ) (extension : Fin 81 → Word w) (W : Wiring T sites t bits link inner length Edge)
    (star : ℕ) (ext : Exterior T sites link → Bool) (row col : Fin bits → Bool)
    (f : BroadcastFrame) (off copied : ℕ) (hdr : List Bool)
    (os : List Operand) (rows : Fin (T+1) → Fin (par+Fintype.card J) → ℕ)
    (bank : Bank w) (selected : Memory w) (es : List (TeamRAM.Event w))
    (tally : Tally (Fin (T+1)) (Fin par) J B) :
    let u := Fintype.card query
    let v := Fintype.card guess
    let start := l.entry w u v reader.gates
    let packet := reader.nativePacket (l.valuation w) start A.ibase A.hbase l.tallyBits extension
    let pins := W.pinLayout 0 A.ibase A.hbase star
    let mac := install gen n S.routines
    let ar := l.after.arenaFor os.length raw (par+Fintype.card J) (T+1) 0 subt
    BootHeaderState (W.processorFields 0 col ext A.ibase A.hbase star) f ⟨off,copied,A.dense⟩
      packet S.pub hdr S.bank S.memory →
    (S.pins p.1).val.1.flatMap TeamRAM.Event.choices=List.ofFn row →
    S.pub 20=word w start → (S.pub 0).val=A.frame →
    pins.stride<2^w → sites*(W.program.length+t)<2^w → bits ≤ sites*(W.program.length+t) →
    Pins.LoopFits w pins → Pins.Separated pins →
    A.next ≤ l.cube.header.header → bits ≤ A.count → packet.entry.length*w ≤ A.copied →
    l.endAddress w u v reader.gates < 2^w → os.length ≤ l.after.bound.operands →
    ReaderKept A packet.entry.length bits S.memory (S.pins p.1).val.2.2 p.2.val.2.2 →
    Runs S.pub mac (.seq DiagonalTallyPacketEmit.producePacketIDs DiagonalTallyCubeSuffix.appendCubeOperands)
      (cellBank S.pub mac p.2.val.2.1 p.2.val.2.2) p.2.val.2.2 es bank selected →
    (∀ a < l.after.start, a ≠ (S.pub 0).val+35 → selected a=p.2.val.2.2 a) →
    DiagonalTallyRAM.AlignedAllocationInput ar S.pub selected os (DiagonalTallyRAM.broadcast subt rows) l.after.descriptors →
    (∀ c, ar.localRow os c.val=rows 0 c) →
    (∀ i c,rows i c<2^subt) → (∀ c, ∑ i,rows i c<2^w) →
    (∀ c, (∑ i,rows i c)=∑ i, DiagonalTallyRAM.tallyRow (tally.numberScalars (Fintype.equivFin J)) i c) →
    ReaderImage reader S.pub (S.finish p ok).val.2.2 row col tally.exponents (fun x ↦ ∑ a : Fin (T+1),tally.counts a x) := by
  intro u v start packet pins mac ar loaded tape operand frame stride extent width loop separate
    geometry index advice endFit cap before prepared keep input counts small total columns
  have pk : packet.entry.length = 6+3*reader.gates+u := payload_length ..
  have room := l.reader_room A geometry index (pk ▸ advice) endFit
  have dimEq : l.dim=par+Fintype.card J := by rw [SignedTaskArena.Layout.dim,pdim,gdim]
  obtain ⟨retained,sums⟩ := S.reader_finish p ok l A packet.entry.length bits raw _ _ 0 subt os rows
    bank selected es dimEq teams prepared keep input counts small total frame advice index geometry cap before
  apply readerImageOfTypedPacketTally reader l A pdim gdim extension W star ext row col f off copied S.pub mac
    hdr S.bank S.memory (S.finish p ok).val.2.2 (S.pins p.1) tape tally loaded operand frame room.1
    stride extent width loop separate retained room.2.1 room.2.2.1 room.2.2.2 endFit
  intro c j hj
  rw [←columns]
  exact sums c j hj

/-- Specialization to the basic signed task extension. -/
noncomputable abbrev readerImageOfFinish {dim b h C z n sites t link inner length B : ℕ}
    {id : TableEntry dim b h C z → ℕ} {gen : Fragment IO} {Edge : Type}
    (S : PositiveTeam id gen n w) (p : S.Prefix) (ok : S.tallyReturns p)
    (l : SignedTaskArena.Layout) (A : StartupArena) (pdim : l.p.parameters=par)
    (gdim : Fintype.card J=l.p.report.gadgets) (teams : l.cube.teams=T+1)
    (raw subt : ℕ) (old : Fin 81 → Word w) :=
  readerImageOfPacketFinish (sites := sites) (t := t) (link := link) (inner := inner) (length := length)
    (B := B) (Edge := Edge) reader S p ok l A pdim gdim teams raw subt (l.extension raw 0 subt old)

end Diagonal

end BorderVNP
end Computability
end OAI
