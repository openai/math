import OAI.Computability.BorderVNP.RoutingISASignedReaderImage
import OAI.Computability.BorderVNP.CubePhysicalNumberedRows

/-! # Exact readback of the scalar coordinates in the typed path assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier
open DiagonalResidueRAM ResidueRates VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.SignedTaskArena
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

/-- The actual gate reader sees the typed scalar multiplicities after the
physical serializer has written the dense coordinate array. Its indexing
uses the same scalar enumeration for shortening and cube entries. -/
noncomputable def readerImageOfTypedPacketTally {sites t link inner length B : ℕ} {Edge : Type}
    (l : SignedTaskArena.Layout) (A : StartupArena) (pdim : l.p.parameters=par)
    (gdim : Fintype.card J=l.p.report.gadgets) (extension : Fin 81 → Word w)
    (W : Wiring T sites t bits link inner length Edge) (star : ℕ) (ext : Exterior T sites link → Bool)
    (row col : Fin bits → Bool) (f : BroadcastFrame) (off copied : ℕ) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (hdr : List Bool) (bank : Bank w) (boot out : Memory w)
    (selected : Pins.Return pub mac bank boot) (tape : selected.val.1.flatMap TeamRAM.Event.choices=List.ofFn row)
    (tally : Tally (Fin (T+1)) (Fin par) J B) :
    let u := Fintype.card query
    let v := Fintype.card guess
    let start := l.entry w u v reader.gates
    let packet := reader.nativePacket (l.valuation w) start A.ibase A.hbase l.tallyBits extension
    let source := W.processorFields 0 col ext A.ibase A.hbase star
    let pins := W.pinLayout 0 A.ibase A.hbase star
    BootHeaderState source f ⟨off,copied,A.dense⟩ packet pub hdr bank boot →
    pub 20=word w start → (pub 0).val=A.frame → A.frame+30<2^w →
    pins.stride<2^w → sites*(W.program.length+t)<2^w → bits ≤ sites*(W.program.length+t) →
    Pins.LoopFits w pins → Pins.Separated pins →
    ReaderKept A packet.entry.length bits boot selected.val.2.2 out →
    A.ibase+bits ≤ l.tallyBits → A.hbase+bits ≤ l.tallyBits →
    A.dense+(6+3*reader.gates+u)*w ≤ l.tallyBits → l.endAddress w u v reader.gates < 2^w →
    (∀ c : Fin (par+Fintype.card J), ∀ j<w,
      out (l.tallyBits+(c.val*w+j)) = word w (((∑ a : Fin (T+1),DiagonalTallyRAM.tallyRow (tally.numberScalars (Fintype.equivFin J)) a c).testBit j).toNat)) →
      ReaderImage reader pub out row col tally.exponents (fun x ↦ ∑ a : Fin (T+1),tally.counts a x) := by
  intro u v start packet source pins loaded op frame fr stride total room fits sep kept rowRoom colRoom denseRoom endRoom sums
  let numeric := tally.numberScalars (Fintype.equivFin J)
  have image := readerImageOfPacketTally reader l A pdim gdim extension W star ext row col f off copied pub
    mac hdr bank boot out selected tape numeric loaded op frame fr stride total room fits sep kept
    rowRoom colRoom denseRoom endRoom sums
  have counts : (fun x : J => ∑ i : Fin (T+1), numeric.counts i (Fintype.equivFin J x)) =
      fun x => ∑ i : Fin (T+1), tally.counts i x := by
    funext x
    simp only [numeric, Tally.numberScalars, Equiv.symm_apply_apply]
  rw [counts] at image
  exact image

/-- Specialization to the basic signed task extension. -/
noncomputable abbrev readerImageOfTypedTally {sites t link inner length B : ℕ} {Edge : Type}
    (l : SignedTaskArena.Layout) (A : StartupArena) (pdim : l.p.parameters=par)
    (gdim : Fintype.card J=l.p.report.gadgets) (raw team subt : ℕ) (old : Fin 81 → Word w) :=
  readerImageOfTypedPacketTally (sites := sites) (t := t) (link := link) (inner := inner) (length := length)
    (B := B) (Edge := Edge) reader l A pdim gdim (l.extension raw team subt old)

end Diagonal

end BorderVNP
end Computability
end OAI
