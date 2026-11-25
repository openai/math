import OAI.Computability.BorderVNP.DiagonalNativeChosenEntry
import OAI.Computability.BorderVNP.DiagonalNativeSignedWindow

/-! # The true lead-reader clock on the selected Fourier chart -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput ResidueIndex ResidueFourier
open DiagonalResidueRAM ResidueRates VPVNP VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator
open scoped Classical BigOperators
variable {K : Type*} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity K D m}
variable {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
variable {R : CommonField G aux q k s ord} {chart : AdvisedBranch R}
variable [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E] {teams r multBits tally W pin : ℕ}
local notation "h" => pairedTableParameters (k+1) s
local notation "query" => Board.Physical h pin tally (G.Entry ⊕ ι)
local notation "guess" reader => Guess (Fin h) (ChosenReader.gridRank reader) (Nat.clog 2 R.p+1) (Nat.clog 2 R.p)

/-- Actual gate, word, query and binary-guess counts bound both native staging and the subsequent
matrix reader. The charged team-number guard costs six more ordinary instructions. -/
theorem ChosenReader.stagedTicks_le (reader : ChosenReader chart teams r multBits tally W pin) :
    prepareTicks (Fintype.card query) reader.gates W + ticks reader.gates (Fintype.card (guess reader)) ≤ reader.charge := by
  let x : ReaderSizes := ⟨h,adviceGateBudget (2*(k+1)) k s,Fintype.card (G.Entry ⊕ ι),multBits,pin,tally,
    Module.finrank (ZMod R.p) chart.E,reader.gridRank,W,R.p,R.p^reader.power,chart.pinRadius teams r,
    (R.p^reader.power-1)*chart.degreeSum,reader.gridCard⟩
  have hp : Fintype.card query = x.publicBits := by simp [Board.Physical,ReaderSizes.publicBits,x]
  have hg : Fintype.card (guess reader) = x.guessBits := by
    simp [ReaderSizes.guessBits,ResidueEntryBudget.guessWidth,x]
  let B := x.publicBits + x.guessBits + reader.gates + W
  have ht := staged_ticks_le (B := B) (u := Fintype.card query) (v := Fintype.card (guess reader))
    (k := reader.gates) (w := W) (by dsimp [B]; omega) (by dsimp [B]; omega)
    (by dsimp [B]; omega) (by dsimp [B]; omega)
  change _ ≤ x.stagedCharge reader.gates
  apply ht.trans
  dsimp only [ReaderSizes.stagedCharge,B]
  change _ ≤ _ + 128*(x.publicBits+x.guessBits+reader.gates+W+1)^2
  omega

/-- All returning true lead-reader traces fit this chart's advertised reader charge. For a
nonlead team only the guard runs. On the lead team the circuit and every query word are read
from the delivered packet, pin and serialized exponent addresses. -/
theorem ChosenReader.leadTicks_le (reader : ChosenReader chart teams r multBits tally W pin)
    (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (bank : Bank W) (mem : Memory W)
    (base start dense row col totals : ℕ) (extension : Fin 81 → Word W)
    (fit : mem (pub 0).val = 0 →
      DiagonalResidueRAM.Layout base start dense (sourceAddress row col totals ∘ (Fintype.equivFin query).symm)
        (Fintype.card (guess reader)) reader.gates W ∧
      (pub 0).val+30 < 2^W ∧ packFrame pub mem dense start (6+3*reader.gates+Fintype.card query) ∧
      DiagonalTallyBits.WordsAt mem dense ((reader.nativePacket base start row col totals extension).entry.map wordBits) ∧
      ∃ x : Fin (Fintype.card query) → Bool, ∀ i,
        mem (sourceAddress row col totals ((Fintype.equivFin query).symm i)) = wordBit W (x i))
    (z : Returns leadEntry pub mac bank mem) : traceCost z.val.1 ≤ 7+reader.charge := by
  by_cases team : mem (pub 0).val = 0
  · obtain ⟨layout,room,frame,payload,x,values⟩ := fit team
    let circuit := typedCircuit query (guess reader) reader.circuit
    obtain ⟨_,_,_,cost,_⟩ := lead_zero_ticks pub mac bank mem base start dense
      (sourceAddress row col totals ∘ (Fintype.equivFin query).symm) circuit x layout room frame payload values team z.property
    rw [cost]
    have ht := reader.stagedTicks_le
    omega
  · have ht := (lead_other_ticks team z.property).1
    omega

end Diagonal

end BorderVNP
end Computability
end OAI
