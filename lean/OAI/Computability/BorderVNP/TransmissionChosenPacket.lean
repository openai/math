import OAI.Computability.BorderVNP.DiagonalStretchAssembly
import OAI.Computability.BorderVNP.TransmissionJointRate
import OAI.Computability.BorderVNP.TransmissionJointProgram

/-! # Deploying the chosen curve's reader and distinguished index in the actual literals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResidueBox ResiduePins ResidueEntryInput
open DiagonalResidueRAM ResidueRates VPVNP VPVNP.BurstRAM TeamContraction.ProcessorSlots Filter
open scoped Classical BigOperators

variable {K : Type*} [Field K] {D m : ℕ} {ι : Type} [Fintype ι] {G : PaidIdentity K D m}
variable {aux : ι → K} {q k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
variable {R : CommonField G aux q k s ord} {chart : AdvisedBranch R}
variable [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E] {teams r multBits tally W pin : ℕ}

local notation "h" => pairedTableParameters (k+1) s
local notation "query" => Board.Physical h pin tally (G.Entry ⊕ ι)
local notation "guess" reader => Guess (Fin h) (ChosenReader.gridRank reader) (Nat.clog 2 R.p+1) (Nat.clog 2 R.p)

/-- The concrete row pin, live pin and subtotal address operands of the chosen board.
The literal contains the actual board program and the padding-safe binary encoding
of the distinguished index on the same curve and finite ground field. -/
noncomputable def ChosenReader.nativePacket (reader : ChosenReader chart teams r multBits tally W pin)
    (base entry row col totals : ℕ) (extension : Fin 81 → Word W) : ReferencePacket W ((h+2)*pin) :=
  ReferencePacket.ofCircuit base entry (typedCircuit query (guess reader) reader.circuit)
    (sourceAddress row col totals ∘ (Fintype.equivFin query).symm) extension
    ((boxPinCodec h reader.rankFits reader.boxFits).encode reader.star)

/-- The full advised reference index in the literal is independent of the live pin. -/
theorem ChosenReader.nativePacket_reference (reader : ChosenReader chart teams r multBits tally W pin)
    (base entry row col totals : ℕ) (extension : Fin 81 → Word W) :
    (reader.nativePacket base entry row col totals extension).reference =
      (boxPinCodec h reader.rankFits reader.boxFits).encode reader.star := rfl

/-- The scalar entry region is exactly the payload required by the chosen reader's
physical execution theorem, at the actual row, column and tally source addresses. -/
theorem ChosenReader.nativePacket_entry (reader : ChosenReader chart teams r multBits tally W pin)
    (base entry row col totals : ℕ) (extension : Fin 81 → Word W) :
    (reader.nativePacket base entry row col totals extension).entry =
      payload W base entry (typedCircuit query (guess reader) reader.circuit)
        (sourceAddress row col totals ∘ (Fintype.equivFin query).symm) := rfl

private theorem circuitBudget {g pubbits v : ℕ} (x : ReaderSizes) (hpub : pubbits = x.publicBits)
    (teams base entry : ℕ) (c : BooleanTranscript.Circuit (Fin pubbits ⊕ Fin v) g)
    (src : Fin pubbits → ℕ) (extension : Fin 81 → Word x.word) (star : Fin ((x.h+2)*x.pin) → Bool) :
    let p := ReferencePacket.ofCircuit base entry c src extension star
    p.bits.length+jointBudget p.bits.length x.word+x.stagedCharge g+subtotalPrefix teams x ≤
      10000*(teams+1)*(x.stagedCharge g+1)^2 := by
  subst pubbits
  exact ReferencePacket.staged_budget teams x base entry c src extension star

/-- The charge covers precisely the selected program, complete reference packet,
native startup, and the augmented common-prefix claim bits. -/
theorem ChosenReader.nativePacket_budget (reader : ChosenReader chart teams r multBits tally W pin)
    (base entry row col totals : ℕ) (extension : Fin 81 → Word W) :
    let p := reader.nativePacket base entry row col totals extension
    p.bits.length+jointBudget p.bits.length W+reader.charge+1+teams*((h+Fintype.card (G.Entry ⊕ ι))*tally) ≤
      10000*(teams+1)*(reader.charge+1)^2 := by
  let pow := R.p^reader.power
  let x : ReaderSizes := ⟨h,adviceGateBudget (2*(k+1)) k s,Fintype.card (G.Entry ⊕ ι),
    multBits,pin,tally,Module.finrank (ZMod R.p) chart.E,reader.gridRank,W,R.p,pow,
    chart.pinRadius teams r,(pow-1)*chart.degreeSum,reader.gridCard⟩
  have hpub : Fintype.card query = x.publicBits := by simp [Board.Physical,ReaderSizes.publicBits,x]
  have ht := circuitBudget x hpub teams base entry (typedCircuit query (guess reader) reader.circuit)
    (sourceAddress row col totals ∘ (Fintype.equivFin query).symm) extension
    ((boxPinCodec h reader.rankFits reader.boxFits).encode reader.star)
  intro p
  change p.bits.length+jointBudget p.bits.length W+reader.charge+
    (1+teams*((h+Fintype.card (G.Entry ⊕ ι))*tally)) ≤ 10000*(teams+1)*(reader.charge+1)^2 at ht
  omega

/-- The exact uniform quantifier order of the stretch schedule: for each fixed
polynomial chart bound and stage constants there is one threshold before the choice
of chart, field, selected reader, scalar operands, or extension values. -/
theorem StretchSchedule.eventually_nativePackets (S : StretchSchedule) (f : ℕ → ℕ)
    (hf : PolynomiallyBounded f) (A C factor : ℕ) :
    ∀ᶠ n : ℕ in atTop, let batch := stretch S.ρ n
      let T := f (adviceScale S.σ S.ρ n)
      ∀ {k s : ℕ} {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))}
        {R : CommonField G aux q k s ord} (chart : AdvisedBranch R) [Fact R.p.Prime] [Algebra (ZMod R.p) chart.E]
        (reader : ChosenReader chart (S.teamsPred n+1) batch (S.multBits n) (S.tally n) (S.word n) (T+6)),
        reader.charge ≤ A*(T+1)^C → ∀ (base entry row col totals : ℕ) (extension : Fin 81 → Word (S.word n)),
        let packet := reader.nativePacket base entry row col totals extension
        factor*(packet.bits.length+jointBudget packet.bits.length (S.word n)+reader.charge+1+
          (S.teamsPred n+1)*((pairedTableParameters (k+1) s+Fintype.card (G.Entry ⊕ ι))*(S.tally n))) < batch := by
  obtain ⟨a,b,teamsFit⟩ := S.resources
  let H (M : ℕ) := a*(M+1)^b
  let J (M : ℕ) := A*(f M+1)^C
  let cost (M : ℕ) := factor*(10000*(H M+1)*(J M+1)^2)
  have hh : PolynomiallyBounded H := (PolynomiallyBounded.const a).mul ((PolynomiallyBounded.id.add (.const 1)).pow b)
  have hj : PolynomiallyBounded J := (PolynomiallyBounded.const A).mul ((hf.add (.const 1)).pow C)
  have hcost : PolynomiallyBounded cost := (PolynomiallyBounded.const factor).mul
    (((PolynomiallyBounded.const 10000).mul (hh.add (.const 1))).mul ((hj.add (.const 1)).pow 2))
  obtain ⟨L,e,glob⟩ := hcost.exists_global_bound
  filter_upwards [teamsFit,advice_polynomial_lt_batch S.positive S.separated (L*2^e) e,eventually_ge_atTop 1] with n teamBound room hn
  intro batch T k s ord R chart _ _ reader charge base entry row col totals extension packet
  let M := adviceScale S.σ S.ρ n
  have hM : 1 ≤ M := by dsimp only [M,adviceScale]; omega
  have hTeam : S.teamsPred n+1 ≤ H M := by dsimp only [H,M]; omega
  have hCharge : reader.charge ≤ J M := charge
  have bound := reader.nativePacket_budget base entry row col totals extension
  calc
    _ ≤ factor*(10000*(S.teamsPred n+1+1)*(reader.charge+1)^2) := Nat.mul_le_mul_left _ bound
    _ ≤ cost M := by dsimp only [cost]; gcongr
    _ ≤ L*(M+1)^e := glob M
    _ ≤ L*(2*M)^e := by gcongr; omega
    _ = (L*2^e)*M^e := by rw [mul_pow,Nat.mul_assoc]
    _ < _ := room

end Diagonal

end BorderVNP
end Computability
end OAI
