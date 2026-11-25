import OAI.Computability.BorderVNP.DiagonalReaderInputs
import OAI.Computability.BorderVNP.ResidueStagedRates
import OAI.Computability.BorderVNP.ResidueGeometricReader

/-! # The same residue pin and native reader at a selected signed branch

The word program, Frobenius power and distinguished index precede the later
layout and its private term expansion. The scalar entries of the weighted
reader are exactly the chosen common shortening and cube entries.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal

open Branch Crossing MvPolynomial ResiduePins ResidueBox ResidueEntryInput
open DiagonalResidueRAM ResidueRates
open scoped Classical BigOperators

variable {K : Type*} [Field K] {D m : ℕ} {ι : Type} [Fintype ι]
variable {G : PaidIdentity K D m} {aux : ι → K} {q k s : ℕ}
variable {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {R : CommonField G aux q k s ord}

/-- The scalar read at a fixed shortening or cube table position in the chart field. -/
noncomputable def AdvisedBranch.gadgets (chart : AdvisedBranch R) : G.Entry ⊕ ι → chart.E :=
  algebraMap R.E₀ chart.E ∘ R.entry

variable {Pin Wire : Type} [Fintype Wire]

/-- For this distinguished index, the paper's unit-plus-column rule fails on
some live input of every exact path expansion of the substituted network. -/
def ColumnFailure {E : Type} [Field E] {p d : ℕ} [Fact p.Prime] [Algebra (ZMod p) E]
    (B : Module.Basis (Fin d) (ZMod p) E) (H Q : ℕ) (hQ : 0 < Q)
    (teams r k s : ℕ) (ord : Fin (k+1) × Bool ≃ Fin (2*(k+1)))
    (g : Fin (pairedTableParameters (k+1) s) → MvPolynomial (Option (Fin (pairedTableParameters (k+1) s))) E)
    (star : Index (Fin d) (Fin (pairedTableParameters (k+1) s)) H) : Prop :=
  let h := pairedTableParameters (k+1) s
  ∀ (layout : Fin teams × Fin r → Fin (k+1) → InputSlot Pin Wire)
    (encode : Index (Fin d) (Fin h) H → Pin → Bool) (Path : Index (Fin d) (Fin h) H → Type)
    [∀ i, Fintype (Path i)] (μ : ∀ i, Path i → Fin h →₀ ℕ) (a : ∀ i, Path i → E),
    (∀ i, numberedSubstituted E k s ord layout (encode i) =
      ∑ j, monomial (μ i j) (a i j)) →
    ∃ j, (signedContraction layout (encode j) : ZMod p) ≠
      (if j = star then 1 else 0) + ∑ i, ∑ l, entryWeight p B H Q hQ g (μ i l) i j (a i l)

/-- A small border circuit supplies the branch separately via `common_reader_inputs`.
Every such branch with the proved numerical ceilings supplies a charged physical
reader at the very pin and power that rule out the live column identity. -/
theorem staged_chart_data (G : PaidIdentity K D m) (aux : ι → K) :
    ∃ A C : ℕ, ∀ (Pin Wire : Type) [Fintype Wire] {q k s : ℕ}
      {ord : Fin (k+1) × Bool ≃ Fin (2*(k+1))} {R : CommonField G aux q k s ord}
      (chart : AdvisedBranch R) (teams r multBits tally word T : ℕ),
      ReaderInputs chart teams r multBits T → tally ≤ T → word ≤ T →
      letI : Fact R.p.Prime := ⟨R.prime⟩
      letI := Fintype.ofFinite chart.E
      letI : Algebra (ZMod R.p) chart.E := ZMod.algebra _ _
      let h := pairedTableParameters (k+1) s
      let L := batchDegree teams h r k
      let H := radius L chart.degreeSum
      let d := Module.finrank (ZMod R.p) chart.E
      let B := Module.finBasis (ZMod R.p) chart.E
      let g := signedEquations chart.E k s ord chart.advice
      let size := adviceGateBudget (2*(k+1)) k s
      ∃ (e : ℕ) (_ : 0 < e),
        let Q := R.p^e
        let hQ := pow_pos R.prime.pos e
        let width := (Q-1)*chart.degreeSum
        (∀ a : chart.E, a^Q = a) ∧
        ∃ (Ω : Index (Fin d) (Fin h) H → ZMod R.p) (star : Index (Fin d) (Fin h) H), Ω star ≠ 0 ∧
          ColumnFailure (Pin := Pin) (Wire := Wire) B H Q hQ teams r k s ord g star ∧
          ∃ (hd : d ≤ 2^(T+6)) (hH : 2*H < 2^(T+6)) (N d' gates : ℕ),
            let x : ReaderSizes := ⟨h,size,Fintype.card (G.Entry ⊕ ι),multBits,T+6,tally,d,d',word,
              R.p,Q,H,width,N⟩
            x.stagedCharge gates ≤ A*(T+1)^C ∧ ∃ circuit,
              StagedEntries (Guess (Fin h) d' (Nat.clog 2 R.p+1) (Nat.clog 2 R.p))
                B Q H hQ hd hH g chart.gadgets multBits tally (k := gates) circuit := by
  obtain ⟨A,C,reader⟩ := uniform_staged_reader.{0,0}
  refine ⟨A,C,?_⟩
  intro Pin Wire _ q k s ord R chart teams r multBits tally word T cap ht hw
  let : Fact R.p.Prime := ⟨R.prime⟩
  let := Fintype.ofFinite chart.E
  let : Algebra (ZMod R.p) chart.E := ZMod.algebra _ _
  intro h L H d B g size
  let := Fintype.ofFinite (DegreeMonomial (Fin (2*(k+1))) (k+1))
  have hn : 0 < h := parameterCount_pos (by omega) k s
  obtain ⟨e,he,hpower,hfix,Ω,star,hstar,_,_,fail⟩ :=
    geometric_signed_reader_fixed.{0,0,0,0,0,0} (Pin := Pin) (Wire := Wire) R.p k s ord chart.advice chart.branch B L
      (processors_fit_degree teams h r k hn)
  have hp := pow_pos R.prime.pos e
  have fieldCap : Fintype.card chart.E ≤ 2^T := by
    simpa only [Nat.card_eq_fintype_card] using (Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp cap.fieldBits
  have hL : L ≤ 2^T := (Nat.le_succ L).trans ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp cap.monomials)
  have hS : chart.degreeSum ≤ 2^T := (Nat.le_succ _).trans
    ((Nat.clog_le_iff_le_pow (by decide : 1 < 2)).mp cap.degrees)
  have gates (i : Fin h) : VPVNP.circuitSize (g i) ≤ size := chart.advice.equations_circuitSize ..
  obtain ⟨hd,hH,N,_,d',_,num,cost,circuit,entry⟩ := reader R.p B g chart.gadgets
    (R.p^e) L size multBits tally word T hp cap.parameters hL hS fieldCap cap.gates cap.labels
    cap.multiplicities ht hw hpower gates
  exact ⟨e,he,hfix,Ω,star,hstar,fail,hd,hH,N,d',num,cost,circuit,entry⟩

end Diagonal

end BorderVNP
end Computability
end OAI
