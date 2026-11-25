import OAI.Computability.BorderVNP.ResiduePinRates
import OAI.Computability.BorderVNP.ResidueReaderRates
import OAI.Computability.BorderVNP.DiagonalResidueRAMRealization

/-!
# One uniform bound on the actual staged residue-entry circuit

The binary power cutoff is the one proved on the nonsingular branch.
The advised circuit is chosen before either live pin, the monomial tally,
the coefficient tally and the guess path. Its cost includes physical input
bits, guess bits, Boolean gates, delivered binary literals and native ticks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueRates

open Branch ResidueBox ResidueEntryInput ResidueEntryBudget ResidueIndex
open DiagonalResidueRAM VPVNP

/-- The staged native reader of Lemma 10.1, with one absolute polynomial
resource bound simultaneously over all finite fields, charts and later inputs.
The same preselected Cartier power is used throughout. -/
theorem uniform_staged_reader :
    ∃ A C : ℕ, ∀ {E J : Type*} [Field E] [Fintype E] [Fintype J]
      (p : ℕ) [Fact p.Prime] [CharP E p] [Algebra (ZMod p) E] {D h : ℕ}
      (B : Module.Basis (Fin D) (ZMod p) E) (g : Fin h → MvPolynomial (Option (Fin h)) E)
      (gadgets : J → E) (q L size m tally word M : ℕ) (hq : 0 < q),
      let S := ∑ i, (g i).totalDegree
      let H := radius L S
      let width := (q-1)*S
      let pin := M+6
      h ≤ M → L ≤ 2^M → S ≤ 2^M → Fintype.card E ≤ 2^M →
      size ≤ M → Fintype.card J ≤ M → m ≤ M → tally ≤ M → word ≤ M →
      q ≤ Fintype.card E * max (chartBoxPoleBudget h H S) 1 →
      (∀ i, circuitSize (g i) ≤ size) →
      ∃ (hβ : D ≤ 2^pin) (hH : 2*H < 2^pin), ∃ N ≤ Fintype.card E*(width+1),
      ∃ d ≤ Nat.clog 2 N, ∃ k,
        let x : ReaderSizes := ⟨h,size,Fintype.card J,m,pin,tally,D,d,word,p,q,H,width,N⟩
        x.stagedCharge k ≤ A*(M+1)^C ∧ ∃ circuit,
          StagedEntries (Guess (Fin h) d (Nat.clog 2 p+1) (Nat.clog 2 p))
            B q H hq hβ hH g gadgets m tally (k := k) circuit := by
  obtain ⟨a,c,select⟩ := uniform_reader_charge
  have bound := (PolynomiallyBounded.const a).mul
    ((polynomiallyBounded_gridBits.add (PolynomiallyBounded.const 1)).pow c)
  obtain ⟨A,C,hAC⟩ := bound.exists_global_bound
  refine ⟨A,C,?_⟩
  intro E J _ _ _ p _ _ _ D h B g gadgets q L size m tally word M hq S H width pin
    hh hL hS hE hsize hlabels hm ht hw hpower hg
  have hD := (ResidueEntryField.dimensions_le B hE).1
  obtain ⟨hβ,hH,-⟩ := chart_bit_bounds (N := 0) hh hL hS hE hD hpower (Nat.zero_le _)
  obtain ⟨N,hN,_,d,_,hd,hp,k,hk,circuit,entry⟩ :=
    exists_staged_over_base B q H size m tally hq hβ hH g hg gadgets
  let x : ReaderSizes := ⟨h,size,Fintype.card J,m,pin,tally,D,d,word,p,q,H,width,N⟩
  have hgate : k ≤ x.boardGates := by
    simpa only [ReaderSizes.boardGates, ReaderSizes.namedBits, ReaderSizes.guessBits,
      queryWidth, guessWidth, x, input_card, Fintype.card_option, Fintype.card_fin] using hk
  obtain ⟨_,_,hqbits,hHbits,hwidth,hNbits,_⟩ := chart_bit_bounds hh hL hS hE hD hpower hN
  have hpin : pin ≤ gridBits M := by dsimp only [pin,gridBits]; omega
  have hM : M ≤ gridBits M := (Nat.le_add_right M 6).trans hpin
  have hn {a} (ha : Nat.clog 2 a ≤ gridBits M) : a ≤ 2^gridBits M :=
    (Nat.le_pow_clog (by decide) a).trans (Nat.pow_le_pow_right (by decide) ha)
  have hq' : Nat.clog 2 q ≤ gridBits M := hqbits.trans (by unfold gridBits; omega)
  have hcharge := select x (gridBits M) (hh.trans hM) (hsize.trans hM) (hlabels.trans hM)
    (hm.trans hM) hpin (ht.trans hM) (hD.trans hM) (hd.trans hNbits) (hw.trans hM)
    (hp.trans (hn hNbits)) (hn hq') (hn hHbits) (hn hwidth) (hn hNbits)
  exact ⟨hβ,hH,N,hN,d,hd,k,(stagedCharge_le hgate).trans (hcharge.trans (hAC M)),circuit,entry⟩

end ResidueRates

end BorderVNP
end Computability
end OAI
