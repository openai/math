import OAI.Computability.BorderVNP.ResidueEntryCircuit
import OAI.Computability.BorderVNP.ResidueEntryCircuitIndex

/-! # Residue evaluation from the raw binary pin exponents

The same Boolean preprocessor and the same field circuit serve all entries
of all matrices. The former operates on signed integer labels and the
latter on the resulting words and the guessed multiplicative grid point.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ResidueFourier

open VPVNP ResidueBox ResidueIndex
open scoped Classical

/-- Connect the output wires of the binary query preprocessor to the field circuit. -/
noncomputable def queryAssignment {σ K : Type*} [Fintype σ] [Field K]
    (q H width w : ℕ) (x : Option σ → Kˣ) (raw : Raw σ w → Bool) (a b : K) :
    EntryInput σ w → K :=
  let y := (frame σ q H width w).eval raw
  entryAssignment x (fun i j => y (.inr (i,j))) (y (.inl ())) a b

/-- With raw binary pin exponents, the field circuit chosen once per chart produces
the Fourier summand of every matrix entry, including the out-of-box rejection case. -/
theorem exists_rawEntryCircuit {σ ι E K : Type*} [Fintype σ] [Fintype ι]
    [Field E] [Field K] [Fintype K] (φ : E →+* K) (q H width w s : ℕ) (hq : 0 < q)
    (hw : 2*H*q+3*H+q+width+1 < 2^w) (g : ι → MvPolynomial (Option σ) E)
    (hwidth : width = (q-1) * ∑ t, (g t).totalDegree) (hg : ∀ t, circuitSize (g t) ≤ s) :
    ∃ n ≤ entryGateBudget (Fintype.card ι) (Fintype.card (Option σ)) s
        (q-1).size (Fintype.card Kˣ-1).size w, ∃ c : Circuit K (EntryInput σ w) n,
      ∀ (a b : E) (e μ k : Exponent σ), Fits H e → Fits H μ → Fits H k →
      ∀ x : Option σ → Kˣ, c.eval id (queryAssignment q H width w x (encode w H e μ k) (φ a) (φ b)) =
        pathSummand φ q g a b e μ k x := by
  subst width
  obtain ⟨n, hn, c, hc⟩ := exists_entryCircuit φ q w s g hg (by omega)
  refine ⟨n, hn, c, ?_⟩
  intro a b e μ k he hm hk x
  let width := (q-1) * ∑ t, (g t).totalDegree
  let y := (frame σ q H width w).eval (encode w H e μ k)
  have valid := frame_valid q H width w hq hw e μ k he hm hk
  exact hc a b e μ k x (fun i j => y (.inr (i,j))) (y (.inl ())) valid
    fun h => frame_delta q H width w hq hw e μ k he hm hk (valid.mp h)

/-- Polynomial growth of all bit widths and chart sizes suffices for the field gate
budget, even when the raw powers and the grid itself have exponential size. -/
theorem polynomiallyBounded_entryGateBudget {charts coords s q f w : ℕ → ℕ}
    (hc : PolynomiallyBounded charts) (hn : PolynomiallyBounded coords)
    (hs : PolynomiallyBounded s) (hq : PolynomiallyBounded q)
    (hf : PolynomiallyBounded f) (hw : PolynomiallyBounded w) :
    PolynomiallyBounded fun n => entryGateBudget (charts n) (coords n) (s n) (q n) (f n) (w n) :=
  let c := PolynomiallyBounded.const
  ((c 5).add (hc.mul ((hs.add ((c 5).mul hq)).add (c 1)))).add
    (hn.mul ((((c 5).mul hf).add ((c 5).mul hw)).add (c 1)))

end ResidueFourier

end BorderVNP
end Computability
end OAI
