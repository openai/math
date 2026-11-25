import OAI.Optimization.LinearProgramming.PriceGame.ControlEncodingPopulation
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! A fixed polynomial for the whole physical population word, including the
multiplicity of the retained experts and the weight corresponding to each entry. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Wire

open States.Mass Learning Campaign

private theorem pairBound_mono {l r l' r' : ℕ} (hl : l ≤ l') (hr : r ≤ r') :
    pairBound l r ≤ pairBound l' r' := by unfold pairBound; gcongr

private theorem listBound_mono {n w n' w' : ℕ} (hn : n ≤ n') (hw : w ≤ w') :
    listBound n w ≤ listBound n' w' := by unfold listBound; gcongr

private theorem expertBound_mono {d v n w d' v' n' w' : ℕ}
    (hd : d ≤ d') (hv : v ≤ v') (hn : n ≤ n') (hw : w ≤ w') :
    expertBound d v n w ≤ expertBound d' v' n' w' :=
  pairBound_mono hd (pairBound_mono le_rfl (pairBound_mono (listBound_mono le_rfl hv)
    (pairBound_mono (Nat.add_le_add_left (pairBound_mono hd hv) 1) (listBound_mono hn hw))))

private theorem populationBound_mono {m e w m' e' w' : ℕ} (hm : m ≤ m') (he : e ≤ e') (hw : w ≤ w') :
    populationBound m e w ≤ populationBound m' e' w' :=
  pairBound_mono (listBound_mono hm he) (listBound_mono hm hw)

/-- The same expression is evaluated over naturals for a concrete bound and over
polynomials for the uniform resource estimate. -/
private def poolEnvelope {A : Type*} [Semiring A] (x t : A) (k : ℕ) : A :=
  let pair := fun a b : A => 2*a + b + 1
  let list := fun n w : A => n*(2*w+2) + 1
  let size := (x+t+1)*(k : A)
  let count := (x*(t+1))^k
  let w := 10 + 2*t + 3*(size+(6+size)*t)
  let v := 2*x^2
  let raw := 28+2*x
  let expert := pair x (pair 1 (pair (list 64 v) (pair (1+pair x v) (list x raw))))
  pair (list count expert) (list count w)

/-- Includes the catalogue, every expert descriptor and raw table, and all the incoming weights. -/
noncomputable def poolWordPolynomial : Polynomial ℕ :=
  poolEnvelope Polynomial.X (Polynomial.X^300) Pool.catalogueExponent

private theorem eval_poolEnvelope (x t : Polynomial ℕ) (k a : ℕ) :
    (poolEnvelope x t k).eval a = poolEnvelope (x.eval a) (t.eval a) k := by
  simp only [poolEnvelope, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_ofNat, Polynomial.eval_one, Polynomial.eval_natCast, Nat.cast_id]

private theorem size_succ_le (n : ℕ) : (n+1).size ≤ n.size + 1 := by
  apply Nat.size_le.mpr
  rw [pow_succ]
  have h := Nat.lt_size_self n
  have hp : 0 < 2^n.size := Nat.pow_pos (by decide)
  omega

private theorem poolWidth_le_envelope (N R T x U : ℕ) (hX : N+R.size+1 ≤ x) (hT : T ≤ U) :
    poolWidth N R T ≤ poolEnvelope x U Pool.catalogueExponent := by
  let A := (x + U + 1) * Pool.catalogueExponent
  have hx : N ≤ x := by omega
  have hr : (R+1).size ≤ x := (size_succ_le R).trans (by omega)
  have hD : depth N ≤ x := (Nat.succ_le_succ (Nat.log2_le_self N)).trans (by omega)
  have hv : 2*N^2 ≤ 2*x^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx _)
  have hc : expertCount N R T ≤ (x*(U+1))^Pool.catalogueExponent := by
    unfold expertCount
    exact Nat.pow_le_pow_left (Nat.mul_le_mul hX (Nat.succ_le_succ hT)) Pool.catalogueExponent
  have hb : catalogueBits N R T ≤ A := by
    unfold catalogueBits A
    apply Nat.mul_le_mul_right
    have hs (k : ℕ) : k.size ≤ k := Nat.size_le.mpr k.lt_two_pow_self
    have h1 := (hs (N+R.size+1)).trans hX
    have h2 := (hs (T+1)).trans (Nat.succ_le_succ hT)
    omega
  have hw : weightWidth N R T ≤ 10+2*U+3*(A+(6+A)*U) := by
    change 10+2*T+3*(catalogueBits N R T+(6+catalogueBits N R T)*T) ≤ _
    exact Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_left _ hT) _)
      (Nat.mul_le_mul_left _ (Nat.add_le_add hb (Nat.mul_le_mul (Nat.add_le_add_left hb _) hT)))
  have he := expertBound_mono hD hv hx (show 28+2*(R+1).size ≤ 28+2*x from
    Nat.add_le_add_left (Nat.mul_le_mul_left _ hr) _)
  exact populationBound_mono hc he hw

theorem poolWidth_polynomial (N R T : ℕ) (hT : T ≤ (N + R.size + 1)^300) :
    poolWidth N R T ≤ poolWordPolynomial.eval (N + R.size + 1) := by
  simp only [poolWordPolynomial, eval_poolEnvelope, Polynomial.eval_X, Polynomial.eval_pow]
  exact poolWidth_le_envelope N R T (N+R.size+1) ((N+R.size+1)^300) le_rfl hT

/-- A single polynomial in dimension and hidden-cost width bounds the actual
binary encoding of each public root state of the unrestricted campaign. -/
theorem run_population_wire_polynomial {N : ℕ} (anchor : Fin N) (R T : ℕ)
    (markets : AvailableMarkets N) (reply : List (Query N × Bool) → Query N → Bool)
    (history : List (Query N × Bool)) (out : ℕ → RoundResult N)
    (hx : ∀ j : Fin T, out j.val =
      ((trialLoop (Pool.batch N R) (runRound R markets) T (Population.start (Pool.batch N R))).run reply history) j)
    (hT : T ≤ (N + R.size + 1)^300) (t : ℕ) (ht : t ≤ T) :
    (packedPopulationCode (packPopulation (population R out t))).length ≤
      poolWordPolynomial.eval (N + R.size + 1) :=
  (run_population_wire_length anchor R T markets reply history out hx t ht).trans (poolWidth_polynomial N R T hT)

end Wire
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
