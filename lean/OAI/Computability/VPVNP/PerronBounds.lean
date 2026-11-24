import OAI.Computability.VPVNP.PerronSimplex
import OAI.Computability.VPVNP.LogBounds
import OAI.Computability.VPVNP.MacaulayRows

/-!
# Bit lengths of Perron degrees and Macaulay dimensions

The coefficient count for a Perron relation permits a degree that depends on
the number of variables. Its binary logarithm remains polynomially bounded
when the variable count and the input-degree logarithm are polynomially
bounded. The same holds for the dimensions of the resulting Macaulay matrix.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate

/-- The multiplier degree allowance obtained by substituting in a Perron
relation fits the paper's bound `H(d,t) = (2d)^(4(t+2))`. -/
theorem perronSimplexBound_le_paper_envelope {d t : ℕ} (hd : 3 ≤ d) :
    2 * (d + 1) * (perronSimplexBound (t + 1) (d + 1) + 1) ^ 2 ≤
      (2 * d) ^ (4 * (t + 2)) := by
  let b := 2 * d
  have hradix : 2 * (d + 2) ≤ b ^ 2 := by dsimp [b]; nlinarith
  have hcoef : 2 * (d + 1) ≤ b ^ 2 := by dsimp [b]; nlinarith
  have hpos : 1 ≤ (2 * (d + 2)) ^ (t + 1) := one_le_pow₀ (by omega)
  have hbase : perronSimplexBound (t + 1) (d + 1) + 1 ≤ b ^ (2 * (t + 1) + 1) := calc
    _ ≤ 3 * (2 * (d + 2)) ^ (t + 1) := by
      change 2 * (2 * (d + 2)) ^ (t + 1) + 1 ≤ _
      omega
    _ ≤ b * (b ^ 2) ^ (t + 1) :=
      Nat.mul_le_mul (by dsimp [b]; omega) (Nat.pow_le_pow_left hradix _)
    _ = _ := by rw [← pow_mul, pow_succ]; ac_rfl
  calc
    _ ≤ b ^ 2 * (b ^ (2 * (t + 1) + 1)) ^ 2 :=
      Nat.mul_le_mul hcoef (Nat.pow_le_pow_left hbase _)
    _ = b ^ (4 * (t + 2)) := by rw [← pow_mul, ← pow_add]; congr 1; omega

/-- The Perron degree has polynomial bit length even for input degrees of
polynomial bit length. -/
theorem polynomiallyBounded_clog_perronSimplexBound {m d : ℕ → ℕ} (hm : PolynomiallyBounded m)
    (hd : PolynomiallyBounded (fun n => Nat.clog 2 (d n))) :
    PolynomiallyBounded (fun n => Nat.clog 2 (perronSimplexBound (m n) (d n))) := by
  have hc := PolynomiallyBounded.clog (PolynomiallyBounded.const 2)
  exact PolynomiallyBounded.clog_mul hc (PolynomiallyBounded.clog_pow (PolynomiallyBounded.clog_mul hc
    (PolynomiallyBounded.clog_add hd (PolynomiallyBounded.clog (PolynomiallyBounded.const 1)))) hm)

/-- The paper's effective Nullstellensatz multiplier allowance has polynomial bit length. -/
theorem polynomiallyBounded_clog_paperBound {t d : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hd : PolynomiallyBounded (fun n => Nat.clog 2 (d n))) :
    PolynomiallyBounded (fun n => Nat.clog 2 ((2 * d n) ^ (4 * (t n + 2)))) :=
  PolynomiallyBounded.clog_pow (PolynomiallyBounded.clog_mul (PolynomiallyBounded.clog (PolynomiallyBounded.const 2)) hd)
    ((PolynomiallyBounded.const 4).mul (ht.add (PolynomiallyBounded.const 2)))

/-- Bit length of the actual index set of columns in a bounded coefficient matrix. -/
theorem polynomiallyBounded_clog_boundedMonomial {t D : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hD : PolynomiallyBounded (fun n => Nat.clog 2 (D n))) :
    PolynomiallyBounded (fun n => Nat.clog 2 (Fintype.card (BoundedMonomial (t n) (D n)))) :=
  (PolynomiallyBounded.clog_pow (PolynomiallyBounded.clog_add hD (PolynomiallyBounded.clog (PolynomiallyBounded.const 1))) ht).of_le
    fun _ => Nat.clog_mono_right _ (card_boundedMonomial_le _ _)

/-- For a Macaulay matrix formed from a certificate of multiplier degree `H`
and equations of degree `d`, both index sets have polynomial bit length. -/
theorem polynomiallyBounded_clog_macaulayDimensions {ι : ℕ → Type*} [∀ n, Fintype (ι n)]
    {t H d : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hι : PolynomiallyBounded (fun n => Nat.clog 2 (Fintype.card (ι n))))
    (hH : PolynomiallyBounded (fun n => Nat.clog 2 (H n)))
    (hd : PolynomiallyBounded (fun n => Nat.clog 2 (d n))) :
    PolynomiallyBounded (fun n => Nat.clog 2 (Fintype.card (ι n × BoundedMonomial (t n) (H n)))) ∧
    PolynomiallyBounded (fun n => Nat.clog 2 (Fintype.card (BoundedMonomial (t n) (H n + d n)))) := by
  simp only [Fintype.card_prod]
  exact ⟨PolynomiallyBounded.clog_mul hι (polynomiallyBounded_clog_boundedMonomial ht hH),
    polynomiallyBounded_clog_boundedMonomial ht (PolynomiallyBounded.clog_add hH hd)⟩

/-- The bit-length allowance for the prime in the characteristic-zero reduction
stays polynomial even if the coefficients have singly exponential bit length. -/
theorem polynomiallyBounded_good_prime_bits {t H d b : ℕ → ℕ} (ht : PolynomiallyBounded t)
    (hH : PolynomiallyBounded (fun n => Nat.clog 2 (H n)))
    (hd : PolynomiallyBounded (fun n => Nat.clog 2 (d n)))
    (hb : PolynomiallyBounded (fun n => Nat.clog 2 (b n))) :
    PolynomiallyBounded (fun n => let a := Nat.clog 2 (H n + d n + 1) * t n
      2 * (a + Nat.clog 2 (a + b n + 2)) + 1) := by
  have ha := (PolynomiallyBounded.clog_add (PolynomiallyBounded.clog_add hH hd)
    (PolynomiallyBounded.clog (PolynomiallyBounded.const 1))).mul ht
  exact ((PolynomiallyBounded.const 2).mul (ha.add
    (PolynomiallyBounded.clog_add (PolynomiallyBounded.clog_add (PolynomiallyBounded.clog ha) hb)
      (PolynomiallyBounded.clog (PolynomiallyBounded.const 2))))).add (PolynomiallyBounded.const 1)

end RadicalCertificate

end VPVNP
end Computability
end OAI
