import OAI.Computability.VPVNP.MacaulayPairCall

/-! # Reading matrix entries from the physical flags and exponents

The equality word selects exactly the coefficient of the specified formal
monomial, also when the target is obtained by label multiplication or
Frobenius before taking the certificate power. The equation arm's flag
and residual exponents give the shifted scalar coefficient directly.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.PairCall

open MvPolynomial

variable {K : Type*}

/-- No marked coordinate is used for a source monomial in the appended matrix. -/
theorem powerMatch_entry [Zero K] [One K] (d : Inputs) (k : Ordinals d) (hm : d.mark = 0) :
    (if powerMatch d (monomial d k false) (monomial d k true) then (1 : K) else 0) =
      powerEntry d.scale (indexedDigits (k false)) (k true) := by
  simp [powerMatch, monomial, ExponentISA.shifted, hm, powerEntry, indexedDigits_eq]
  split_ifs with he <;> simp [he]

/-- The parameters used for a powered target row. -/
def targetScale {t e : ℕ} (S : QueryData t e K) : QueryData.Operation t → ℕ
  | .label _ => S.power
  | .frobenius => S.power*S.fieldOrder

/-- One-based variable index to increment for a label-multiplication query. Frobenius uses zero
so every coordinate is left unmarked. -/
def targetMark {t : ℕ} : QueryData.Operation t → ℕ
  | .label i => i.val+1
  | .frobenius => 0

theorem powerMatch_target [Zero K] [One K] {e : ℕ} (d : Inputs) (k : Ordinals d)
    (S : QueryData d.arity e K) (op : QueryData.Operation d.arity)
    (hs : d.scale = targetScale S op) (hm : d.mark = targetMark op) :
    (if powerMatch d (monomial d k false) (monomial d k true) then (1 : K) else 0) =
      powerEntry S.power (S.target op (indexedDigits (k false))) (k true) := by
  cases op with
  | label i =>
    simp only [powerMatch, decide_eq_true_eq, monomial, ExponentISA.shifted, hs, targetScale,
      hm, targetMark, Nat.add_left_inj, Fin.val_inj, powerEntry, QueryData.target, indexedDigits_eq, Nat.add_comm]
    split_ifs with he <;> simp [he]
  | frobenius =>
    simp [powerMatch, monomial, ExponentISA.shifted, hs, targetScale, hm, targetMark,
      powerEntry, QueryData.target, indexedDigits_eq, Nat.mul_assoc]
    split_ifs with he <;> simp [he]

/-- Decode the integer/affine row block. The ordered buffer has exactly
the difference exponents passed to the coefficient reader. -/
theorem equationEntry_at [Zero K] {e : ℕ} (d : Inputs) (k : Ordinals d) (i : Fin e)
    (getCoeff : Fin e → (Fin d.arity → ℕ) → K) :
    let a := monomial d k false
    let b := monomial d k true
    equationEntry getCoeff (finProdFinEquiv (i,k false)) (k true) =
      if a.val ≤ b.val then getCoeff i (fun j => b.val j-a.val j) else 0 := by
  simp [equationEntry, indexedDigits_eq, monomial, Finsupp.le_def]

end RadicalCertificate.MonomialIndex.PairCall

end VPVNP
end Computability
end OAI
