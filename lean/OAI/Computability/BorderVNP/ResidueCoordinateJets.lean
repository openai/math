import OAI.Computability.BorderVNP.ResidueBranchJet
import OAI.Computability.BorderVNP.ResidueJetRing
import OAI.Computability.BorderVNP.ResidueAmbientJet

/-!
# Coordinates on the two successive jet algebras

The parameter directions are truncated over the univariate branch jet.
Translating the parameter directions by their branch increments and changing
the last coordinate from the uniformizer to `t` gives the normalized
coefficient functional of the ambient chart.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Residue.CoordinateJets

open BranchJet JetRing
open scoped BigOperators

noncomputable section

variable {κ σ : Type*} [Field κ] [Fintype σ] (p : ℕ) [Fact p.Prime]
  [CharP κ p] [PerfectRing κ p]

/-- The parameter jet algebra over the jet in the branch uniformizer. -/
abbrev Combined (σ κ : Type*) [Field κ] (p : ℕ) :=
  JetRing.Carrier σ (BranchJet.Ring κ p) (p-1)

/-- The parameter and time increments under the Taylor substitution. -/
def delta (x : σ → LaurentSeries κ) (t : LaurentSeries κ) : Option σ → Combined σ κ p
  | none => algebraMap (BranchJet.Ring κ p) _ (jet p t - algebraMap _ _ t)
  | some i => algebraMap (BranchJet.Ring κ p) _ (jet p (x i) - algebraMap _ _ (x i)) +
      coord (p-1) i

/-- The normalized top coefficient in the two successive jet rings. -/
def chartTop (t : LaurentSeries κ) : Combined σ κ p →ₗ[LaurentSeries κ] LaurentSeries κ :=
  ((LaurentSeries.derivative κ t)^p)⁻¹ •
    ((BranchJet.top p).comp <| (LinearMap.mulRight _ (jet p (LaurentSeries.derivative κ t))).comp <|
      (JetRing.top (ι := σ) (B := BranchJet.Ring κ p) (p-1)).restrictScalars (LaurentSeries κ))

/-- The chart top functional is one on the top monomial and zero on the other
reduced monomials, including when the time function is ramified. -/
theorem chartTop_monomial (x : σ → LaurentSeries κ) (t : LaurentSeries κ)
    (ht : LaurentSeries.derivative κ t ≠ 0) (b : Option σ → ℕ) (hb : ∀ i, b i ≤ p-1) :
    chartTop p t (∏ i, delta p x t i ^ b i) = if b = (fun _ => p-1) then 1 else 0 := by
  classical
  let z (i : σ) := jet p (x i) - algebraMap _ (BranchJet.Ring κ p) (x i)
  have htX := jet_top_translate (p-1) (JetRing.top (ι := σ) (B := BranchJet.Ring κ p) (p-1))
    z (coord (p-1)) (fun b _ => top_monomial (p-1) b) (fun i => b (some i)) (fun i => hb _)
  rw [Fintype.prod_option]
  change ((LaurentSeries.derivative κ t)^p)⁻¹ *
    BranchJet.top p (JetRing.top (p-1)
      ((algebraMap (BranchJet.Ring κ p) _ (jet p t - algebraMap _ _ t)) ^ b none *
        ∏ i, (algebraMap (BranchJet.Ring κ p) _ (z i) + coord (p-1) i)^b (some i)) *
        jet p (LaurentSeries.derivative κ t)) = _
  rw [← map_pow (algebraMap (BranchJet.Ring κ p) (Combined σ κ p)), ← Algebra.smul_def,
    map_smul, smul_eq_mul, htX]
  split_ifs with hx ha
  · rw [mul_one, top_increment_derivative, ite_eq_left (congrFun ha none), inv_mul_cancel₀
      (pow_ne_zero _ ht)]
  · have hn : b none ≠ p - 1 := by
      intro hn
      exact ha (funext fun i => by cases i with
        | none => exact hn
        | some j => exact congrFun hx j)
    rw [mul_one, top_increment_derivative, ite_eq_right hn, mul_zero]
  · rename_i ha
    exact False.elim (hx (by rw [ha]))
  · simp

omit [Fintype σ] in
/-- Every translated increment is nilpotent of the truncation order. -/
theorem delta_pow [ExpChar (Combined σ κ p) p] (x : σ → LaurentSeries κ) (t : LaurentSeries κ)
    (i : Option σ) : delta p x t i ^ p = 0 := by
  cases i with
  | none => rw [delta, ← map_pow, jet_sub_pow, map_zero]
  | some i =>
    rw [delta, add_pow_expChar, ← map_pow, jet_sub_pow, map_zero, zero_add]
    have := coord_pow (B := BranchJet.Ring κ p) (p-1) i
    rwa [Nat.sub_add_cancel (Fact.out : p.Prime).pos] at this

end
end Residue.CoordinateJets

end BorderVNP
end Computability
end OAI
