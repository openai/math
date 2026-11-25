import OAI.Computability.BorderVNP.CrossingFusionAtLength
import OAI.Computability.BorderVNP.CrossingNormalization
import OAI.Computability.BorderVNP.Rate

/-! # The actual shortening argument at the quantitative rate

The signed coefficient queries and the paid crossing come from the gate and
projection constructions in §4. For each ground characteristic only the
stretch implication of Theorem 3.2 is needed in the deduction below. Its
exponent is allowed to depend on the individual identity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Rate

open Filter BorderVNP.Crossing MvPolynomial
universe u

/-- The border stretch assertion of §3 for the algebraic closure of a prime field.
The wire configuration, widths and tables are all part of the paid identity. -/
def PrimeFieldStretch (K : Type) [Field K] : Prop :=
  ∀ D ≥ 2, ∀ m > 0, Nonempty (PaidIdentity (AlgebraicClosure K) D m) →
    ∃ ε : ℝ, 0 < ε ∧ ∀ᶠ n : ℕ in atTop, (2 : ℝ)^((n : ℝ)^ε) ≤
      borderSize n (map (Int.castRingHom (AlgebraicClosure K)) (Pstar n))

/-- A single absolute rate constant works for all characteristics satisfying §3.2.
Every exceptional length is tested using the actual degree-projected image closure
and yields the concrete signed-table shortening of §4. -/
theorem absolute_ground_rate :
    ∃ c : ℝ, 0 < c ∧ ∀ (K : Type) [Field K], PrimeFieldStretch K →
      ∀ᶠ n : ℕ in atTop, rate c n ≤ borderSize n (map (Int.castRingHom K) (Pstar n)) := by
  obtain ⟨c₁, hc₁, _, hcross⟩ := exists_width_paidIdentity_of_small_approximation.{0}
  let c₀ : ℝ := 1/100
  let c₂ : ℝ := 1/100
  let c := crossingConstant c₀ c₁ c₂
  have h₀ : 0 < c₀ := by norm_num [c₀]
  have h₂ : 0 < c₂ := by norm_num [c₂]
  have hall := hcross c₀ h₀ (by norm_num [c₀])
  have perField (K : Type) [Field K] (hK : PrimeFieldStretch K) :
      ∀ᶠ n : ℕ in atTop, rate c n ≤ borderSize n (map (Int.castRingHom K) (Pstar n)) := by
    let s (n : ℕ) := borderSize n (map (Int.castRingHom K) (Pstar n))
    apply eventual_rate_of_single_shortening h₀ hc₁ h₂ s (HasProfileShortening (AlgebraicClosure K))
    · filter_upwards [hall] with n hsmall
      intro hn
      have ha := borderSize_spec n (map (Int.castRingHom K) (Pstar n))
      have he : (algebraMap K (AlgebraicClosure K)).comp (Int.castRingHom K) =
        Int.castRingHom (AlgebraicClosure K) := Subsingleton.elim ..
      simp only [BorderApprox, MvPolynomial.map_map, he] at ha
      obtain ⟨hd,t,ht,hpaid⟩ := hsmall (AlgebraicClosure K) (s n) hn ha
      exact (hasProfileShortening_iff_paid _).mpr ⟨_,hd,_,ht,hpaid⟩
    · intro hs
      obtain ⟨D,hD,m,hm,hi⟩ := (hasProfileShortening_iff_paid _).mp hs
      obtain ⟨ε,hε,hbound⟩ := hK D hD m hm hi
      refine ⟨ε,hε,?_⟩
      filter_upwards [hbound] with n hn
      have he : (algebraMap K (AlgebraicClosure K)).comp (Int.castRingHom K) =
        Int.castRingHom (AlgebraicClosure K) := Subsingleton.elim ..
      have eq := borderSize_map (E := AlgebraicClosure K) n (map (Int.castRingHom K) (Pstar n))
      rw [MvPolynomial.map_map, he] at eq
      exact hn.trans_eq (congrArg Nat.cast eq)
  exact ⟨c,crossingConstant_pos h₀ hc₁ h₂,perField⟩

/-- The uniform field conclusion specializes the same absolute coefficient to the
rational prime field and to each positive-characteristic prime field. -/
theorem uniform_rate_of_border_stretch
    (hzero : PrimeFieldStretch ℚ)
    (hpos : ∀ q : ℕ, ∀ hq : q.Prime, letI : Fact q.Prime := ⟨hq⟩; PrimeFieldStretch (ZMod q)) :
    ∃ c : ℝ, 0 < c ∧ ∀ q : ℕ, ∃ N : ℕ, ∀ n ≥ N, ∀ (F : Type u) [Field F] [CharP F q],
      rate c n ≤ borderSize n (map (Int.castRingHom F) (Pstar n)) := by
  obtain ⟨c,hc,perField⟩ := absolute_ground_rate
  refine ⟨c,hc,uniform_of_prime_fields Pstar id c (perField ℚ hzero) ?_⟩
  intro q hq
  let : Fact q.Prime := ⟨hq⟩
  exact perField (ZMod q) (hpos q hq)

end Rate

end BorderVNP
end Computability
end OAI
