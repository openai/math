import OAI.LinearAlgebra.FiniteFourier.ConvolutionPrimeColoring
import OAI.LinearAlgebra.FiniteFourier.ConvolutionDyadicProgressions
import OAI.LinearAlgebra.FiniteFourier.ConvolutionShiftedPrimes
import OAI.NumberTheory.JointDickman.Amplification.ReciprocalTail
import Mathlib.Tactic

/-! # Counting shared odd prime factors on two axes

A collision on distinct dyadic prime axes must divide both predecessors.
The contribution from large moduli follows by counting all multiples, and
the small-modulus sum uses the progression counts at residue one.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
open Finset Real
open scoped BigOperators Classical

section

private lemma no_axis_dvd_shift {B p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hp₀ : B/2 < p) (hq' : q ≤ B)
    (hpp : p ≠ 2) (hqq : q ≠ 2) : ¬ p ∣ q - 1 := by
  rintro ⟨k, hk⟩
  have hkpos : 0 < k := by
    by_contra! h
    have : k = 0 := by omega
    simp [this] at hk
    have := hq.two_le
    omega
  have hklt : k < 2 := by
    by_contra! h
    have hmul := Nat.mul_le_mul_left p h
    omega
  have : k = 1 := by omega
  simp [this] at hk
  have hpodd := hp.mod_two_eq_one_iff_ne_two.mpr hpp
  have hqodd := hq.mod_two_eq_one_iff_ne_two.mpr hqq
  omega

private lemma odd_prime_shift_sum (L : Finset ℕ)
    (hL : ∀ l ∈ L, l.Prime ∧ 3 ≤ l) :
    ∑ l ∈ L, 1 / ((l : ℝ)-1)^2 ≤ 1/2 := by
  let half (l : ℕ) := l/2
  have heq (l : ℕ) (hl : l ∈ L) : l = 2 * half l + 1 := by
    have h := (hL l hl).1.mod_two_eq_one_iff_ne_two.mpr (by have := (hL l hl).2; omega)
    dsimp [half]
    omega
  let Q := L.image half
  have hhalf (l : ℕ) (hl : l ∈ L) : (l : ℝ) - 1 = 2 * (half l : ℝ) := by
    have eq := congrArg (fun n : ℕ ↦ (n : ℝ)) (heq l hl)
    push_cast at eq
    linarith
  have hpow : ∑ q ∈ Q, 1/(q : ℝ)^2 ≤ 2 := by
    have htail := JointDickman.sum_reciprocal_square_tail (Q.erase 1) (N := 1) (by decide)
      (by
        intro q hq
        obtain ⟨hne, hQ⟩ := mem_erase.mp hq
        obtain ⟨l, hl, rfl⟩ := mem_image.mp hQ
        have := (hL l hl).2
        dsimp [half] at *
        omega)
    norm_num at htail
    by_cases h : 1 ∈ Q
    · rw [← sum_erase_add _ _ h]
      norm_num
      linarith
    · simpa [erase_eq_of_notMem h] using htail.trans (by norm_num : (1 : ℝ) ≤ 2)
  have hsum : (∑ l ∈ L, 1/((l : ℝ)-1)^2) =
      (1/4 : ℝ) * ∑ q ∈ Q, 1/(q : ℝ)^2 := by
    rw [mul_sum, sum_image]
    · apply sum_congr rfl
      intro l hl
      rw [hhalf l hl]
      ring
    · intro l hl k hk eq
      rw [heq l hl, heq k hk, eq]
  linarith

private lemma count_shift_fibre_le {B l : ℕ} (P : Finset ℕ)
    (hP : ∀ p ∈ P, 2 ≤ p ∧ p ≤ B) (hl : 0 < l) :
    ((P.filter (l ∣ · - 1)).card : ℝ) ≤ B/l := by
  let T := (range (B+1)).filter fun m ↦ m ≠ 0 ∧ l ∣ m
  have h : (P.filter (l ∣ · - 1)).card ≤ T.card := by
    apply card_le_card_of_injOn (fun p ↦ p-1)
    · intro p hp
      obtain ⟨hp, hl⟩ := mem_filter.mp hp
      obtain ⟨hp₀, hp₁⟩ := hP p hp
      change p-1 ∈ T
      exact mem_filter.mpr ⟨mem_range.mpr (by omega), by omega, hl⟩
    · intro p hp q hq he
      have p2 := (hP p (mem_filter.mp hp).1).1
      have q2 := (hP q (mem_filter.mp hq).1).1
      dsimp at he
      omega
  have h' : (P.filter (l ∣ · - 1)).card ≤ B/l := by
    simpa only [T, Nat.card_multiples'] using h
  apply (le_div_iff₀ (by exact_mod_cast hl : (0 : ℝ) < l)).mpr
  exact_mod_cast (Nat.mul_le_mul_right l h').trans (Nat.div_mul_le_self B l)

private lemma shift_fibre_squares {B H : ℕ} (P : Finset ℕ) (L : Finset ℕ) {a : ℝ}
    (hP : ∀ p ∈ P, 2 ≤ p ∧ p ≤ B)
    (hL : ∀ l ∈ L, l.Prime ∧ 3 ≤ l)
    (hH : 1 ≤ H) (_ha : 0 ≤ a)
    (hsmall : ∀ l ∈ L, l ≤ H →
      ((P.filter (l ∣ · - 1)).card : ℝ) ≤ P.card / ((l : ℝ)-1) + a) :
    (∑ l ∈ L, ((P.filter (l ∣ · - 1)).card : ℝ)^2) ≤
      (5/8 : ℝ) * (P.card : ℝ)^2 + 5 * H * a^2 + (B : ℝ)^2 / H := by
  let S := L.filter (· ≤ H)
  let T := L.filter (fun l ↦ ¬l ≤ H)
  let f (l : ℕ) : ℝ := (P.filter (l ∣ · - 1)).card
  have hsplit : (∑ l ∈ S, (f l)^2) + (∑ l ∈ T, (f l)^2) = ∑ l ∈ L, (f l)^2 :=
    sum_filter_add_sum_filter_not L (· ≤ H) _
  have hS : (S.card : ℝ) ≤ H := by
    have hi : S ⊆ Icc 1 H := fun l hl ↦ mem_Icc.mpr ⟨by
      have := (hL l (mem_filter.mp hl).1).2; omega, (mem_filter.mp hl).2⟩
    exact_mod_cast (show S.card ≤ H by simpa using card_le_card hi)
  have hsumS : ∑ l ∈ S, (f l)^2 ≤ 5/8 * (P.card : ℝ)^2 + 5*H*a^2 := calc
    _ ≤ ∑ l ∈ S, (((5/4 : ℝ) * (P.card : ℝ)^2) * (1/((l : ℝ)-1)^2) + 5*a^2) := by
      apply sum_le_sum
      intro l hl
      have h := hsmall l (mem_filter.mp hl).1 (mem_filter.mp hl).2
      have hn : 0 ≤ f l := Nat.cast_nonneg _
      have hy : (f l)^2 ≤ (P.card / ((l : ℝ)-1) + a)^2 := by
        apply pow_le_pow_left₀ hn h
      have hxy := sq_nonneg ((P.card : ℝ)/((l : ℝ)-1) - 4*a)
      have heq : ((P.card : ℝ)/((l : ℝ)-1))^2 = (P.card : ℝ)^2 * (1/((l : ℝ)-1)^2) := by rw [div_pow, div_eq_mul_one_div]
      nlinarith only [hy, hxy, heq]
    _ = ((5/4 : ℝ) * (P.card : ℝ)^2) * (∑ l ∈ S, 1/((l : ℝ)-1)^2) + S.card * (5*a^2) := by
      rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ _ := by
      have hx := mul_le_mul_of_nonneg_left (odd_prime_shift_sum S
        (fun l hl ↦ hL l (mem_filter.mp hl).1)) (show 0 ≤ (5/4 : ℝ) * (P.card : ℝ)^2 by positivity)
      nlinarith only [hx, mul_le_mul_of_nonneg_right hS (sq_nonneg a)]
  have hsumT : ∑ l ∈ T, (f l)^2 ≤ (B : ℝ)^2/H := calc
    _ ≤ ∑ l ∈ T, (B : ℝ)^2 * (1 / (l : ℝ)^2) := by
      apply sum_le_sum
      intro l hl
      have hl₀ := (hL l (mem_filter.mp hl).1).2
      have h := pow_le_pow_left₀ (show 0 ≤ f l from Nat.cast_nonneg _)
        (count_shift_fibre_le P hP (show 0 < l by omega)) 2
      simpa [div_pow, mul_pow, div_eq_mul_inv] using h
    _ = (B : ℝ)^2 * ∑ l ∈ T, 1/(l : ℝ)^2 := (mul_sum _ _ _).symm
    _ ≤ _ := by
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left (JointDickman.sum_reciprocal_square_tail T (by omega)
        (fun l hl ↦ lt_of_not_ge (mem_filter.mp hl).2)) (sq_nonneg _)
  change ∑ l ∈ L, (f l)^2 ≤ _
  linarith

/-- Diagonal, ineligible, and shared-predecessor pairs cover the complement
of the disjoint eligible pairs. -/
private lemma count_axis_collisions {B : ℕ} (P E R : Finset ℕ) (hB : 8 ≤ B)
    (hP : ∀ p ∈ P, p.Prime ∧ B / 2 < p ∧ p ≤ B)
    (helig : ∀ p ∈ P, p ∈ E ∨ p ∈ R) :
    let G := (E ×ˢ E).filter fun z ↦ Disjoint (axisOddPrimeSupport z.1) (axisOddPrimeSupport z.2)
    let L := (Icc 3 B).filter Nat.Prime
    (P.card)^2 ≤ G.card + 2 * R.card * P.card + P.card +
      ∑ l ∈ L, ((P.filter (l ∣ · - 1)).card)^2 := by
  intro G L
  let F (l : ℕ) := P.filter (l ∣ · - 1)
  let A := P.image fun p ↦ (p,p)
  let C := L.biUnion fun l ↦ F l ×ˢ F l
  have hsub : P ×ˢ P ⊆ G ∪ (R ×ˢ P) ∪ (P ×ˢ R) ∪ A ∪ C := by
    rintro ⟨p,q⟩ hpq
    obtain ⟨hp,hq⟩ := mem_product.mp hpq
    simp only [mem_union, mem_product]
    by_cases eq : p = q
    · left; right
      exact mem_image.mpr ⟨p, hp, by simp [eq]⟩
    obtain ⟨pp,p₁,p₂⟩ := hP p hp
    obtain ⟨pq,q₁,q₂⟩ := hP q hq
    rcases helig p hp with hpE | hpR
    · rcases helig q hq with hqE | hqR
      · by_cases hd : Disjoint (axisOddPrimeSupport p) (axisOddPrimeSupport q)
        · left; left; left; left
          exact mem_filter.mpr ⟨mem_product.mpr ⟨hpE,hqE⟩,hd⟩
        right
        obtain ⟨l, hlp, hlq⟩ := Finset.not_disjoint_iff.mp hd
        obtain ⟨hl₂, hlprime, hdvp⟩ := (mem_axisOddPrimeSupport pp.two_le).mp hlp
        obtain ⟨_, _, hdvq⟩ := (mem_axisOddPrimeSupport pq.two_le).mp hlq
        have hpq' := no_axis_dvd_shift pp pq p₁ q₂ (by omega) (by omega)
        have hqp' := no_axis_dvd_shift pq pp q₁ p₂ (by omega) (by omega)
        have hshift : l ∣ p-1 ∧ l ∣ q-1 := by
          rcases hlprime.dvd_mul.mp hdvp with hp' | hp' <;>
            rcases hlprime.dvd_mul.mp hdvq with hq' | hq'
          · exact (eq (((Nat.prime_dvd_prime_iff_eq hlprime pp).mp hp').symm.trans
              ((Nat.prime_dvd_prime_iff_eq hlprime pq).mp hq'))).elim
          · exact (hpq' ((Nat.prime_dvd_prime_iff_eq hlprime pp).mp hp' ▸ hq')).elim
          · exact (hqp' ((Nat.prime_dvd_prime_iff_eq hlprime pq).mp hq' ▸ hp')).elim
          · exact ⟨hp',hq'⟩
        have hlB : l ≤ B := (Nat.le_of_dvd (by omega : 0 < p-1) hshift.1).trans (by omega)
        have hlL : l ∈ L := mem_filter.mpr ⟨mem_Icc.mpr ⟨by have := hlprime.two_le; omega, hlB⟩, hlprime⟩
        exact mem_biUnion.mpr ⟨l, hlL, mem_product.mpr
          ⟨mem_filter.mpr ⟨hp,hshift.1⟩, mem_filter.mpr ⟨hq,hshift.2⟩⟩⟩
      · left; left; right; exact ⟨hp,hqR⟩
    · left; left; left; right; exact ⟨hpR,hq⟩
  have hC : C.card ≤ ∑ l ∈ L, (F l).card ^ 2 := by
    simpa only [C, card_product, sq] using
      (card_biUnion_le (s := L) (t := fun l ↦ F l ×ˢ F l))
  have h := (card_le_card hsub).trans (card_union_le _ _)
  have h₁ := card_union_le (G ∪ (R ×ˢ P) ∪ (P ×ˢ R)) A
  have h₂ := card_union_le (G ∪ (R ×ˢ P)) (P ×ˢ R)
  have h₃ := card_union_le G (R ×ˢ P)
  have hA : A.card ≤ P.card := card_image_le
  simp only [card_product] at h h₁ h₂ h₃
  change P.card ^ 2 ≤ _ + ∑ l ∈ L, (F l).card ^ 2
  nlinarith only [h, h₁, h₂, h₃, hA, hC]

/-- Finite collision estimate for the pair count. Small progressions enter
with additive error `a`. All moduli larger than `H` cost at most `B²/H`. -/
theorem dyadicPairLoss_bound (B H : ℕ) (η a : ℝ) (hB : 8 ≤ B) (hH : 1 ≤ H)
    (ha : 0 ≤ a)
    (hprog : ∀ l : ℕ, l.Prime → 3 ≤ l → l ≤ H →
      ((axisShiftFibre B l).card : ℝ) ≤ (dyadicAxisPrimes B).card / ((l : ℝ)-1) + a) :
    ((dyadicAxisPrimes B).card : ℝ)^2 ≤ (dyadicDisjointPairs B η).card +
      2 * (roughPredecessorPrimes B η).card * (dyadicAxisPrimes B).card +
      (dyadicAxisPrimes B).card + 5/8 * ((dyadicAxisPrimes B).card : ℝ)^2 +
      5 * H * a^2 + (B : ℝ)^2 / H := by
  let P := dyadicAxisPrimes B
  let E := dyadicEligibleAxes B η
  let R := roughPredecessorPrimes B η
  let L := (Icc 3 B).filter Nat.Prime
  have hP (p : ℕ) (hp : p ∈ P) : p.Prime ∧ B/2 < p ∧ p ≤ B := by
    obtain ⟨h₁,h₂,h₃⟩ := mem_dyadicAxisPrimes.mp hp
    exact ⟨h₁,by omega,h₃⟩
  have helig (p : ℕ) (hp : p ∈ P) : p ∈ E ∨ p ∈ R := by
    obtain ⟨h₁,h₂,h₃⟩ := hP p hp
    by_cases hsm : ∀ l ∈ (p-1).primeFactors, (l : ℝ) ≤ (B : ℝ)^(1-η)
    · exact Or.inl (mem_dyadicEligibleAxes.mpr ⟨⟨h₂,h₃⟩, h₁, hsm⟩)
    · push Not at hsm
      right
      change p ∈ roughPredecessorPrimes (B : ℝ) η
      simp only [roughPredecessorPrimes, mem_filter]
      exact ⟨mem_erase.mpr ⟨by omega,
        Nat.mem_primesLE.mpr ⟨by simpa using h₃, h₁⟩⟩, hsm⟩
  have hcount : (P.card : ℝ)^2 ≤ (dyadicDisjointPairs B η).card + 2*R.card*P.card +
      P.card + ∑ l ∈ L, ((P.filter (l ∣ · - 1)).card : ℝ)^2 := by
    have h := count_axis_collisions P E R hB hP helig
    dsimp only at h
    exact_mod_cast h
  have hL (l : ℕ) (hl : l ∈ L) : l.Prime ∧ 3 ≤ l :=
    ⟨(mem_filter.mp hl).2,(mem_Icc.mp (mem_filter.mp hl).1).1⟩
  have hshift := shift_fibre_squares P L (fun p hp ↦ ⟨(hP p hp).1.two_le,(hP p hp).2.2⟩)
    hL hH ha (fun l hl hh ↦ hprog l (hL l hl).1 (hL l hl).2 hh)
  change (P.card : ℝ)^2 ≤ (dyadicDisjointPairs B η).card + 2 * R.card * P.card + P.card +
    5/8 * (P.card : ℝ)^2 + 5 * H * a^2 + (B : ℝ)^2/H
  linarith only [hcount, hshift]

end

end

end FiniteFourier
end LinearAlgebra
end OAI
