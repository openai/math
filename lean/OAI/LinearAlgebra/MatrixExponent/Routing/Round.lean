import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.System
import OAI.LinearAlgebra.MatrixExponent.Spectrum.Comparison
import OAI.LinearAlgebra.MatrixExponent.Spectral.Placements
import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Local substitutions including selector cost

The alphabet of offers stays fixed as the common rate is multiplied.
The constant from strict spectral comparison is absorbed later, by
repeating the entire construction. Even a unary selector for each
letter then fits in the strict margin.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral
open scoped NNReal

variable {K S I J : Type} [Field K] [Fintype S] [Nonempty S]

/-- A direct sum of words in supplies restricts to a block of demands.
A selector chooses a summand. Its transmission costs at most `H` per bit. -/
structure Replacement (D : Tensor K S) (T : I → Tensor K S)
    (p : I → ℝ) (L H : ℝ) where
  block : ℕ
  positive : 0 < block
  letter : Type
  [finiteLetter : Fintype letter]
  length : ℕ
  bits : ℕ
  fits : Fintype.card letter ≤ 2 ^ bits
  good : letter → Fin length → I
  count : letter → Fin length → ℕ
  cheaper : ∀ j, (∑ i, (count j i : ℝ) * p (good j i)) + bits * H < block * L
  covers : D ^ block ≤ ∑ j, ∏ i, T (good j i) ^ count j i

attribute [instance] Replacement.finiteLetter

private theorem scale_margin [Fintype J] (g : J → ℝ) (hg : ∀ j, 0 < g j) (H : ℝ) :
    ∃ k : ℕ, 0 < k ∧ ∀ j, H < g j * k := by
  choose a ha using fun j => exists_nat_gt (H / g j)
  refine ⟨(∑ j, a j) + 1, Nat.zero_lt_succ _, fun j => ?_⟩
  rw [mul_comm, ← div_lt_iff₀ (hg j)]
  apply (ha j).trans_le
  exact_mod_cast (Finset.single_le_sum (fun i _ => Nat.zero_le (a i))
    (Finset.mem_univ j)).trans (Nat.le_succ _)

omit [Nonempty S] in
private theorem expand_word [Fintype J] (V : J → Tensor K S) (C r : ℕ) :
    (C : Tensor K S) * (∑ j, V j) ^ r =
      ∑ j : Fin C × (Fin r → J), ∏ i, V (j.2 i) := by
  simp only [Fintype.sum_prod_type, ← Fintype.sum_pow, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul]

private theorem replace_aux [Fintype J] (D : Tensor K S) (T : I → Tensor K S)
    (p : I → ℝ) (L H : ℝ) (t : J → I) (n : J → ℕ) (b : ℕ) (hb : 0 < b)
    (hmargin : ∀ j, (n j : ℝ) * p (t j) < (b : ℝ) * L)
    (hspec : ∀ v : Tensor K S →+* ℝ≥0, Monotone v → ∃ j, v D ^ b < v (T (t j)) ^ n j)
    (hunit : ∃ j, n j = 0) : Nonempty (Replacement D T p L H) := by
  classical
  let m := Fintype.card J
  obtain ⟨k, hk, hg⟩ := scale_margin (fun j => (b : ℝ) * L - n j * p (t j))
    (fun j => sub_pos.mpr (hmargin j)) (m * H + 1)
  let V j := T (t j) ^ (n j * k)
  have hn : (∑ j, V j) ≠ 0 := by
    obtain ⟨j, hj⟩ := hunit
    have hv : V j = 1 := by simp [V, hj]
    have hs : 1 ≤ ∑ i, V i := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ j), hv]
      have h := Tensor.add_le_add_right 0 (∑ i ∈ Finset.univ.erase j, V i) 1 (Tensor.zero_le _)
      rw [zero_add] at h
      exact h
    intro h
    rw [h] at hs
    exact one_ne_zero (le_antisymm hs (Tensor.zero_le _))
  have hstrict (v : Tensor K S →+* ℝ≥0) (hv : Monotone v) :
      v (D ^ (b * k)) < v (∑ j, V j) := by
    obtain ⟨j, hj⟩ := hspec v hv
    rw [map_sum, map_pow, pow_mul]
    refine lt_of_lt_of_le ?_ (Finset.single_le_sum (fun _ _ => zero_le) (Finset.mem_univ j))
    simp only [V, map_pow, pow_mul]
    exact pow_lt_pow_left₀ hj zero_le hk.ne'
  obtain ⟨C, hC⟩ := Spectrum.strictComparison Tensor.add_le_add_right Tensor.mul_le_mul_left
    Tensor.zero_le Tensor.one_le Tensor.exists_bound hn hstrict
  obtain ⟨r, hr⟩ := exists_nat_gt (max 0 ((C : ℝ) * H))
  have hr0 : 0 < r := Nat.cast_pos.mp ((le_max_left _ _).trans_lt hr)
  let W := Fin C × (Fin r → J)
  refine ⟨{ block := b * k * r, positive := by positivity, letter := W, length := r, bits := C + m * r
            fits := ?_, good := fun j i => t (j.2 i), count := fun j i => n (j.2 i) * k,
            cheaper := ?_, covers := ?_ }⟩
  · simp only [W, Fintype.card_prod, Fintype.card_fin, Fintype.card_fun, pow_add, pow_mul]
    exact Nat.mul_le_mul (Nat.lt_two_pow_self.le) (Nat.pow_le_pow_left Nat.lt_two_pow_self.le r)
  · intro j
    have hs : (∑ i : Fin r, ((n (j.2 i) * k : ℕ) : ℝ) * p (t (j.2 i))) ≤
        ∑ _ : Fin r, ((b : ℝ) * k * L - (m * H + 1)) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [Nat.cast_mul]
      linarith only [hg (j.2 i)]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    push_cast at hs ⊢
    linarith only [hs, (le_max_right _ _).trans_lt hr]
  · have he := hC r
    rw [← pow_mul, expand_word] at he
    exact he

/-- A failed test on one ball gives a local restriction at strictly lower
cost in every branch, including the cost of transmitting the selector. -/
theorem failed_replacement [Nonempty I]
    (T : I → Tensor K S) (hT : ∀ i, T i ≠ 0)
    (p : I → ℝ) (hp : ∀ i, 0 ≤ p i) (s : Finset I) (hL : 0 < ∑ i ∈ s, p i)
    (hpos : ∀ v : Tensor K S →+* ℝ, Monotone v → ∃ i, 1 < v (T i))
    (hfail : ¬ Consistent T p s) (H : ℝ) :
    Nonempty (Replacement (∏ i ∈ s, T i) T p (∑ i ∈ s, p i) H) := by
  obtain ⟨J, _, b, t, n, hb, hc, hv⟩ := failed_offers T hT p hp s hL hpos hfail
  refine replace_aux _ _ _ _ _ (fun j : Option J => j.elim (Classical.arbitrary I) t)
    (fun j => j.elim 0 n) b hb ?_ ?_ ⟨none, rfl⟩
  · rintro (_ | j)
    · simpa using mul_pos (Nat.cast_pos.mpr hb) hL
    · exact hc j
  · intro v h
    obtain ⟨j, hj⟩ := hv v h
    exact ⟨some j, hj⟩

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# A finite menu of local substitutions

Prices may vary on a compact set. Only coordinates of positive price
are demanded. Strict bounds for the selected demands and all branches
persist on an open neighborhood of the original price vector.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral Set

variable {K S I : Type} [Field K] [Fintype S]

structure Proposal (T : I → Tensor K S) (H : ℝ) where
  demand : Finset I
  posted : I → ℝ
  move : Replacement (∏ i ∈ demand, T i) T posted (∑ i ∈ demand, posted i) H

variable {T : I → Tensor K S} {H : ℝ}

namespace Proposal

def cost (q : Proposal T H) (j : q.move.letter) (p : I → ℝ) : ℝ :=
  (∑ i, (q.move.count j i : ℝ) * p (q.move.good j i)) + q.move.bits * H

def Works (q : Proposal T H) (δ : ℝ) (p : I → ℝ) : Prop :=
  (∀ i ∈ q.demand, δ < p i) ∧ ∀ j, q.cost j p < q.move.block * ((∑ i ∈ q.demand, p i) - δ)

theorem Works.mono {q : Proposal T H} {δ ε : ℝ} {p : I → ℝ} (h : q.Works ε p)
    (hδε : δ ≤ ε) : q.Works δ p :=
  ⟨fun i hi => hδε.trans_lt (h.1 i hi), fun j => (h.2 j).trans_le
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hδε _) (Nat.cast_nonneg _))⟩

private theorem open_works (q : Proposal T H) :
    IsOpen {x : ℝ × (I → ℝ) | q.Works x.1 x.2} := by
  simp only [Works, ofPred_and, ofPred_forall]
  apply IsOpen.inter
  · exact isOpen_biInter_finset fun i _ => isOpen_lt continuous_fst ((continuous_apply i).comp continuous_snd)
  · refine isOpen_iInter_of_finite fun j => isOpen_lt ?_ (by fun_prop)
    unfold cost
    fun_prop

private theorem positive_margin (q : Proposal T H)
    (hp : ∀ i ∈ q.demand, 0 < q.posted i) : ∃ δ : ℝ, 0 < δ ∧ q.Works δ q.posted := by
  have ho : IsOpen {δ : ℝ | q.Works δ q.posted} :=
    q.open_works.preimage (continuous_id.prodMk continuous_const)
  have h0 : q.Works 0 q.posted := ⟨hp, fun j => by simpa [cost] using q.move.cheaper j⟩
  obtain ⟨δ, hδ, hs⟩ := Metric.isOpen_iff.mp ho 0 h0
  refine ⟨δ / 2, half_pos hδ, hs ?_⟩
  simpa [Metric.mem_ball, abs_of_pos hδ] using half_lt_self hδ

end Proposal

theorem uniform_move_bound (menu : Finset (Proposal T H)) :
    ∃ C : ℕ, ∀ q ∈ menu, q.move.block ≤ C ∧ ∀ j, ∑ k, q.move.count j k ≤ C := by
  let size (q : Proposal T H) := q.move.block + ∑ j, ∑ k, q.move.count j k
  refine ⟨∑ q ∈ menu, size q, fun q hq => ?_⟩
  have h := Finset.single_le_sum (fun i _ => Nat.zero_le (size i)) hq
  refine ⟨(Nat.le_add_right _ _).trans h, fun j => ?_⟩
  exact (Finset.single_le_sum (f := fun i => ∑ k, q.move.count i k)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ j)).trans ((Nat.le_add_left _ _).trans h)

variable [Nonempty S] [Nonempty I]

/-- At each failing price vector a uniform saving is possible, using
one of finitely many demand sets and restrictions. -/
theorem finite_menu (T : I → Tensor K S) (hT : ∀ i, T i ≠ 0) (s : Finset I)
    (hpos : ∀ v : Tensor K S →+* ℝ, Monotone v → ∃ i, 1 < v (T i))
    (Q : Set (I → ℝ)) (hc : IsCompact Q) (hp : ∀ p ∈ Q, ∀ i, 0 ≤ p i)
    (hn : ∀ p ∈ Q, ∃ i ∈ s, 0 < p i) (hf : ∀ p ∈ Q, ¬ Consistent T p s) (H : ℝ) :
    ∃ menu : Finset (Proposal T H), ∃ δ : ℝ, 0 < δ ∧
      ∀ p ∈ Q, ∃ q ∈ menu, q.demand ⊆ s ∧ q.demand.Nonempty ∧ q.Works δ p := by
  classical
  let J := {q : Proposal T H // q.demand ⊆ s ∧ q.demand.Nonempty} × {δ : ℝ // 0 < δ}
  let U (j : J) := {p : I → ℝ | j.1.val.Works j.2 p}
  have ho (j : J) : IsOpen (U j) :=
    j.1.val.open_works.preimage (continuous_const.prodMk continuous_id)
  have hu : Q ⊆ ⋃ j, U j := by
    intro p h
    let t := s.filter fun i => 0 < p i
    have ht : t.Nonempty := by
      obtain ⟨i, hi, hpi⟩ := hn p h
      exact ⟨i, Finset.mem_filter.mpr ⟨hi, hpi⟩⟩
    have ht' : ∀ i ∈ t, 0 < p i := fun i hi => (Finset.mem_filter.mp hi).2
    have bad : ¬ Consistent T p t := by
      rintro ⟨d, v, hd, hv, hcap, he⟩
      refine hf p h ⟨d, v, hd, hv, hcap, fun i hi => ?_⟩
      by_cases hpi : 0 < p i
      · exact he i (Finset.mem_filter.mpr ⟨hi, hpi⟩)
      · exact le_antisymm (hcap i) ((le_of_not_gt hpi).trans (Tensor.values_nonneg hd hv _))
    obtain ⟨R⟩ := failed_replacement T hT p (hp p h) t (Finset.sum_pos ht' ht) hpos bad H
    let q : Proposal T H := ⟨t, p, R⟩
    obtain ⟨δ, hδ, hq⟩ := q.positive_margin ht'
    exact mem_iUnion.mpr ⟨(⟨q, Finset.filter_subset _ _, ht⟩, ⟨δ, hδ⟩), hq⟩
  obtain ⟨u, h⟩ := hc.elim_finite_subcover U ho hu
  let v := insert 1 (u.image fun j => j.2.val)
  have hv : v.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  refine ⟨u.image (fun j => j.1.val), v.min' hv, ?_, fun p hp => ?_⟩
  · rcases Finset.mem_insert.mp (v.min'_mem hv) with he | he
    · rw [he]; exact zero_lt_one
    · obtain ⟨j, _, hj⟩ := Finset.mem_image.mp he
      exact hj ▸ j.2.property
  · obtain ⟨j, hj, hh⟩ := mem_iUnion₂.mp (h hp)
    have hδ : j.2.val ∈ v := Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hj)
    exact ⟨_, Finset.mem_image_of_mem _ hj, j.1.property.1, j.1.property.2,
      Proposal.Works.mono hh (v.min'_le _ hδ)⟩

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Local price tests with a tolerance

A near match is open in the posted prices, even with no scale bound.
On the compact remainder the finite menu gives a uniform improvement.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral Set

variable {K S I : Type} [Field K] [Fintype S] [Nonempty S] [Fintype I]

def NearPrices (T : I → Tensor K S) (s : Finset I) (ρ : ℝ) (p : I → ℝ) : Prop :=
  ∃ P, (P = 0 ∨ ∃ D, P ∈ Tensor.ordinary K S D) ∧
    (∀ i, P (T i) < p i + ρ) ∧ ∀ i ∈ s, |p i - P (T i)| < ρ

omit [Nonempty S] in
private theorem near_open (T : I → Tensor K S) (s : Finset I) (ρ : ℝ) :
    IsOpen {p | NearPrices T s ρ p} := by
  let J := {P // P = 0 ∨ ∃ D, P ∈ Tensor.ordinary K S D}
  let U (j : J) := {p : I → ℝ | (∀ i, j.val (T i) < p i + ρ) ∧
    ∀ i ∈ s, |p i - j.val (T i)| < ρ}
  have he : {p | NearPrices T s ρ p} = ⋃ j, U j := by
    ext p
    rw [mem_iUnion]
    exact ⟨fun ⟨P, hP, h⟩ => ⟨⟨P, hP⟩, h⟩, fun ⟨j, h⟩ => ⟨j.val, j.property, h⟩⟩
  rw [he]
  refine isOpen_iUnion fun j => ?_
  simp only [U, ofPred_and, ofPred_forall]
  exact (isOpen_iInter_of_finite fun i => isOpen_lt continuous_const (by fun_prop)).inter
    (isOpen_biInter_finset fun i _ => isOpen_lt (by fun_prop) continuous_const)

theorem menu_dichotomy [Nonempty I] (T : I → Tensor K S) (hT : ∀ i, T i ≠ 0)
    (s : Finset I) (hpos : ∀ v : Tensor K S →+* ℝ, Monotone v → ∃ i, 1 < v (T i))
    (a : I → ℝ) (H : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ menu : Finset (Proposal T H), ∃ δ : ℝ, 0 < δ ∧
      ∀ p ∈ Icc 0 a, NearPrices T s ρ p ∨
        ∃ q ∈ menu, q.demand ⊆ s ∧ q.demand.Nonempty ∧ q.Works δ p := by
  let Q := Icc 0 a ∩ {p | NearPrices T s ρ p}ᶜ
  have hc : IsCompact Q := isCompact_Icc.inter_right (near_open T s ρ).isClosed_compl
  have hp : ∀ p ∈ Q, ∀ i, 0 ≤ p i := fun _ h => h.1.1
  have hn (p) (h : p ∈ Q) : ∃ i ∈ s, 0 < p i := by
    by_contra! hz
    refine h.2 ⟨0, .inl rfl, fun i => add_pos_of_nonneg_of_pos (hp p h i) hρ, fun i hi => ?_⟩
    simpa [le_antisymm (hz i hi) (hp p h i)] using hρ
  have hf (p) (h : p ∈ Q) : ¬ Consistent T p s := by
    rintro ⟨d, v, hd, hv, hb, he⟩
    refine h.2 ⟨Tensor.values d v, .inr ⟨d, d, ⟨hd, le_rfl⟩, v, hv, rfl⟩,
      fun i => (hb i).trans_lt (lt_add_of_pos_right _ hρ), fun i hi => ?_⟩
    simpa [he i hi] using hρ
  obtain ⟨m, δ, hd, hm⟩ := finite_menu T hT s hpos Q hc hp hn hf H
  exact ⟨m, δ, hd, fun p hp => (em (NearPrices T s ρ p)).imp_right fun h => hm p ⟨hp, h⟩⟩

variable [DecidableEq S]

/-- A connected core cannot have zero length at every link: it would
transport the full diagonal to a single site at no cost. -/
theorem positive_link (c : S → S → Prop) (hc : ∀ x y, Relation.EqvGen c x y)
    (v : Tensor K S →+* ℝ) (hv : Monotone v) :
    ∃ x y, c x y ∧ 1 < v (Tensor.wire K x y 2) := by
  by_contra! hh
  have hz {x y : S} (h : Relation.EqvGen c x y) : Tensor.dist v x y = 0 := by
    induction h with
    | rel x y h =>
      have he : v (Tensor.wire K x y 2) = 1 := le_antisymm (hh x y h) (by
        simpa using hv (Tensor.one_le_wire K x y (n := 2) (by decide)))
      simp [Tensor.dist, he]
    | refl x => exact Tensor.dist_self _ _
    | symm x y _ ih => rw [Tensor.dist_comm, ih]
    | trans x y z _ _ ih ij =>
      exact le_antisymm (by simpa [ih, ij] using Tensor.dist_triangle v hv x y z)
        (Tensor.dist_nonneg v hv _ _)
  let x := Classical.arbitrary S
  have he := Tensor.price_place_eq v hv id (fun _ => x) (fun s => hz (hc s x))
    (Tensor.shared K Finset.univ 2)
  have h : (Finset.univ.image (fun _ : S => x)) = {x, x} := by ext t; simp [eq_comm]
  rw [Tensor.place_id, Tensor.place_shared, h, Tensor.shared_all] at he
  change v (2 : Tensor K S) = v (Tensor.wire K x x 2) at he
  rw [Tensor.wire_self K x (by decide), map_one, map_ofNat] at he
  norm_num at he

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Repeating a local substitution at a fixed inventory

Only the histogram remains in the outer sum. Sending a selector at
every repetition suffices to pay for all words with that histogram.
The outer alphabet grows polynomially in the repetition count.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset Spectral Stock

def histograms (A : Type) [Fintype A] (m : ℕ) : Finset (A → ℕ) := by
  classical
  exact (Fintype.piFinset (fun _ : A => range (m + 1))).filter (fun t => ∑ i, t i = m)

theorem mem_histograms {A : Type} [Fintype A] {m : ℕ} {t : A → ℕ} :
    t ∈ histograms A m ↔ ∑ i, t i = m := by
  classical
  rw [histograms, mem_filter]
  refine ⟨And.right, fun h => ⟨Fintype.mem_piFinset.mpr fun i => ?_, h⟩⟩
  exact mem_range.mpr (Nat.lt_succ_of_le
    ((single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ i)).trans_eq h))

theorem card_histograms (A : Type) [Fintype A] (m : ℕ) :
    (histograms A m).card ≤ (m + 1) ^ Fintype.card A := by
  classical
  unfold histograms
  refine (card_filter_le _ _).trans_eq ?_
  simp

variable {K S I : Type} [Field K] [Fintype S] [Nonempty S]

omit [Nonempty S] in
/-- Bound each word by its inventory and pay separately for the selector words. -/
theorem word_bound {A : Type} [Fintype A] (V : A → Tensor K S) (m : ℕ)
    {X : Tensor K S} (hX : ∀ h ∈ histograms A m, bundle V h ≤ X) :
    (∑ i, V i) ^ m ≤ (Fintype.card A : Tensor K S) ^ m * X := by
  classical
  let : AddLeftMono (Tensor K S) :=
    ⟨fun c a b h => by rw [add_comm c a, add_comm c b]; exact Tensor.add_le_add_right _ _ _ h⟩
  calc
    _ = ∑ f : Fin m → A, ∏ j, V (f j) := Fintype.sum_pow _ _
    _ ≤ ∑ _ : Fin m → A, X := sum_le_sum fun f _ => by
      let t (i : A) := (univ.filter (fun j => f j = i)).card
      have ht : t ∈ histograms A m := by
        apply mem_histograms.mpr
        simpa only [card_univ, Fintype.card_fin] using
          (card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := f) (by simp)).symm
      have h : (∏ j, V (f j)) = bundle V t := by
        rw [← prod_fiberwise' univ f V]
        simp only [prod_const, bundle, t]
      rw [h]
      exact hX t ht
    _ = _ := by simp [nsmul_eq_mul]

namespace Proposal

variable {T : I → Tensor K S} {H : ℝ} [DecidableEq I] (q : Proposal T H)

def orders (j : q.move.letter) : I → ℕ := collect (q.move.good j) (q.move.count j)

def output (u : Finset I) (m : ℕ) (h : q.move.letter → ℕ) (i : I) : ℕ :=
  copies u (q.move.bits * m) i + ∑ j, q.orders j i * h j

variable [Fintype I]

/-- A comparison of selector inventories suffices to scale a whole batch. -/
theorem batch_scaled (u : Finset I) (hu : (2 : Tensor K S) ≤ ∏ i ∈ u, T i)
    (m n z : ℕ) (hmn : m ≤ n)
    (hcover : ∀ t ∈ histograms q.move.letter (m * z), ∃ h ∈ histograms q.move.letter n,
      bundle (fun j => bundle T (q.orders j)) t ≤ (bundle (fun j => bundle T (q.orders j)) h) ^ z) :
    (bundle T (copies q.demand (q.move.block * m))) ^ z ≤
      ∑ h ∈ histograms q.move.letter n, (bundle T (q.output u n h)) ^ z := by
  classical
  let : MulLeftMono (Tensor K S) := ⟨fun c a b h => Tensor.mul_le_mul_left _ _ _ h⟩
  let : AddLeftMono (Tensor K S) :=
    ⟨fun c a b h => by rw [add_comm c a, add_comm c b]; exact Tensor.add_le_add_right _ _ _ h⟩
  let V j := bundle T (q.orders j)
  have hv (j) : V j = ∏ k, T (q.move.good j k) ^ q.move.count j k :=
    bundle_collect T (q.move.good j) (q.move.count j)
  have h : (∏ i ∈ q.demand, T i) ^ q.move.block ≤ ∑ j, V j := by
    simp only [hv]
    exact q.move.covers
  have hc : (Fintype.card q.move.letter : Tensor K S) ≤ (∏ i ∈ u, T i) ^ q.move.bits := by
    refine (Tensor.natCast_le q.move.fits).trans ?_
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_left' hu _
  let X := ∑ h ∈ histograms q.move.letter n, (bundle V h) ^ z
  have hX (t) (ht : t ∈ histograms q.move.letter (m * z)) : bundle V t ≤ X := by
    obtain ⟨r, hr, htr⟩ := hcover t ht
    exact htr.trans (single_le_sum (f := fun h => (bundle V h) ^ z) (fun _ _ => Tensor.zero_le _) hr)
  have h₁ : 1 ≤ ∏ i ∈ u, T i := by
    have h₂ := Tensor.natCast_le (K := K) (S := S) (by decide : 1 ≤ 2)
    rw [Nat.cast_one, Nat.cast_ofNat] at h₂
    exact h₂.trans hu
  have hp := pow_le_pow_left' h₁ q.move.bits
  rw [one_pow] at hp
  rw [bundle_copies, pow_mul, ← pow_mul _ m z]
  refine ((pow_le_pow_left' h (m * z)).trans (word_bound V (m * z) hX)).trans ?_
  have hh := (pow_le_pow_left' hc (m * z)).trans (pow_le_pow_right' hp (Nat.mul_le_mul_right z hmn))
  refine (mul_le_mul_left hh X).trans_eq ?_
  unfold X
  rw [mul_sum]
  apply sum_congr rfl
  intro t _
  unfold output
  rw [bundle_add, bundle_copies, bundle_sum, mul_pow, pow_mul, pow_mul]
  rfl

theorem batch (u : Finset I) (hu : (2 : Tensor K S) ≤ ∏ i ∈ u, T i) (m : ℕ) :
    bundle T (copies q.demand (q.move.block * m)) ≤
      ∑ h ∈ histograms q.move.letter m, bundle T (q.output u m h) := by
  simpa only [pow_one] using q.batch_scaled u hu m m 1 le_rfl
    (fun t ht => ⟨t, by simpa using ht, by rw [pow_one]; exact le_refl _⟩)

omit [Nonempty S] in
theorem batch_cost (u : Finset I) (p : I → ℝ) {δ : ℝ}
    (hw : q.Works δ p) (hu : ∑ i ∈ u, p i ≤ H)
    {m : ℕ} {h : q.move.letter → ℕ} (hh : h ∈ histograms q.move.letter m) :
    total p (q.output u m h) ≤ (q.move.block * m : ℕ) * ((∑ i ∈ q.demand, p i) - δ) := by
  have hh' : ∑ j, (h j : ℝ) = m := by exact_mod_cast mem_histograms.mp hh
  let v := (∑ i ∈ q.demand, p i) - δ
  have hj (j : q.move.letter) : total p (q.orders j) ≤ q.move.block * v - q.move.bits * H := by
    rw [orders, total_collect]
    exact (le_sub_iff_add_le).mpr (hw.2 j).le
  unfold output
  rw [total_add, total_copies, total_sum]
  calc
    _ ≤ (q.move.bits * m : ℕ) * H + ∑ j, (q.move.block * v - q.move.bits * H) * (h j : ℝ) :=
      add_le_add (mul_le_mul_of_nonneg_left hu (Nat.cast_nonneg _))
        (sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hj j) (Nat.cast_nonneg _))
    _ = _ := by rw [← mul_sum, hh']; unfold v; push_cast; ring

end Proposal
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! # An inventory change with an outcome-dependent supply -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

structure Intervention (I E : Type) where
  choice : Type
  [finiteChoice : Fintype choice]
  take : I → ℕ
  put : choice → I → ℕ
  core : choice → E → ℕ

attribute [instance] Intervention.finiteChoice

namespace Intervention

variable {I E : Type} (q : Intervention I E)

def next (z : I → ℕ) (j : q.choice) (i : I) := z i - q.take i + q.put j i

def cost [Fintype E] (j : q.choice) : ℕ := ∑ e, q.core j e

open Spectral Stock

variable {K S : Type} [Field K] [Fintype S] [Fintype I] [Fintype E]

def Covers (T : I → Tensor K S) (V : E → Tensor K S) : Prop :=
  bundle T q.take ≤ ∑ j, bundle T (q.put j) * bundle V (q.core j)

theorem covers_next {T : I → Tensor K S} {V : E → Tensor K S} (h : q.Covers T V)
    (z : I → ℕ) (hz : q.take ≤ z) :
    bundle T z ≤ ∑ j, bundle T (q.next z j) * bundle V (q.core j) := by
  let x := fun i => z i - q.take i
  calc
    _ = bundle T x * bundle T q.take := by
      rw [← bundle_add, show (fun i => x i + q.take i) = z from funext fun i => Nat.sub_add_cancel (hz i)]
    _ ≤ bundle T x * ∑ j, bundle T (q.put j) * bundle V (q.core j) := Tensor.mul_le_mul_left _ _ _ h
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_assoc, ← bundle_add]
      rfl

end Intervention
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! # Posting a batch of local orders to a shared inventory -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Spectral Stock Finset

variable {I E J : Type} [Fintype I] [Fintype E] [Fintype J]

namespace Intervention

/-- Linear saving for each outcome, and the per-commodity volume limit.
Only positive-price stock may be consumed. -/
def Efficient (q : Intervention I E) (p : I → ℝ) (δ : ℝ) (B m : ℕ) : Prop :=
  (∀ i, q.take i ≤ B * m ∧ (q.take i ≠ 0 → δ ≤ p i)) ∧
  ∀ j, (∀ i, q.put j i ≤ B * m) ∧
    total p (q.put j) + q.cost j + m * δ ≤ total p q.take

def affects (q : Intervention I E) (i : I) : Prop :=
  q.take i ≠ 0 ∨ ∃ j, q.put j i ≠ 0

end Intervention

namespace Stock

omit [Fintype I] in
theorem collect_nonzero [DecidableEq I] {g : J → I} {x : J → ℕ} {i : I}
    (h : collect g x i ≠ 0) : ∃ j, g j = i ∧ x j ≠ 0 := by
  obtain ⟨j, hj, hn⟩ := exists_ne_zero_of_sum_ne_zero h
  exact ⟨j, (mem_filter.mp hj).2, hn⟩

omit [Fintype I] in
theorem collect_inj [DecidableEq I] {g : J → I} (hg : Function.Injective g)
    (x : J → ℕ) (j : J) : collect g x (g j) = x j := by
  unfold collect
  exact sum_eq_single j (fun k hk hn => (hn (hg (mem_filter.mp hk).2)).elim) (by simp)

theorem total_split (p : I → ℝ) (x : I ⊕ E → ℕ) :
    total (Sum.elim p (fun _ => 1)) x = total p (x ∘ Sum.inl) + (∑ e, x (.inr e) : ℕ) := by
  simp [total, Fintype.sum_sum_type]

theorem bundle_split {R : Type*} [CommMonoid R] (T : I ⊕ E → R) (x : I ⊕ E → ℕ) :
    bundle T x = bundle (T ∘ Sum.inl) (x ∘ Sum.inl) * bundle (T ∘ Sum.inr) (x ∘ Sum.inr) :=
  Fintype.prod_sum_type _

end Stock

namespace Proposal

variable {K S : Type} [Field K] [Fintype S] {T : J → Tensor K S} {H : ℝ}
  [DecidableEq I] [DecidableEq E] [DecidableEq J]
  (q : Proposal T H) (g : J → I ⊕ E) (u : Finset J) (m : ℕ)

def trade : Intervention I E where
  choice := ↥(histograms q.move.letter m)
  take := collect g (copies q.demand (q.move.block * m)) ∘ Sum.inl
  put j := collect g (q.output u m j.val) ∘ Sum.inl
  core j := collect g (q.output u m j.val) ∘ Sum.inr

omit [Fintype I] [Fintype E] in
theorem trade_support {i : I} (h : (q.trade g u m).affects i) : ∃ j, g j = .inl i := by
  rcases h with h | ⟨_, h⟩ <;>
    obtain ⟨j, hj, _⟩ := collect_nonzero h <;> exact ⟨j, hj⟩

omit [Fintype I] [Fintype E] in
theorem take_core (hd : ∀ j ∈ q.demand, ∃ i, g j = .inl i) (e : E) :
    collect g (copies q.demand (q.move.block * m)) (.inr e) = 0 := by
  by_contra h
  obtain ⟨j, hj, hn⟩ := collect_nonzero h
  obtain ⟨i, hi⟩ := hd j (by by_contra h; simp [copies, h] at hn)
  rw [hi] at hj
  contradiction

theorem trade_efficient (hg : Function.Injective g)
    (hd : ∀ j ∈ q.demand, ∃ i, g j = .inl i)
    (hu : ∀ j ∈ u, ∃ e, g j = .inr e) (hc : (u.card : ℝ) ≤ H)
    {p : I → ℝ} {δ : ℝ} (hδ : 0 ≤ δ)
    (hw : q.Works δ (Sum.elim p (fun _ => 1) ∘ g))
    {B : ℕ} (hb : q.move.block ≤ B) (ho : ∀ j, ∑ k, q.move.count j k ≤ B) :
    (q.trade g u m).Efficient p δ B m := by
  let P : I ⊕ E → ℝ := Sum.elim p (fun _ => 1)
  have hcore : ∑ i ∈ u, (P ∘ g) i ≤ H := by
    refine le_trans ?_ hc
    rw [show (u.card : ℝ) = ∑ _ ∈ u, (1 : ℝ) by simp]
    apply sum_le_sum
    intro j hj
    obtain ⟨e, he⟩ := hu j hj
    simp [P, he]
  constructor
  · intro i
    by_cases hz : (q.trade g u m).take i = 0
    · simp [hz]
    obtain ⟨j, hj, hne⟩ := collect_nonzero hz
    have hjd : j ∈ q.demand := by by_contra h; simp [copies, h] at hne
    refine ⟨?_, fun _ => ?_⟩
    · change collect g _ (.inl i) ≤ _
      rw [← hj, collect_inj hg, copies, ite_eq_left hjd]
      exact Nat.mul_le_mul_right m hb
    · simpa [hj] using (hw.1 j hjd).le
  intro h
  constructor
  · intro i
    by_cases hz : (q.trade g u m).put h i = 0
    · simp [hz]
    obtain ⟨j, hj, _⟩ := collect_nonzero hz
    have hju : j ∉ u := by
      intro hj'
      obtain ⟨e, he⟩ := hu j hj'
      rw [hj] at he
      contradiction
    change collect g _ (.inl i) ≤ _
    rw [← hj, collect_inj hg, output, copies, ite_eq_right hju, zero_add]
    calc
      _ ≤ ∑ k, B * h.val k := by
        apply sum_le_sum
        intro k _
        apply Nat.mul_le_mul_right
        exact (sum_le_sum_of_subset (filter_subset _ _)).trans (ho k)
      _ = _ := by rw [← mul_sum, mem_histograms.mp h.property]
  · have hs := q.batch_cost u (P ∘ g) hw hcore h.property
    have hy : total p (q.trade g u m).take = (q.move.block * m : ℕ) * ∑ j ∈ q.demand, (P ∘ g) j := by
      rw [← total_copies, ← total_collect, total_split]
      simp only [q.take_core g m hd, sum_const_zero, Nat.cast_zero, add_zero]
      rfl
    rw [← total_collect, total_split] at hs
    change total p ((q.trade g u m).put h) + (q.trade g u m).cost h ≤ _ at hs
    have hm : (m : ℝ) ≤ (q.move.block * m : ℕ) := by
      exact_mod_cast Nat.le_mul_of_pos_left m q.move.positive
    linarith only [hs, hy, mul_le_mul_of_nonneg_right hm hδ]

end Proposal
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Simultaneous inventory changes

Bounded overlap suffices. A smaller batch per center allows all
selected centers to act simultaneously, without choosing a packing.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Intervention

open Stock Spectral Finset

variable {I E J : Type} [Fintype I] [Fintype E] [Fintype J] [DecidableEq J]
variable (q : J → Intervention I E)

def parallel : Intervention I E where
  choice := ∀ j, (q j).choice
  take i := ∑ j, (q j).take i
  put u i := ∑ j, (q j).put (u j) i
  core u e := ∑ j, (q j).core (u j) e

def Overlap (N : ℕ) : Prop :=
  ∀ i, ∃ U : Finset J, U.card ≤ N ∧ ∀ j, (q j).affects i → j ∈ U

theorem parallel_covers {K S : Type} [Field K] [Fintype S]
    {T : I → Tensor K S} {V : E → Tensor K S} (h : ∀ j, (q j).Covers T V) :
    (parallel q).Covers T V := by
  let : MulLeftMono (Tensor K S) := ⟨fun c a b h => Tensor.mul_le_mul_left _ _ _ h⟩
  have hb {A : Type} [Fintype A] (t : A → Tensor K S) (z : J → A → ℕ) :
      bundle t (fun i => ∑ j, z j i) = ∏ j, bundle t (z j) := by
    simpa only [mul_one, pow_one] using bundle_sum t z (fun _ => 1)
  unfold Covers parallel
  simp only [hb, ← prod_mul_distrib]
  rw [← Fintype.prod_sum (fun j c => bundle T ((q j).put c) * bundle V ((q j).core c))]
  exact prod_le_prod fun j _ => h j

theorem parallel_bounds {N B m : ℕ} {p : I → ℝ} {δ : ℝ}
    (ho : Overlap q N) (h : ∀ j, (q j).Efficient p δ B m) (i : I) :
    (parallel q).take i ≤ N * (B * m) ∧ ((parallel q).take i ≠ 0 → δ ≤ p i) ∧
      ∀ u, (parallel q).put u i ≤ N * (B * m) := by
  obtain ⟨U, hu, hl⟩ := ho i
  have bound (f : J → ℕ) (hf : ∀ j, f j ≤ B * m) (hs : ∀ j, f j ≠ 0 → (q j).affects i) :
      ∑ j, f j ≤ N * (B * m) := by
    rw [← sum_subset (subset_univ U) (fun j _ hj => Classical.byContradiction
      (fun h => hj (hl j (hs j h))))]
    refine (sum_le_sum (fun j _ => hf j)).trans ?_
    simpa using Nat.mul_le_mul_right (B * m) hu
  refine ⟨bound _ (fun j => ((h j).1 i).1) (fun _ => Or.inl), ?_, ?_⟩
  · intro ht
    obtain ⟨j, _, hj⟩ := exists_ne_zero_of_sum_ne_zero ht
    exact ((h j).1 i).2 hj
  · intro u
    exact bound _ (fun j => ((h j).2 (u j)).1 i) (fun j h => .inr ⟨u j, h⟩)

theorem parallel_saving {B m : ℕ} {p : I → ℝ} {δ : ℝ}
    (h : ∀ j, (q j).Efficient p δ B m) (u : (parallel q).choice) :
    total p ((parallel q).put u) + (parallel q).cost u + Fintype.card J * ((m : ℝ) * δ) ≤
      total p (parallel q).take := by
  have hp (z : J → I → ℕ) : total p (fun i => ∑ j, z j i) = ∑ j, total p (z j) := by
    simpa using total_sum p z (fun _ => 1)
  have hc : (parallel q).cost u = ∑ j, (q j).cost (u j) := sum_comm
  rw [hc, Nat.cast_sum]
  change total p (fun i => ∑ j, (q j).put (u j) i) + _ + _ ≤ total p (fun i => ∑ j, (q j).take i)
  rw [hp, hp]
  simpa only [sum_add_distrib, sum_const, card_univ, nsmul_eq_mul] using
    sum_le_sum (s := univ) (fun j _ => ((h j).2 (u j)).2)

/-- The account drops by the linear saving minus a quadratic error. -/
theorem parallel_change {N B m M : ℕ} (d : I → ℕ) (hd : ∀ i, d i ≤ M) {a : I → ℝ} {z : I → ℕ} {μ δ : ℝ} (hμ : 0 < μ)
    (ho : Overlap q N) (h : ∀ j, (q j).Efficient (fun i => price μ (a i) (z i)) δ B m)
    (hs : (N * (B * m) : ℕ) ≤ μ * δ) :
    (parallel q).take ≤ z ∧ ∀ u,
      potential μ a ((parallel q).next z u + d) + (parallel q).cost u +
        Fintype.card J * ((m : ℝ) * δ) ≤
        potential μ a z + total (fun i => price μ (a i) (z i)) d +
          Fintype.card I * (((N * (B * m) : ℕ) : ℝ) + M) ^ 2 / (2 * μ) := by
  let Q := parallel q
  let t : ℝ := (N * (B * m) : ℕ)
  have ht (i) : (Q.take i : ℝ) ≤ t := Nat.cast_le.mpr (parallel_bounds q ho h i).1
  have hz : Q.take ≤ z := by
    intro i
    by_cases he : Q.take i = 0
    · simp [he]
    apply (Nat.cast_le (α := ℝ)).mp
    refine (ht i).trans (hs.trans ?_)
    exact (mul_le_mul_of_nonneg_left ((parallel_bounds q ho h i).2.1 he) hμ.le).trans
      (mul_price_le hμ)
  refine ⟨hz, fun u => ?_⟩
  let p i := price μ (a i) (z i)
  let y := Q.next z u + d
  have diff (i) : (y i : ℝ) - z i = (Q.put u i : ℝ) - Q.take i + d i := by
    simp only [y, Pi.add_apply, next, Nat.cast_add, Nat.cast_sub (hz i)]
    ring
  have linear : (∑ i, p i * ((y i : ℝ) - z i)) = total p (Q.put u) - total p Q.take + total p d := by
    simp only [diff, total, ← sum_sub_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun _ _ => by ring
  have error : (∑ i, ((y i : ℝ) - z i) ^ 2) ≤ Fintype.card I * (t + M) ^ 2 := by
    rw [show (Fintype.card I : ℝ) * (t + M) ^ 2 = ∑ _ : I, (t + M) ^ 2 by simp]
    apply sum_le_sum
    intro i _
    rw [diff]
    have hk : (Q.put u i : ℝ) ≤ t := Nat.cast_le.mpr ((parallel_bounds q ho h i).2.2 u)
    have hi : (d i : ℝ) ≤ M := Nat.cast_le.mpr (hd i)
    nlinarith only [hk, ht i, hi, Nat.cast_nonneg (α := ℝ) (Q.take i), Nat.cast_nonneg (α := ℝ) (Q.put u i),
      Nat.cast_nonneg (α := ℝ) (d i)]
  have inc := potential_increment (z := z) (y := y) (a := a) hμ
  rw [linear] at inc
  have red := parallel_saving q h u
  change total p (Q.put u) + Q.cost u + _ ≤ total p Q.take at red
  change potential μ a y + Q.cost u + _ ≤ potential μ a z + total p d + Fintype.card I * (t + M) ^ 2 / (2 * μ)
  linarith only [inc, red, div_le_div_of_nonneg_right error (by positivity : 0 ≤ 2 * μ)]

theorem parallel_gain {N B m : ℕ} {a : I → ℝ} {z : I → ℕ} {μ δ : ℝ} (hμ : 0 < μ)
    (ho : Overlap q N) (h : ∀ j, (q j).Efficient (fun i => price μ (a i) (z i)) δ B m)
    (hs : (N * (B * m) : ℕ) ≤ μ * δ) :
    (parallel q).take ≤ z ∧ ∀ u,
      potential μ a ((parallel q).next z u) + (parallel q).cost u +
        Fintype.card J * ((m : ℝ) * δ) ≤
        potential μ a z + Fintype.card I * (N * (B * m) : ℕ) ^ 2 / (2 * μ) := by
  simpa [total] using parallel_change q 0 (M := 0) (fun _ => le_rfl) hμ ho h hs

end OAI.LinearAlgebra.MatrixExponent.Routing.Intervention
end

/-!
# Paying for an inventory protocol

Reserve the payload not yet injected. Injecting a tranche only changes
the accounting, since all reserved copies are present in the actual
inventory. Only interventions create branches. The initial account and
the saving per intervention give a uniform depth bound.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset Stock

variable {I E : Type} [Fintype I] [Fintype E]

inductive Plan (a : I → ℝ) (P : Intervention I E → Prop) (budget : ℝ) :
    ℕ → (I → ℕ) → ℝ → Prop
  | close {k z u} : u + total a z ≤ budget → Plan a P budget k z u
  | step {k z u} (q : Intervention I E) : P q → q.take ≤ z →
      (∀ j, Plan a P budget k (q.next z j) (u + q.cost j)) → Plan a P budget (k + 1) z u

variable [DecidableEq I] {a : I → ℝ} {μ C : ℝ} (L : Finset I)

private theorem injection (z : I → ℕ) (n : ℕ) (hμ : 0 < μ) (hn : (n : ℝ) ≤ μ)
    (hp : ∑ i ∈ L, price μ (a i) (z i) ≤ C * L.card) :
    potential μ a (z + copies L n) ≤ potential μ a z + (C + 1) * L.card * n := by
  let p i := price μ (a i) (z i)
  have hi (i : I) : value μ (a i) ((z + copies L n) i) ≤
      value μ (a i) (z i) + (if i ∈ L then (p i + 1) * n else 0) := by
    by_cases h : i ∈ L
    · simp only [Pi.add_apply, copies, ite_eq_left h, Nat.cast_add]
      refine (value_increment (z := (z i : ℝ)) hμ).trans ?_
      have he : (n : ℝ) ^ 2 / (2 * μ) ≤ n := by
        rw [div_le_iff₀ (by positivity)]
        nlinarith [Nat.cast_nonneg (α := ℝ) n]
      simp only [add_sub_cancel_left]
      unfold p
      linarith
    · simp [copies, h]
  have h := sum_le_sum (s := univ) fun i _ => hi i
  simp only [sum_add_distrib, sum_ite_mem, univ_inter, ← sum_mul, sum_const,
    nsmul_eq_mul, mul_one] at h
  change potential μ a _ ≤ potential μ a _ + _ at h
  exact h.trans (by gcongr; linarith)

theorem plan {P : Intervention I E → Prop} (w k : ℕ) (hμ : 1 ≤ μ)
    (ha : ∀ i, 0 ≤ a i) (hC : 0 ≤ C) {s : ℝ}
    (hcap : μ * (∑ i, a i ^ 2) ≤ 2 * L.card * w)
    (hk : (C + 1) * L.card * w < k * s)
    (act : ∀ z : I → ℕ, C * L.card < ∑ i ∈ L, price μ (a i) (z i) →
      ∃ q, P q ∧ q.take ≤ z ∧ ∀ j,
        potential μ a (q.next z j) + q.cost j + s ≤ potential μ a z) :
    Plan a P ((C + 2) * L.card * w) k (copies L w) 0 := by
  let r := (C + 1) * (L.card : ℝ)
  have hμ' : 0 < μ := lt_of_lt_of_le zero_lt_one hμ
  have aux (t : ℕ) : ∀ v : ℕ, ∀ (z : I → ℕ) (u : ℝ),
      potential μ a z + r * v < t * s →
      u + potential μ a z + r * v ≤ r * w →
      Plan a P ((C + 2) * L.card * w) t (z + copies L v) u := by
    induction t with
    | zero =>
      intro v z u h _
      simp only [Nat.cast_zero, zero_mul] at h
      exact (h.not_ge (add_nonneg (potential_nonneg hμ' ha) (by unfold r; positivity))).elim
    | succ t ih =>
      intro v
      induction v using Nat.strong_induction_on with
      | h v prev =>
        intro z u ht hu
        by_cases hv : v = 0
        · subst v
          rw [show copies L 0 = 0 by ext i; simp [copies], add_zero]
          apply Plan.close
          have h : total a z ≤ potential μ a z + μ * (∑ i, a i ^ 2) / 2 := by
            simpa only [total, mul_comm] using potential_close (z := z) (a := a) hμ'
          simp only [Nat.cast_zero, mul_zero, add_zero, r] at hu
          linarith only [hu, h, hcap]
        by_cases hp : ∑ i ∈ L, price μ (a i) (z i) ≤ C * L.card
        · let n := min v ⌊μ⌋₊
          have hn0 : 0 < n := lt_min (by omega) (Nat.floor_pos.mpr hμ)
          have hnv : n ≤ v := min_le_left _ _
          have hn : (n : ℝ) ≤ μ := (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le hμ'.le)
          have hin := injection L z n hμ' hn hp
          change _ ≤ potential μ a z + r * n at hin
          have he : z + copies L v = (z + copies L n) + copies L (v - n) := by
            funext i
            by_cases e : i ∈ L <;> simp [copies, e]
            omega
          rw [he]
          apply prev (v - n) (by omega)
          · rw [Nat.cast_sub hnv]
            linarith only [hin, ht]
          · rw [Nat.cast_sub hnv]
            linarith only [hin, hu]
        · obtain ⟨q, hq, hz, hd⟩ := act z (lt_of_not_ge hp)
          apply Plan.step (z := z + copies L v) q hq (fun i => (hz i).trans (Nat.le_add_right _ _))
          intro j
          have he : q.next (z + copies L v) j = q.next z j + copies L v := by
            funext i
            have htake : q.take i ≤ z i := hz i
            simp only [Intervention.next, Pi.add_apply]
            omega
          rw [he]
          apply ih
          · rw [Nat.cast_succ] at ht
            linarith only [ht, hd j, Nat.cast_nonneg (α := ℝ) (q.cost j)]
          · have hs : 0 ≤ s := by
              by_contra! bad
              have : 0 ≤ (C + 1) * (L.card : ℝ) * w := by positivity
              exact (this.trans_lt hk).not_ge (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) bad.le)
            linarith only [hu, hd j, hs]
  simpa using aux k w 0 0 (by simpa only [potential_zero ha, zero_add] using hk)
    (by simp [potential_zero ha])

end OAI.LinearAlgebra.MatrixExponent.Routing
end
