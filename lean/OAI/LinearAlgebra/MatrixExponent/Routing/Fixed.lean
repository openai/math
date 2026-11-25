import OAI.LinearAlgebra.MatrixExponent.Routing.Round
import OAI.LinearAlgebra.MatrixExponent.Control.BucketNet
import OAI.LinearAlgebra.MatrixExponent.Control.Ranks
import OAI.LinearAlgebra.MatrixExponent.Control.Address
import OAI.LinearAlgebra.MatrixExponent.Install.Products
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryComparison
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Decor
import OAI.LinearAlgebra.MatrixExponent.Routing.Parameters
import OAI.LinearAlgebra.MatrixExponent.Control.Named
import OAI.LinearAlgebra.MatrixExponent.Install.SumOut

section
/-! # Rounding repetition counts for a scalable substitution -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Finset

variable {A : Type} [Fintype A] [DecidableEq A]

/-- Round each count up to a whole block, charging one extra block per
letter. Put the unused budget on the distinguished letter. -/
def rounded (a₀ : A) (m z : ℕ) (t : A → ℕ) (a : A) : ℕ :=
  t a / z + 1 + if a = a₀ then m - ∑ j, t j / z else 0

theorem rounded_mem (a₀ : A) {m z : ℕ} (hz : 0 < z)
    {t : A → ℕ} (ht : t ∈ histograms A (m * z)) :
    rounded a₀ m z t ∈ histograms A (m + Fintype.card A) := by
  have hs : ∑ a, t a / z ≤ m := by
    apply Nat.le_of_mul_le_mul_right _ hz
    rw [sum_mul, ← mem_histograms.mp ht]
    exact sum_le_sum fun a _ => Nat.div_mul_le_self _ _
  apply mem_histograms.mpr
  simp only [rounded, sum_add_distrib, sum_const, card_univ, nsmul_eq_mul, Nat.cast_id,
    mul_one, sum_ite_eq', mem_univ, ite_true]
  omega

theorem rounded_covers (a₀ : A) (m : ℕ) {z : ℕ} (hz : 0 < z) (t : A → ℕ) (a : A) :
    t a ≤ rounded a₀ m z t a * z := by
  rw [mul_comm]
  exact (Nat.lt_mul_div_succ _ hz).le.trans (Nat.mul_le_mul_left z (Nat.le_add_right _ _))

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Local coefficients of a rounded substitution

Occurrences of each letter use consecutive addresses. All addresses
left over after rounding contract to the scalar one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.WordSum

open Finset Control

variable {K S X Y A : Type} [Field K] [Fintype A] [DecidableEq A] {n : ℕ}

def profile (a₀ : A) (m z : ℕ) (w : Fin n → A) : A → ℕ :=
  rounded a₀ m z (fun a => histogram w a none)

theorem profile_mem (a₀ : A) {m z : ℕ} (hn : n = m * z) (hz : 0 < z) (w : Fin n → A) :
    profile a₀ m z w ∈ histograms A (m + Fintype.card A) := by
  apply rounded_mem a₀ hz
  rw [mem_histograms, ← hn]
  simpa only [histogram_none, card_univ, Fintype.card_fin] using
    (card_eq_sum_card_fiberwise (s := univ) (t := univ) (f := w) (by simp)).symm

abbrev Address (z : ℕ) (t : A → ℕ) := Σ a : A, Fin (t a * z)

variable [Inhabited Y]

/-- Values on out-of-range addresses only matter for rejected profiles. -/
def factor (L : A → S → X → Y → K) (U : A → S → Y → K)
    (z : ℕ) (w : Fin n → A) (t : A → ℕ) (s : S) (x : Fin n → X) (y : Address z t → Y) : K :=
  (∏ i, L (w i) s (x i) (if h : rank w i < t (w i) * z then y ⟨w i, ⟨rank w i, h⟩⟩ else default)) *
    ∏ u : Address z t, if histogram w u.1 none ≤ u.2.val then U u.1 s (y u) else 1

variable [Fintype S] [DecidableEq S] [Fintype Y]
  (P : A → (S → Y) → K) (L : A → S → X → Y → K) (U : A → S → Y → K)
  (hU : ∀ a, ∑ y, (∏ s, U a s (y s)) * P a y = 1)

include hU in
private theorem contract (w : Fin n → A) {z : ℕ} (t : A → ℕ)
    (ht : ∀ a, histogram w a none ≤ t a * z) (x : Fin n → S → X) :
    (∑ y : Address z t → S → Y,
      (∏ s, factor L U z w t s (fun i => x i s) (fun u => y u s)) * ∏ u, P u.1 (y u)) =
      ∏ i, ∑ y, (∏ s, L (w i) s (x i s) (y s)) * P (w i) y := by
  classical
  have ok (i) := (rank_lt w i).trans_le (ht (w i))
  let send (i : Fin n) : Address z t := ⟨w i, ⟨rank w i, ok i⟩⟩
  have inj : Function.Injective send := fun i j h =>
    rank_injective w (congrArg (fun u : Address z t => (u.1, u.2.val)) h)
  let unused (u : Address z t) := histogram w u.1 none ≤ u.2.val
  have used (i) : ¬ unused (send i) := (rank_lt w i).not_ge
  have spare {u} (hu : u ∉ univ.image send) : unused u := by
    by_contra h
    obtain ⟨i, hi, hr⟩ := (rank_range w u.1 u.2.val).mpr (lt_of_not_ge h)
    refine hu (mem_image.mpr ⟨i, mem_univ _, Sigma.ext hi ?_⟩)
    exact (Fin.heq_ext_iff (congrArg (fun a => t a * z) hi)).mpr hr
  let row (s : S) (u : Address z t) (v : Y) :=
    (∏ i, if send i = u then L (w i) s (x i s) v else 1) *
      if unused u then U u.1 s v else 1
  have split (s) (y : Address z t → Y) :
      factor L U z w t s (fun i => x i s) y = ∏ u, row s u (y u) := by
    unfold row
    rw [prod_mul_distrib, prod_comm]
    simp only [factor, dite_eq_left (ok _), prod_ite_eq, mem_univ, ite_true]
    rfl
  let weight (u : Address z t) (v : S → Y) := (∏ s, row s u (v s)) * P u.1 v
  have factors (y : Address z t → S → Y) :
      (∏ s, factor L U z w t s (fun i => x i s) (fun u => y u s)) * (∏ u, P u.1 (y u)) =
        ∏ u, weight u (y u) := by
    simp_rw [split]
    rw [prod_comm, ← prod_mul_distrib]
  simp_rw [factors]
  rw [← Fintype.prod_sum weight]
  have empty (u) (_ : u ∈ univ) (hu : u ∉ univ.image send) : ∑ y, weight u y = 1 := by
    have hne (i) : send i ≠ u := fun he => hu (mem_image.mpr ⟨i, mem_univ _, he⟩)
    simpa only [weight, row, hne, ite_false, prod_const_one, spare hu, ite_true, one_mul] using hU u.1
  rw [← prod_subset (subset_univ _) empty, prod_image inj.injOn]
  apply prod_congr rfl
  intro i _
  simp only [weight, row, inj.eq_iff, prod_ite_eq', mem_univ, ite_true, used, ite_false, mul_one]
  rfl

include hU in
/-- Separate the outer histogram from the selector word. Exactly one
histogram contributes per word. The identity does not divide by a
multiplicity and holds in positive characteristic. -/
theorem expand (T : (S → X) → K)
    (hT : ∀ x, T x = ∑ a, ∑ y, (∏ s, L a s (x s) (y s)) * P a y)
    (a₀ : A) {m z : ℕ} (hn : n = m * z) (hz : 0 < z) (x : Fin n → S → X) :
    (∏ i, T (x i)) =
      ∑ t : ↥(histograms A (m + Fintype.card A)), ∑ w : Fin n → A,
        if profile a₀ m z w = t.val then
          ∑ y : Address z t.val → S → Y,
            (∏ s, factor L U z w t.val s (fun i => x i s) (fun u => y u s)) *
              ∏ u, P u.1 (y u)
        else 0 := by
  classical
  rw [sum_comm]
  simp_rw [hT]
  rw [Fintype.prod_sum]
  apply sum_congr rfl
  intro w _
  let t : ↥(histograms A (m + Fintype.card A)) := ⟨profile a₀ m z w, profile_mem a₀ hn hz w⟩
  rw [Fintype.sum_eq_single t]
  · rw [ite_eq_left (show profile a₀ m z w = t.val from rfl)]
    exact (contract P L U hU w t.val (rounded_covers a₀ m hz _) x).symm
  · intro u hu
    exact ite_eq_right (fun he => hu (Subtype.ext he.symm))

end OAI.LinearAlgebra.MatrixExponent.Routing.WordSum
end

/-!
# Checking a rounded profile

The total count fixes the distinguished letter. Every other count can
be checked in a separate table on just one logarithmic-width counter.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.WordSum

open Control Install Finset

variable {K A R : Type} [Field K] [Fintype A] [DecidableEq A] [Fintype R]
  (a₀ : A) (D : (R → Bool) → A)

private theorem profile_eq {m z n : ℕ} (hn : n = m * z) (hz : 0 < z)
    (t : ↥(histograms A (m + Fintype.card A))) (w : Fin n → A) :
    profile a₀ m z w = t.val ↔ ∀ a ≠ a₀, histogram w a none / z + 1 = t.val a := by
  have e (a : A) (ha : a ≠ a₀) : profile a₀ m z w a = histogram w a none / z + 1 := by
    simp [profile, rounded, ha]
  constructor
  · exact fun he a ha => (e a ha).symm.trans (congrFun he a)
  · intro h
    have h' (a : A) (ha : a ≠ a₀) : profile a₀ m z w a = t.val a := (e a ha).trans (h a ha)
    funext a
    by_cases ha : a ≠ a₀
    · exact h' a ha
    have : a = a₀ := not_ne_iff.mp ha
    subst a
    have hs := (mem_histograms.mp (profile_mem a₀ hn hz w)).trans (mem_histograms.mp t.property).symm
    rw [← sum_erase_add univ _ (mem_univ a₀), ← sum_erase_add univ _ (mem_univ a₀),
      sum_congr rfl (fun i hi => h' i (mem_erase.mp hi).1)] at hs
    exact add_left_cancel hs

/-- Tests on all counters cost linear times logarithmic in the number
of positions, for each fixed alphabet and encoding. -/
theorem check_net : ∃ B : ℕ, ∀ h m z : ℕ, 2 ^ h = m * z → 0 < z →
    ∀ t : ↥(histograms A (m + Fintype.card A)),
      Weight K (fun x : Fin (2 ^ h) × R → Bool =>
        if profile a₀ m z (letters D x) = t.val then 1 else 0) (B * 2 ^ h * (h + 1)) := by
  let B := rankCost R A + Fintype.card A + 20
  refine ⟨Fintype.card R + Fintype.card A * (5 * Fintype.card R + B), fun h m z hn hz t => ?_⟩
  let test (a : A) (x : Fin (2 ^ h) × R → Bool) :=
    if a ≠ a₀ → histogram (letters D x) a none / z + 1 = t.val a then (1 : K) else 0
  have one (a : A) : Weight K (test a) (B * 2 ^ h * (h + 1)) := by
    let q (x : slots (word (h + 1)) → Bool) :=
      if a ≠ a₀ → (decode (h + 1) x).val / z + 1 = t.val a then (1 : K) else 0
    let select (i : slots (word (h + 1))) : (A ⊕ Fin (2 ^ h)) × slots (word (h + 1)) := (.inl a, i)
    have H := (ranks_bnet K R A D h).weight ((Weight.dense K _ q).pull select)
    have he : (fun x => q (x ∘ select)) ∘ ranks D h = test a := by
      funext x
      have hc : histogram (letters D x) a none < 2 ^ (h + 1) :=
        (histogram_le _ _ _).trans_lt (by exact pow_lt_pow_right₀ (by decide) (by omega))
      change q (bits (word (h + 1)) (Lookup.bits (h + 1) (histogram (letters D x) a none))) = _
      simp [q, test, decode, index, Lookup.value_bits hc]
    rw [he] at H
    apply H.mono
    simp only [Fintype.card_prod, Fintype.card_sum, Fintype.card_fin, card_slots, wd_word, B,
      show Fintype.card (slots .bit) = 1 from rfl, Nat.add_comm 1 h, pow_succ]
    have hp : 1 ≤ 2 ^ h := Nat.one_le_pow _ _ (by decide)
    nlinarith only [Nat.mul_le_mul_right (Fintype.card A * (h + 1)) hp,
      Nat.mul_le_mul_right (h + 1) hp, Nat.zero_le (2 ^ h * h)]
  have hv : (fun x => ∏ a, test a x) =
      (fun x => if profile a₀ m z (letters D x) = t.val then (1 : K) else 0) := by
    funext x
    simp only [profile_eq a₀ hn hz]
    by_cases hp : ∀ a ≠ a₀, histogram (letters D x) a none / z + 1 = t.val a
    · rw [ite_eq_left hp]
      exact prod_eq_one fun a _ => ite_eq_left (hp a)
    · rw [ite_eq_right hp]
      obtain ⟨a, ha⟩ := not_forall.mp hp
      exact prod_eq_zero (mem_univ a) (ite_eq_right ha)
  rw [← hv]
  apply (Weight.finite_product test one).mono
  simp only [Fintype.card_prod, Fintype.card_fin]
  ring_nf
  omega

end OAI.LinearAlgebra.MatrixExponent.Routing.WordSum
end

/-! # Exact coverage at arbitrary scale with a fixed selector set -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.Proposal

open Spectral Stock Finset

variable {K S B I E J : Type} [Field K] [Fintype S] [Fintype B] [DecidableEq S]
  [DecidableEq B] [Nonempty S] [Fintype I] [Fintype E] [Fintype J]
  [DecidableEq I] [DecidableEq E] [DecidableEq J] {T : J → Tensor K S} {H : ℝ}

/-- After fixing the number of blocks, every positive tensor power
uses the same selector alphabet of rounded histograms. -/
theorem flex_covers (q : Proposal T H) (g : J → I ⊕ E) (u : Finset J) (m : ℕ)
    (hd : ∀ j ∈ q.demand, ∃ i, g j = .inl i) (hu : (2 : Tensor K S) ≤ ∏ j ∈ u, T j)
    (n : S → B) (U : I ⊕ E → Tensor K B) (he : ∀ j, Tensor.place n (T j) = U (g j))
    (hT : ∀ j, 1 ≤ T j) (hm : 0 < m) (z : ℕ) (hz : 0 < z) :
    (q.flex g u m).Covers (fun i => U (.inl i) ^ z) (fun e => U (.inr e) ^ z) := by
  classical
  let : MulLeftMono (Tensor K S) := ⟨fun c a b h => Tensor.mul_le_mul_left _ _ _ h⟩
  let V j := bundle T (q.orders j)
  have hV (j) : 1 ≤ V j := by
    apply one_le_prod
    intro i _
    have h := pow_le_pow_left' (hT i) (q.orders j i)
    rw [one_pow] at h
    exact h
  let l := m + Fintype.card q.move.letter
  have round (t) (ht : t ∈ histograms q.move.letter (m * z)) :
      ∃ h ∈ histograms q.move.letter l, bundle V t ≤ (bundle V h) ^ z := by
    have hpos : 0 < ∑ i, t i := by rw [mem_histograms.mp ht]; exact Nat.mul_pos hm hz
    obtain ⟨a, _, _⟩ := Finset.exists_ne_zero_of_sum_ne_zero hpos.ne'
    refine ⟨rounded a m z t, rounded_mem a hz ht, ?_⟩
    rw [bundle, bundle, ← prod_pow]
    exact prod_le_prod fun i _ => by
      rw [← pow_mul]
      exact pow_le_pow_right' (hV i) (rounded_covers a m hz t i)
  have cmp := q.batch_scaled u hu m l z (Nat.le_add_right _ _) round
  refine q.place_trade g u m l hd (fun j => T j ^ z) n (fun j => U j ^ z) ?_ ?_
  · intro j
    have aux (k : ℕ) : Tensor.place n (T j ^ k) = U (g j) ^ k := by
      induction k with
      | zero => simp [Tensor.place_one]
      | succ k ih => rw [pow_succ, Tensor.place_mul, ih, he, pow_succ]
    exact aux z
  · have hp (t) : bundle (fun j => T j ^ z) t = (bundle T t) ^ z := by
      rw [bundle, bundle, ← prod_pow]
      exact prod_congr rfl (fun i _ => pow_right_comm _ _ _)
    simpa only [hp] using cmp

end OAI.LinearAlgebra.MatrixExponent.Routing.Proposal
end

/-!
# A fixed local decision at every center

A price vector restricted to a shape determines whether it acts and
what it does. Acting at every enabled center avoids testing a global
average or computing a packing in the protocol.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral
open scoped Classical

variable {K I S : Type} [Field K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  {A : Finset (Tensor K S)} {N M : ℕ} {ρ : ℝ} (a : Atlas N A M ρ)

namespace Atlas

def Enabled (s : Shape N) (p : s.2.Goods A → ℝ) : Prop :=
  ∃ q ∈ a.menu s, q.demand ⊆ s.2.demands A ∧ q.demand.Nonempty ∧ q.Works a.margin p

def select (s : Shape N) (p : s.2.Goods A → ℝ) (h : a.Enabled s p) : s.Move A :=
  Classical.choose h

theorem selected (s : Shape N) (p : s.2.Goods A → ℝ) (h : a.Enabled s p) :
    let q := a.select s p h
    q ∈ a.menu s ∧ q.demand ⊆ s.2.demands A ∧ q.demand.Nonempty ∧ q.Works a.margin p :=
  Classical.choose_spec h

/-- The extra supply for rounding each symbol costs at most half the saving. -/
def Room (m : ℕ) : Prop :=
  ∀ s q, q ∈ a.menu s → Fintype.card q.move.letter ≤ m ∧
    ∀ p : s.2.Goods A → ℝ, p ≤ (fun _ => (M : ℝ)) →
      (Fintype.card q.move.letter : ℝ) * q.move.block * (∑ j ∈ q.demand, p j) ≤ m * (a.margin / 2)

theorem room : ∃ m₀ : ℕ, ∀ m ≥ m₀, a.Room m := by
  obtain ⟨C, hC⟩ := a.bound (fun _ q => Fintype.card q.move.letter)
  obtain ⟨D, hD⟩ := a.bound (fun _ q => Fintype.card q.move.letter * q.move.block * q.demand.card * M)
  obtain ⟨t, ht⟩ := exists_nat_gt ((D : ℝ) / (a.margin / 2))
  refine ⟨max C t, fun m hm s q hq => ⟨(hC _ _ hq).trans ((le_max_left _ _).trans hm), ?_⟩⟩
  intro p hp
  calc
    _ ≤ (Fintype.card q.move.letter : ℝ) * q.move.block * (q.demand.card * M) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      simpa using Finset.sum_le_sum (s := q.demand) fun i _ => hp i
    _ ≤ (D : ℝ) := by rw [← mul_assoc]; exact_mod_cast hD _ _ hq
    _ ≤ _ := (div_le_iff₀ (half_pos a.positive)).mp (ht.le.trans
      (Nat.cast_le.mpr ((le_max_right _ _).trans hm)))

end Atlas

namespace Market

variable (b : Market I N) (p : b.Request A → ℝ)

def active : Finset I := Finset.univ.filter fun i => a.Enabled (b.code i) (b.rates A p ∘ b.assign A i)

def moveAt (i : b.active a p) : (b.code i).Move A :=
  a.select (b.code i) (b.rates A p ∘ b.assign A i) (Finset.mem_filter.mp i.property).2

omit [DecidableEq I] in
theorem moving (i : b.active a p) :
    let q := b.moveAt a p i
    q ∈ a.menu (b.code i) ∧ q.demand ⊆ (b.shape i).demands A ∧ q.demand.Nonempty ∧
      q.Works a.margin (b.rates A p ∘ b.assign A i) :=
  a.selected _ _ _

def localMove (m : ℕ) (i : b.active a p) : Intervention (b.Request A) b.Edge :=
  (b.moveAt a p i).flex (b.assign A i) ((b.shape i).links A) m

def policy (m : ℕ) : Intervention (b.Request A) b.Edge :=
  Intervention.parallel (b.localMove a p m)

theorem local_overlap [Nonempty S] (m : ℕ) :
    Intervention.Overlap (b.localMove a p m) N := by
  intro x
  let J := b.active a p
  let U := Finset.univ.filter fun j : J => b.home A x ∈ b.support j
  have h : U.map (Function.Embedding.subtype _) ⊆
      Finset.univ.filter (fun j => b.home A x ∈ b.support j) := by
    rintro _ hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hj).2⟩
  refine ⟨U, ?_, fun j he => ?_⟩
  · simpa only [Finset.card_map] using (Finset.card_le_card h).trans (b.count_support _)
  · obtain ⟨k, hk⟩ := (b.moveAt a p j).flex_support _ _ _ he
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, b.home_mem A j k x hk⟩

omit [DecidableEq I] in
theorem demand_slot (i : b.active a p) :
    ∀ j ∈ (b.moveAt a p i).demand, ∃ l, b.assign A i j = .inl l := by
  intro j hj
  obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp ((b.moving a p i).2.1 hj)
  exact ⟨_, rfl⟩

theorem local_efficient (m : ℕ) (hm : a.Room m) (hM : 1 ≤ M)
    (hp : ∀ i, p i ≤ M) (i : b.active a p) :
    (b.localMove a p m i).Efficient p (a.margin / 2) (2 * a.capacity) m := by
  let E := b.shape i
  let g := b.assign A i
  let q := b.moveAt a p i
  have hs := b.moving a p i
  have hu : ∀ j ∈ E.links A, ∃ l, g j = .inr l := by
    intro j hj
    obtain ⟨x, _, rfl⟩ := Finset.mem_map.mp hj
    exact ⟨_, rfl⟩
  obtain ⟨hb, ho⟩ := a.small _ q hs.1
  obtain ⟨hm₁, hm₂⟩ := hm _ q hs.1
  refine q.flex_efficient g (E.links A) m (b.assign_injective A i) (b.demand_slot a p i) hu
    (by simp [BallShape.links, E]) a.positive.le hs.2.2.2 hb ho hm₁ (hm₂ _ ?_)
  intro j
  change b.rates A p (g j) ≤ _
  cases g j with
  | inl x => exact hp x
  | inr x => exact Nat.one_le_cast.mpr hM

end Market
end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# A local schedule independent of the payload width
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral
open scoped Classical BigOperators

variable {K I S : Type} [Field K] [Fintype I] [DecidableEq I] [Fintype S] [DecidableEq S]
  {A : Finset (Tensor K S)} {N M : ℕ} {ρ : ℝ} (b : Market I N) (a : Atlas N A M ρ)

namespace Market

theorem policy_covers [Nonempty S] (p : b.Request A → ℝ) (ha : 0 ∉ A)
    (m : ℕ) (hm : 0 < m) (z : ℕ) (hz : 0 < z) :
    (b.policy a p m).Covers (fun i => b.tensor A (.inl i) ^ z) (fun e => b.tensor A (.inr e) ^ z) := by
  apply Intervention.parallel_covers
  intro i
  let _ : Nonempty (b.Site i) := ⟨(b.shape i).src⟩
  exact (b.moveAt a p i).flex_covers _ _ _ (b.demand_slot a p i)
    ((b.shape i).broadcast A) (b.name i) (b.tensor A) (b.place_tensor A i)
    (fun j => Tensor.one_le _ ((b.shape i).nonzero A ha j)) hm z hz

omit [DecidableEq I] in
theorem active_count [Nonempty I] (hM : 1 ≤ M) (d : ℕ) (hf : b.Frequent A ρ d)
    (p : b.Request A → ℝ) (hp : ∀ i, p i ∈ Set.Icc 0 (M : ℝ)) (hd : ∀ i, |p (.inl i)| ≤ d)
    (h : 1201 * (b.payload A).card < ∑ i ∈ b.payload A, p i) :
    ρ * (b.payload A).card ≤ Fintype.card (b.active a p) := by
  have h' : 1201 < (𝔼 i, p (.inl i)) := by
    rw [Fintype.expect_eq_sum_div_card, lt_div_iff₀ (by positivity)]
    rw [card_payload, payload, Finset.sum_map] at h
    exact h
  obtain ⟨J, hJ, hj⟩ := hf p hd h'
  have sub : J ⊆ b.active a p := by
    intro i hi
    let g := b.assign A i
    have hb (j) : b.rates A p (g j) ∈ Set.Icc 0 (M : ℝ) := by
      cases g j with
      | inl x => exact hp x
      | inr x => exact ⟨zero_le_one, Nat.one_le_cast.mpr hM⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (a.detect (b.code i) (b.rates A p ∘ g)
      ⟨fun j => (hb j).1, fun j => (hb j).2⟩).resolve_left (hj _ hi)⟩
  rw [card_payload, Fintype.card_coe]
  exact hJ.le.trans (Nat.cast_le.mpr (Finset.card_le_card sub))

def decision (μ d m : ℕ) (z : b.Request A → ℕ) : Intervention (b.Request A) b.Edge :=
  b.policy a (fun i => price μ (b.cap A d M i) (z i)) m

end Market

theorem Atlas.schedule [Nonempty S] (hM : 1 ≤ M) (hρ : 0 < ρ) :
    ∃ h μ W : ℕ, a.Room (2 ^ h) ∧ 0 < μ ∧ 4 ≤ W ∧
      ∀ (I : Type) [Fintype I] [Nonempty I] [DecidableEq I] (b : Market I N) (d : ℕ), d ≤ M →
        b.Frequent A ρ d →
          Runs (b.payload A) (b.cap A d M) (b.decision a μ d (2 ^ h)) (1203 * Fintype.card I * W) W 0 0 := by
  let C := max M (1 + N ^ Fintype.card S * A.card)
  obtain ⟨m₀, hm₀⟩ := a.room
  obtain ⟨h, μ, W, hm, hμ, hw, hr⟩ := Routing.schedule N (2 * a.capacity) C m₀
    (half_pos a.positive) hρ (show (0 : ℝ) ≤ 1201 by norm_num)
  have room := hm₀ _ hm
  refine ⟨h, μ, W, room, hμ, hw, fun I _ _ _ b d hd hf => ?_⟩
  have hb (i) : 0 ≤ b.cap A d M i ∧ b.cap A d M i ≤ M := by
    cases i with
    | inl x => exact ⟨Nat.cast_nonneg _, Nat.cast_le.mpr hd⟩
    | inr x => exact ⟨Nat.cast_nonneg _, le_rfl⟩
  rw [show (1203 : ℝ) = 1201 + 2 by norm_num, ← b.card_payload A]
  apply hr
  · rw [b.card_payload, mul_comm]
    exact (b.card_request A).trans (Nat.mul_le_mul_left _ (le_max_right _ _))
  · exact fun i => ⟨(hb i).1, (hb i).2.trans (Nat.cast_le.mpr (le_max_left _ _))⟩
  · intro z
    let p i := price μ (b.cap A d M i) (z i)
    have hp (i) : p i ∈ Set.Icc 0 (M : ℝ) :=
      ⟨price_nonneg (Nat.cast_pos.mpr hμ) (hb i).1 (Nat.cast_nonneg _), price_le.trans (hb i).2⟩
    have hv (i) : |p (.inl i)| ≤ d := by
      rw [abs_of_nonneg (hp _).1]
      exact price_le
    exact ⟨b.active a p, inferInstance, inferInstance, b.localMove a p (2 ^ h),
      b.active_count a hM d hf p hp hv, b.local_overlap a p (2 ^ h),
      b.local_efficient a p (2 ^ h) room hM (fun i => (hp i).2), rfl⟩

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! # Access to the supply bits selected by a word -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.WordSum

open Install Control

abbrev Row (h : ℕ) := Fin (2 ^ h)

variable {A R B C K : Type}

abbrev Input (R B C : Type) (h z : ℕ) (t : A → ℕ) :=
  (Row h × (R ⊕ B)) ⊕ (Address z t × C)

abbrev Work (R B C : Type) (h z : ℕ) (t : A → ℕ) :=
  Input R B C h z t ⊕ ((A ⊕ Row h) × slots (word (h + 1)))

def scale (h : ℕ) := 2 ^ h * (h + 1) ^ 3

theorem rows_le (h : ℕ) : 2 ^ h ≤ scale h := Nat.le_mul_of_pos_right _ (by positivity)

theorem rows_succ_le (h : ℕ) : 2 ^ (h + 1) ≤ 2 * scale h := by
  rw [pow_succ']
  exact Nat.mul_le_mul_left _ (rows_le h)

private theorem row_bits (h : ℕ) : 2 ^ h * (h + 1) ≤ scale h := by
  unfold scale
  ring_nf
  omega

variable [Field K] [Fintype A] [DecidableEq A] [Fintype R] [Fintype B] [Fintype C]
  {h z : ℕ} {t : A → ℕ}

omit [DecidableEq A] in
theorem work_size :
    ∃ M : ℕ, ∀ (h z : ℕ) (t : A → ℕ), (∀ a, t a * z ≤ 2 ^ (h + 1)) →
      Fintype.card (Work R B C h z t) ≤ M * scale h := by
  refine ⟨Fintype.card R + Fintype.card B + 2 * Fintype.card A * Fintype.card C +
    (Fintype.card A + 1), fun h z t ht => ?_⟩
  have ha : Fintype.card (Address z t) ≤ Fintype.card A * (2 * scale h) := by
    rw [Fintype.card_sigma]
    simpa using Finset.sum_le_sum (s := Finset.univ) (fun a _ => (ht a).trans (rows_succ_le h))
  have hi : Fintype.card A + 2 ^ h ≤ (Fintype.card A + 1) * 2 ^ h := by
    rw [add_mul, one_mul]
    exact Nat.add_le_add_right (Nat.le_mul_of_pos_right _ (by positivity)) _
  simp only [Work, Input, Row, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_slots, wd_word,
    show Fintype.card (slots .bit) = 1 from rfl, Nat.add_comm 1 h]
  calc
    _ ≤ scale h * (Fintype.card R + Fintype.card B) +
        (Fintype.card A * (2 * scale h)) * Fintype.card C +
        ((Fintype.card A + 1) * 2 ^ h) * (h + 1) := by gcongr; exact rows_le h
    _ ≤ _ := by
      have := Nat.mul_le_mul_left (Fintype.card A + 1) (row_bits h)
      ring_nf at this ⊢
      omega

def prepare (D : (R → Bool) → A) (v : Input R B C h z t → Bool) : Work R B C h z t → Bool :=
  Sum.elim v (ranks D h (fun ij => v (.inl (ij.1, .inl ij.2))))

theorem prepare_net (D : (R → Bool) → A) {M : ℕ} (hm : Fintype.card (Work R B C h z t) ≤ M * scale h) :
    BNet K (prepare (B := B) (C := C) (h := h) (z := z) (t := t) D)
      ((7 * M + 2 * Fintype.card R + rankCost R A) * scale h) := by
  let sel (p : Row h × R) : Input R B C h z t := .inl (p.1, .inl p.2)
  apply ((BNet.id K _).pair ((ranks_bnet K R A D h).pull sel)).mono
  have hc : Fintype.card (Input R B C h z t) ≤ M * scale h :=
    (Fintype.card_le_of_injective Sum.inl Sum.inl_injective).trans hm
  rw [Fintype.card_prod, Fintype.card_fin]
  have := Nat.mul_le_mul_right (Fintype.card R) (rows_le h)
  have hk := Nat.mul_le_mul_left (rankCost R A) (row_bits h)
  ring_nf at this hk hc ⊢
  omega

def load (v : Work R B C h z t → Bool) (a : A) (j : ℕ) (c : C) : Bool :=
  if hj : j < t a * z then v (.inl (.inr (⟨a, ⟨j, hj⟩⟩, c))) else false

def number (v : Work R B C h z t → Bool) (i : A ⊕ Row h) : ℕ :=
  (decode (h + 1) (fun j => v (.inr (i, j)))).val

omit [Fintype R] [Fintype B] [Fintype C] [Fintype A] in
theorem number_prepare (D : (R → Bool) → A) (v : Input R B C h z t → Bool) (i : A ⊕ Row h) :
    number (prepare D v) i =
      let w := fun j => D (fun k => v (.inl (j, .inl k)))
      Sum.elim (fun a => histogram w a none) (rank w) i := by
  let w := fun j => D (fun k => v (.inl (j, .inl k)))
  let n := Sum.elim (fun a => histogram w a none) (rank w) i
  have hn : n ≤ 2 ^ h := by
    cases i <;> exact histogram_le w _ _
  have hr : n < 2 ^ (h + 1) := by
    rw [pow_succ]
    have : 0 < 2 ^ h := by positivity
    omega
  change ((decode (h + 1)) ((decode (h + 1)).symm ⟨n, hr⟩)).val = n
  rw [Equiv.apply_symm_apply]

def up (i : Row h) : Row (h + 1) := ⟨i, by rw [pow_succ]; have := i.isLt; omega⟩

private def down (i : Row (h + 1)) : Row h := if hi : i.val < 2 ^ h then ⟨i, hi⟩ else 0

private abbrev Buffer (h : ℕ) := Row (h + 1) ⊕ (Row (h + 1) × slots (word (h + 1)))

private def buf (a : A) (c : C) (v : Work R B C h z t → Bool) : Buffer h → Bool
  | .inl j => load v a j c
  | .inr p => v (.inr (.inr (down p.1), p.2))

omit [DecidableEq A] [Fintype A] [Fintype R] [Fintype B] [Fintype C] in
private theorem buf_depends (a : A) (c : C) :
    Depends (buf (R := R) (B := B) (h := h) (z := z) (t := t) a c) 1 := by
  classical
  intro k
  cases k with
  | inl i =>
    by_cases he : i.val < t a * z
    · refine ⟨{.inl (.inr (⟨a, ⟨i, he⟩⟩, c))}, by simp, fun x y hxy => ?_⟩
      simp only [buf, load, he, dite_true]
      exact hxy _ (by simp)
    · exact ⟨∅, by simp, fun x y _ => by simp [buf, load, he]⟩
  | inr p => exact ⟨{.inr (.inr (down p.1), p.2)}, by simp, fun x y hxy => hxy _ (by simp)⟩

/-- Run one batched read for each possible letter and payload bit. -/
def fetchColumn (ac : A × C) (v : Work R B C h z t → Bool) : Row (h + 1) → Bool :=
  read (h + 1) (buf ac.1 ac.2 v)

omit [DecidableEq A] [Fintype A] [Fintype R] [Fintype B] [Fintype C] in
theorem fetchColumn_up (a : A) (c : C) (v : Work R B C h z t → Bool) (i : Row h) :
    fetchColumn (a, c) v (up i) = load v a (number v (.inr i)) c := by
  have hd : down (up i) = i := by simp [up, down, i.isLt]
  simp only [fetchColumn, Control.read, buf, hd, number]

omit [DecidableEq A] in
theorem column_net {M : ℕ} (hm : Fintype.card (Work R B C h z t) ≤ M * scale h) (ac : A × C) :
    BNet K (fetchColumn (R := R) (B := B) (h := h) (z := z) (t := t) ac)
      ((M + 4 * localCost 1 + 160000) * scale h) := by
  apply (((buf_depends ac.1 ac.2).bnet K).comp (read_net K (h + 1))).mono
  have hb : Fintype.card (Buffer h) ≤ 4 * scale h := by
    unfold Buffer
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, card_slots, wd_word]
    unfold scale
    ring_nf
    omega
  have hr : 10000 * 2 ^ (h + 1) * (h + 1 + 1) ^ 3 ≤ 160000 * scale h := by
    unfold scale
    ring_nf
    omega
  have hb' := Nat.mul_le_mul_left (localCost 1) hb
  ring_nf at hm hb' hr ⊢
  omega

end OAI.LinearAlgebra.MatrixExponent.Routing.WordSum
end

/-!
# Trivalent implementation of a local rounded-word factor

All bit alphabets are fixed. Query every payload column in parallel,
then select the letter and apply its kernel in a fixed-arity table.
Unused supplies are handled by thresholds on the per-letter counts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Routing.WordSum

open Install Control

variable {K A R B C S : Type} [Field K] [Fintype A] [DecidableEq A]
  [Fintype R] [Fintype B] [Fintype C] {h z : ℕ} {t : A → ℕ}

private def active (L : A → (B → Bool) → (C → Bool) → K) (D : (R → Bool) → A)
    (v : Work R B C h z t → Bool) :=
  ∏ i : Row h,
    let a := D (fun r => v (.inl (.inl (i, .inl r))))
    L a (fun b => v (.inl (.inl (i, .inr b)))) (load v a (number v (.inr i)))

omit [DecidableEq A] in
private theorem active_net (D : (R → Bool) → A) (M : ℕ) :
    ∃ N : ℕ, ∀ h z (t : A → ℕ), Fintype.card (Work R B C h z t) ≤ M * scale h →
      ∀ L : A → (B → Bool) → (C → Bool) → K,
        Weight K (active (h := h) (z := z) (t := t) L D) (N * scale h) := by
  let J := A × C
  let Q := (R ⊕ B) ⊕ J
  let n := M + 4 * localCost 1 + 160000
  let q := 8 * 2 ^ Fintype.card Q
  refine ⟨8 * M + Fintype.card J * (5 * M + n + 2) + 2 * Fintype.card Q + q,
    fun h z t hm L => ?_⟩
  let W := Work R B C h z t
  let cols := BNet.finite_share _ (fun j : J => column_net (K := K) hm j)
  let e (ij : Row h × Q) : W ⊕ (J × Row (h + 1)) :=
    Sum.elim (fun k => .inl (.inl (.inl (ij.1, k)))) (fun k => .inr (k, up ij.1)) ij.2
  let table (v : Q → Bool) :=
    let a := D (fun r => v (.inl (.inl r)))
    L a (fun b => v (.inl (.inr b))) (fun c => v (.inr (a, c)))
  have net := ((BNet.id K W).pair cols).weight (((Weight.dense K Q table).prod h).pull e)
  convert net.mono (n := (8 * M + Fintype.card J * (5 * M + n + 2) +
    2 * Fintype.card Q + q) * scale h) ?_ using 1
  · funext v
    simp only [active, Function.comp_def, table, e, Sum.elim_inl, Sum.elim_inr, id_eq, fetchColumn_up]
  · change 5 * Fintype.card W + Fintype.card W +
      (Fintype.card W + Fintype.card J * (5 * Fintype.card W + n * scale h)) +
      (Fintype.card (W ⊕ (J × Row (h + 1))) + 2 * Fintype.card (Row h × Q) + 2 ^ h * q) ≤ _
    have hc : Fintype.card (W ⊕ (J × Row (h + 1))) =
        Fintype.card W + Fintype.card J * 2 ^ (h + 1) := by
      rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    rw [hc, show Fintype.card (Row h × Q) = 2 ^ h * Fintype.card Q by
      rw [Fintype.card_prod, Fintype.card_fin]]
    change Fintype.card W ≤ _ at hm
    have h₁ := Nat.mul_le_mul_left (Fintype.card J) hm
    have h₂ := Nat.mul_le_mul_left (Fintype.card J) (rows_succ_le h)
    have h₃ := Nat.mul_le_mul_right (Fintype.card Q) (rows_le h)
    have h₄ := Nat.mul_le_mul_right q (rows_le h)
    ring_nf at hm h₁ h₂ h₃ h₄ ⊢
    omega

private def extra (a : A) (U : (C → Bool) → K) (v : Work R B C h z t → Bool) :=
  ∏ j : Row (h + 1), if j.val < t a * z then
    if number v (.inl a) ≤ j.val then U (load v a j.val) else 1 else 1

private def flags (a : A) (v : Work R B C h z t ⊕ Row (h + 1) → Bool)
    (p : Row (h + 1) × (Unit ⊕ C)) : Bool :=
  if hj : p.1.val < t a * z then
    Sum.elim (fun _ => v (.inr p.1)) (fun c => v (.inl (.inl (.inr (⟨a, ⟨p.1.val, hj⟩⟩, c))))) p.2
  else false

omit [DecidableEq A] [Fintype A] [Fintype R] [Fintype B] [Fintype C] in
private theorem flags_depends (a : A) :
    Depends (flags (R := R) (B := B) (C := C) (h := h) (z := z) (t := t) a) 1 := by
  classical
  rintro ⟨j, k⟩
  by_cases hj : j.val < t a * z
  · cases k with
    | inl u =>
      refine ⟨{.inr j}, by simp, fun x y he => ?_⟩
      simp only [flags, hj, dite_true, Sum.elim_inl]
      exact he _ (by simp)
    | inr c =>
      refine ⟨{.inl (.inl (.inr (⟨a, ⟨j.val, hj⟩⟩, c)))}, by simp, fun x y he => ?_⟩
      simp only [flags, hj, dite_true, Sum.elim_inr]
      exact he _ (by simp)
  · exact ⟨∅, by simp, fun x y _ => by simp [flags, hj]⟩

omit [DecidableEq A] in
private theorem extra_net (M : ℕ) :
    ∃ N : ℕ, ∀ h z (t : A → ℕ), Fintype.card (Work R B C h z t) ≤ M * scale h →
      ∀ (a : A) (U : (C → Bool) → K),
        Weight K (extra (R := R) (B := B) (h := h) (z := z) (t := t) a U) (N * scale h) := by
  let q := 8 * 2 ^ Fintype.card (Unit ⊕ C)
  refine ⟨8 * M + 8004 + 2 * (localCost 1 * Fintype.card (Unit ⊕ C) + q), fun h z t hm a U => ?_⟩
  let W := Work R B C h z t
  let e (k : slots (word (h + 1))) : W := .inr (.inl a, k)
  let table (v : Unit ⊕ C → Bool) := if v (.inl ()) then U (v ∘ Sum.inr) else 1
  have ht := (BNet.id K W).pair ((threshold_bnet K (h + 1)).pull e)
  have net := (ht.comp ((flags_depends a).bnet K)).weight ((Weight.dense K _ table).prod (h + 1))
  convert net.mono (n := (8 * M + 8004 + 2 * (localCost 1 * Fintype.card (Unit ⊕ C) + q)) *
    scale h) ?_ using 1
  · funext v
    unfold extra
    apply Finset.prod_congr rfl
    intro j _
    by_cases hj : j.val < t a * z
    · have hl : load v a j.val = fun c => v (.inl (.inr (⟨a, ⟨j.val, hj⟩⟩, c))) := by
        funext c
        simp [load, hj]
      simp [table, flags, e, number, Function.comp_def, hj, hl]
    · simp [table, flags, hj]
  · change 5 * Fintype.card W + Fintype.card W + (Fintype.card W +
        2 * Fintype.card (slots (word (h + 1))) + 2000 * 2 ^ (h + 1) * (h + 1 + 1)) +
      (Fintype.card (W ⊕ Row (h + 1)) + localCost 1 * Fintype.card (Row (h + 1) × (Unit ⊕ C))) +
      2 ^ (h + 1) * q ≤ _
    rw [card_slots, wd_word,
      show Fintype.card (W ⊕ Row (h + 1)) = Fintype.card W + 2 ^ (h + 1) by
        rw [Fintype.card_sum, Fintype.card_fin],
      show Fintype.card (Row (h + 1) × (Unit ⊕ C)) = 2 ^ (h + 1) * Fintype.card (Unit ⊕ C) by
        rw [Fintype.card_prod, Fintype.card_fin]]
    change Fintype.card W ≤ _ at hm
    have hh : h + 1 ≤ scale h := by
      have hp := Nat.lt_two_pow_self (n := h)
      exact Nat.le_trans hp (rows_le h)
    have ht : 2000 * 2 ^ (h + 1) * (h + 1 + 1) ≤ 8000 * scale h := by
      unfold scale
      ring_nf
      omega
    have hk := Nat.mul_le_mul_right (1 + localCost 1 * Fintype.card (Unit ⊕ C) + q) (rows_succ_le h)
    ring_nf at hh ht hk hm ⊢
    omega

private theorem prod_prefix {m n : ℕ} (hm : m ≤ n) (f : ℕ → K) :
    (∏ i : Fin n, if i.val < m then f i.val else 1) = ∏ i : Fin m, f i.val := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  rw [Fin.prod_univ_add]
  simp

omit [Fintype R] [Fintype B] [Fintype C] in
private theorem factor_eq (L : A → S → (B → Bool) → (C → Bool) → K) (U : A → S → (C → Bool) → K)
    (D : (R → Bool) → A) (ht : ∀ a, t a * z ≤ 2 ^ (h + 1)) (s : S)
    (v : Input R B C h z t → Bool) :
    factor L U z (fun i => D (fun k => v (.inl (i, .inl k)))) t s
      (fun i b => v (.inl (i, .inr b))) (fun j c => v (.inr (j, c))) =
      active (fun a => L a s) D (prepare D v) * ∏ a, extra a (U a s) (prepare D v) := by
  have hload (a : A) (j : ℕ) : load (prepare D v) a j =
      if hj : j < t a * z then (fun c => v (.inr (⟨a, ⟨j, hj⟩⟩, c))) else default := by
    funext c
    by_cases hj : j < t a * z <;> simp [load, prepare, hj]
  unfold factor
  apply congrArg₂ (· * ·)
  · simp only [active, number_prepare, Sum.elim_inr, hload]
    rfl
  · rw [Fintype.prod_sigma]
    apply Finset.prod_congr rfl
    intro a _
    unfold extra
    rw [prod_prefix (ht a) (fun j => if number (prepare D v) (.inl a) ≤ j then
      U a s (load (prepare D v) a j) else 1)]
    apply Finset.prod_congr rfl
    intro j _
    simp only [number_prepare, Sum.elim_inl, hload, dite_eq_left j.isLt]

/-- The constant is independent of the site, histogram, power and
batch length. Invalid addresses read the all-false word. -/
theorem factor_net (L : A → S → (B → Bool) → (C → Bool) → K) (U : A → S → (C → Bool) → K)
    (D : (R → Bool) → A) :
    ∃ N : ℕ, ∀ h z (t : A → ℕ), (∀ a, t a * z ≤ 2 ^ (h + 1)) → ∀ s,
      Weight K (fun v : Input R B C h z t → Bool =>
        factor L U z (fun i => D (fun k => v (.inl (i, .inl k)))) t s
          (fun i b => v (.inl (i, .inr b))) (fun j c => v (.inr (j, c))))
        (N * 2 ^ h * (h + 1) ^ 3) := by
  obtain ⟨M, hM⟩ := work_size (A := A) (R := R) (B := B) (C := C)
  obtain ⟨N, hN⟩ := active_net (K := K) (B := B) (C := C) D M
  obtain ⟨P, hP⟩ := extra_net (K := K) (A := A) (R := R) (B := B) (C := C) M
  let cost := 13 * M + 2 * Fintype.card R + rankCost R A + N + Fintype.card A * (5 * M + P)
  refine ⟨cost, fun h z t ht s => ?_⟩
  have hm := hM h z t ht
  have ha := hN h z t hm (fun a => L a s)
  have he := Weight.finite_product _ (fun a => hP h z t hm a (U a s))
  have net := (prepare_net (K := K) D hm).weight (ha.mul he)
  rw [mul_assoc]
  change Weight K _ (cost * scale h)
  convert net.mono (n := cost * scale h) ?_ using 1
  · exact funext (factor_eq L U D ht s)
  · have := Nat.mul_le_mul_left (Fintype.card A) hm
    unfold cost
    ring_nf at hm this ⊢
    omega

end OAI.LinearAlgebra.MatrixExponent.Routing.WordSum
end
