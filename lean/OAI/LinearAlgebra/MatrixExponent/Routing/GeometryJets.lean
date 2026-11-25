import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.LinearAlgebra.Dual.Lemmas
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryTerms
import Mathlib.Algebra.Module.Basic
import Mathlib.Algebra.Polynomial.AlgebraMap
import OAI.LinearAlgebra.MatrixExponent.Sphere.Block
import OAI.LinearAlgebra.MatrixExponent.Sphere.Seam
import OAI.LinearAlgebra.MatrixExponent.Sphere.Private.Preparation
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.RingTheory.AdjoinRoot

/-!
# Selecting fusion terms by a common functional

After clearing poles a family is a polynomial of degree at most `N`.
The order at infinity is then `N - P.natDegree`. A single functional
annihilating the span of cheap tensors keeps the total order of the
first surviving coefficients over all collision charts at most `N`.
Energies are recorded in half-integer units.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset Polynomial
open scoped Classical

variable {F B : Type*} [Field F]

def jetAt (N : ℕ) (d : Option F) (i : ℕ) : F[X] →ₗ[F] F :=
  match d with
  | none => lcoeff F (N - i)
  | some s => (lcoeff F i).comp (taylor (-s))

private def firstOrder (N : ℕ) (P : F[X]) : Option F → ℕ
  | none => N - P.natDegree
  | some s => P.rootMultiplicity (-s)

private theorem jet_first (P : F[X]) {N : ℕ} (hP : P ≠ 0) (hN : P.natDegree ≤ N)
    (d : Option F) : jetAt N d (firstOrder N P d) P ≠ 0 := by
  cases d with
  | none =>
    change P.coeff (N - (N - P.natDegree)) ≠ 0
    rw [Nat.sub_sub_self hN, coeff_natDegree]
    exact leadingCoeff_ne_zero.mpr hP
  | some s =>
    change ((taylor (-s)) P).coeff (P.rootMultiplicity (-s)) ≠ 0
    rw [rootMultiplicity_eq_natTrailingDegree, ← taylor_apply, coeff_natTrailingDegree_ne_zero]
    simpa using hP

private theorem sum_first (P : F[X]) {N : ℕ} (hN : P.natDegree ≤ N)
    (D : Finset (Option F)) : ∑ d ∈ D, firstOrder N P d ≤ N := by
  have hs : D ⊆ insertNone (eraseNone D) := by
    intro d hd
    cases d <;> simp [hd]
  let S := (eraseNone D).image Neg.neg
  have h : ∑ z ∈ S, P.roots.count z ≤ P.natDegree := calc
    _ ≤ ∑ z ∈ S ∪ P.roots.toFinset, P.roots.count z := sum_le_sum_of_subset subset_union_left
    _ = P.roots.card := Multiset.sum_count_eq_card (fun _ hz => mem_union_right _ (Multiset.mem_toFinset.mpr hz))
    _ ≤ _ := card_roots' _
  rw [show S = _ from rfl, sum_image neg_injective.injOn] at h
  simp_rw [count_roots] at h
  apply le_trans (sum_le_sum_of_subset hs)
  rw [sum_insertNone]
  change N - P.natDegree + (∑ z ∈ eraseNone D, P.rootMultiplicity (-z)) ≤ N
  omega

variable [Fintype B]

private theorem scalarize (f : (B → F) →ₗ[F] F) (P : B → F[X]) {N : ℕ}
    (hn : ∀ b, (P b).natDegree ≤ N) :
    ∃ Q : F[X], Q.natDegree ≤ N ∧ ∀ g : F[X] →ₗ[F] F, g Q = f (fun b => g (P b)) := by
  let c (b : B) := f (Pi.single b 1)
  refine ⟨∑ b, c b • P b, ?_, fun g => ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun b _ => ?_
    exact (natDegree_smul_le _ _).trans (hn b)
  rw [map_sum, ← univ_sum_single (fun b => g (P b)), map_sum]
  refine sum_congr rfl fun b _ => ?_
  rw [map_smul, smul_eq_mul, mul_comm, ← smul_eq_mul]
  dsimp only [c]
  rw [← map_smul, ← Pi.single_smul, smul_eq_mul, mul_one]

/-- Each local jet lies in the span of candidates costing at most twice
its order. If one value survives modulo `W`, select a surviving candidate
in every chart with a *joint* budget of twice the degree bound. -/
theorem select_fusions {T : Option F → Type*} [∀ d, Nonempty (T d)] (D : Finset (Option F)) (P : B → F[X]) (N : ℕ)
    (term : ∀ d, T d → B → F) (cost : ∀ d, T d → ℕ)
    (hn : ∀ b, (P b).natDegree ≤ N)
    (hjet : ∀ d ∈ D, ∀ i ≤ N, (fun b => jetAt N d i (P b)) ∈
      Submodule.span F {v | ∃ t : T d, cost d t ≤ 2 * i ∧ term d t = v})
    (W : Submodule F (B → F)) (s : F) (he : (fun b => (P b).eval s) ∉ W) :
    ∃ t : ∀ d, T d, (∀ d ∈ D, term d (t d) ∉ W) ∧
      ∑ d ∈ D, cost d (t d) ≤ 2 * N := by
  have h := mt (Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff W _).mp he
  push Not at h
  obtain ⟨f, hf, hval⟩ := h
  obtain ⟨Q, hN, hQ⟩ := scalarize f P hn
  have hne : Q ≠ 0 := by
    intro hz
    apply hval
    simpa [hz] using (hQ (leval s)).symm
  have hsum := sum_first Q hN D
  have ex (d : Option F) (hd : d ∈ D) :
      ∃ t, cost d t ≤ 2 * firstOrder N Q d ∧ term d t ∉ W := by
    have hm : firstOrder N Q d ≤ N :=
      (single_le_sum (fun _ _ => Nat.zero_le _) hd).trans hsum
    by_contra! hall
    have hw : (fun b => jetAt N d (firstOrder N Q d) (P b)) ∈ W := by
      apply (Submodule.span_le.mpr ?_) (hjet d hd _ hm)
      rintro _ ⟨t, ht, rfl⟩
      exact hall t ht
    apply jet_first Q hne hN d
    rw [hQ]
    exact (Submodule.mem_dualAnnihilator f).mp hf _ hw
  choose! t ht ht' using ex
  refine ⟨t, ht', (sum_le_sum ht).trans ?_⟩
  rw [← mul_sum]
  exact Nat.mul_le_mul_left _ hsum

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-!
# Secant widths and incidence energy

The unit-mass transport inequality in the proof of the secant bound gives a
width for each line, with a bound on the sum of their squares. Transport along
a short segment, followed by squared distance comparison, lets us use those
widths directly, without introducing angles or first variation.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset

variable {Y : Type*} [MetricSpace Y]

/-- The transport bound controls the loss in the law of cosines, summed
over the points incident with a line. -/
theorem secant_comparison {E : Type*} (C : Comparison Y) (S : Finset E)
    (x : E → Y) (o z : Y) (b : ℝ)
    (h : ∀ m : Y, (∑ i ∈ S, dist o (x i) ^ 2) ≤
      b * dist o m + ∑ i ∈ S, dist o (x i) * dist m (x i)) :
    (∑ i ∈ S, dist o (x i) ^ 2) + S.card * dist o z ^ 2 ≤
      (∑ i ∈ S, dist (x i) z ^ 2) + 2 * b * dist o z := by
  let B := (S.card : ℝ) * dist o z ^ 2
  have hB : 0 ≤ B := by positivity
  apply le_of_forall_pos_le_add
  intro ε hε
  let t := min 1 (ε / (1 + B))
  have ht : 0 < t := lt_min zero_lt_one (by positivity)
  have he : t * B ≤ ε := calc
    _ ≤ t * (1 + B) := mul_le_mul_of_nonneg_left (by linarith) ht.le
    _ ≤ ε := (le_div_iff₀ (by positivity)).mp (min_le_right _ _)
  obtain ⟨m, hm, hcmp⟩ := C o z t ht.le (min_le_left _ _)
  have hl := h m
  rw [hm] at hl
  have hu : ∑ i ∈ S, 2 * (dist o (x i) * dist m (x i)) ≤
      ∑ i ∈ S, ((2 - t) * dist o (x i) ^ 2 + t * dist (x i) z ^ 2 -
        t * (1 - t) * dist o z ^ 2) := by
    apply sum_le_sum
    intro i _
    rw [dist_comm (x i) z]
    nlinarith only [hcmp (x i), sq_nonneg (dist o (x i) - dist m (x i))]
  simp only [sum_sub_distrib, sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul] at hu
  have hh : (∑ i ∈ S, dist o (x i) ^ 2) + B ≤
      (∑ i ∈ S, dist (x i) z ^ 2) + 2 * b * dist o z + t * B := by
    refine le_of_mul_le_mul_left ?_ ht
    dsimp [B]
    linarith only [hu, hl]
  exact hh.trans (add_le_add_right he _)

variable {A L E : Type*} [Fintype L] [Fintype E] [DecidableEq L]

/-- Raw sums over flags. In a biregular graph the normalized left hand
side uses the uniform distribution on each class of vertices. -/
theorem incidence_of_widths (C : Comparison Y) (p : E → A) (l : E → L)
    (x : A → Y) (y : L → Y) (o : Y) (b : L → ℝ) {s : ℕ} (hs : 0 < s)
    (hc : ∀ k, #{i | l i = k} = s)
    (transport : ∀ k m, (∑ i with l i = k, dist o (x (p i)) ^ 2) ≤
      b k * dist o m + ∑ i with l i = k, dist o (x (p i)) * dist m (x (p i)))
    {t : ℝ} (ht : 0 ≤ t)
    (budget : t ^ 2 * ∑ k, b k ^ 2 ≤ (s : ℝ) * ∑ i, dist o (x (p i)) ^ 2) :
    (t - 1) * (∑ i, (dist o (x (p i)) ^ 2 + dist o (y (l i)) ^ 2)) ≤
      t * ∑ i, dist (x (p i)) (y (l i)) ^ 2 := by
  have hs' : 0 < (s : ℝ) := Nat.cast_pos.mpr hs
  have step (k : L) :
      (s : ℝ) * ((t - 1) *
        ∑ i with l i = k, (dist o (x (p i)) ^ 2 + dist o (y (l i)) ^ 2)) +
        s * (∑ i with l i = k, dist o (x (p i)) ^ 2) ≤
      s * (t * ∑ i with l i = k, dist (x (p i)) (y (l i)) ^ 2) + t ^ 2 * b k ^ 2 := by
    have eqn (f : E → L → ℝ) :
        ∑ i with l i = k, f i (l i) = ∑ i with l i = k, f i k :=
      sum_congr rfl (fun i hi => congrArg (f i) (mem_filter.mp hi).2)
    rw [eqn (fun i v => dist o (x (p i)) ^ 2 + dist o (y v) ^ 2),
      eqn (fun i v => dist (x (p i)) (y v) ^ 2), sum_add_distrib, sum_const, hc, nsmul_eq_mul]
    have h := secant_comparison C {i | l i = k} (fun i => x (p i)) o (y k) (b k) (transport k)
    rw [hc] at h
    linarith only [mul_le_mul_of_nonneg_left h (mul_nonneg hs'.le ht),
      sq_nonneg ((s : ℝ) * dist o (y k) - t * b k)]
  have htotal := sum_le_sum (s := univ) (fun k _ => step k)
  simp only [sum_add_distrib, ← mul_sum, sum_fiberwise] at htotal
  refine le_of_mul_le_mul_left ?_ hs'
  rw [sum_add_distrib]
  linarith only [htotal, budget]

variable [Fintype A]

/-- The fused widths on the retained lines, after dropping the nonnegative
contributions of omitted secants. Here `n + 1` counts *all* secants
through each point. This is the input from the spectral spaces argument. -/
def SecantBound (p : E → A) (l : E → L) (x : A → Y) (o : Y) (n : ℕ) : Prop :=
  ∃ b : L → ℝ, (∑ k, b k ^ 2) ≤ n * ∑ a, dist o (x a) ^ 2 ∧
    ∀ k m, (∑ i with l i = k, dist o (x (p i)) ^ 2) ≤
      b k * dist o m + ∑ i with l i = k, dist o (x (p i)) * dist m (x (p i))

variable [DecidableEq A]

theorem uniform_sum (p : E → A) {j : ℕ} (hp : ∀ a, #{i | p i = a} = j) (f : A → ℝ) :
    ∑ i, f (p i) = j * ∑ a, f a := by
  rw [← sum_fiberwise univ p, mul_sum]
  refine sum_congr rfl fun a _ => ?_
  calc
    _ = ∑ i with p i = a, f a :=
      sum_congr rfl (fun i hi => congrArg f (mem_filter.mp hi).2)
    _ = _ := by rw [sum_const, hp, nsmul_eq_mul]

/-- The projective degrees are `s = q+1`, `j = n+1`. For affine points
of order `Q` with `q+1` retained directions they are `s = n = Q`,
`j = q+1`. In both cases `q*n ≤ j*s`. -/
theorem regular_incidence (C : Comparison Y) (p : E → A) (l : E → L)
    (x : A → Y) (y : L → Y) (o : Y) {j s n q : ℕ} (hs : 0 < s)
    (hp : ∀ a, #{i | p i = a} = j) (hl : ∀ k, #{i | l i = k} = s)
    (hd : q * n ≤ j * s) (h : SecantBound p l x o n) :
    (Real.sqrt q - 1) * (∑ i, (dist o (x (p i)) ^ 2 + dist o (y (l i)) ^ 2)) ≤
      Real.sqrt q * ∑ i, dist (x (p i)) (y (l i)) ^ 2 := by
  obtain ⟨b, hb, htrans⟩ := h
  apply incidence_of_widths C p l x y o b hs hl htrans (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (Nat.cast_nonneg _), uniform_sum p hp (fun a => dist o (x a) ^ 2)]
  calc
    _ ≤ q * (n * ∑ a, dist o (x a) ^ 2) := mul_le_mul_of_nonneg_left hb (Nat.cast_nonneg _)
    _ ≤ (j : ℝ) * s * (∑ a, dist o (x a) ^ 2) := by
      rw [← mul_assoc]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hd) (by positivity)
    _ = _ := by ring

theorem incidence_bound (C : Comparison Y) (p : E → A) (l : E → L)
    (x : A → Y) (y : L → Y) (o : Y) {j s n : ℕ} (hs : 0 < s)
    (hp : ∀ a, #{i | p i = a} = j) (hl : ∀ k, #{i | l i = k} = s)
    (hd : 100 * n ≤ j * s) (h : SecantBound p l x o n) :
    9 * (∑ i, (dist o (x (p i)) ^ 2 + dist o (y (l i)) ^ 2)) ≤
      10 * ∑ i, dist (x (p i)) (y (l i)) ^ 2 := by
  have e := regular_incidence C p l x y o hs hp hl hd h
  have hr : Real.sqrt 100 = 10 := by
    rw [show (100 : ℝ) = 10 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  norm_num [hr] at e
  exact e

end OAI.LinearAlgebra.MatrixExponent.Routing
end

section
/-! A slope in the base field, or the vertical direction. -/

namespace OAI.LinearAlgebra.MatrixExponent.Routing

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def projection (a : Fin 2 → V) : Option K → V
  | none => a 0
  | some t => a 1 - t • a 0

def affineGraph (i : (Fin 2 → V) × Option K) : Option K × V :=
  (i.2, projection i.1 i.2)

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! Finite arrangements of affine points and their secants. -/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset
open scoped Classical

variable {F : Type*} [Field F]

def through (a b : Fin 2 → F) : Option F × F :=
  if a 0 = b 0 then (none, a 0)
  else
    let d := (a 1 - b 1) / (a 0 - b 0)
    (some d, a 1 - d * a 0)

theorem through_left (a b : Fin 2 → F) :
    projection a (through a b).1 = (through a b).2 := by
  unfold through
  split <;> rfl

theorem through_right (a b : Fin 2 → F) :
    projection b (through a b).1 = (through a b).2 := by
  unfold through
  split
  · rename_i h
    exact h.symm
  · rename_i h
    simp only [projection, smul_eq_mul]
    linear_combination div_mul_cancel₀ (a 1 - b 1) (sub_ne_zero.mpr h)

theorem eq_through {a b : Fin 2 → F} {k : Option F × F} (h : a ≠ b)
    (ha : projection a k.1 = k.2) (hb : projection b k.1 = k.2) : k = through a b := by
  obtain ⟨_ | d, z⟩ := k
  · change a 0 = z at ha
    change b 0 = z at hb
    simp [through, ha, hb]
  · change a 1 - d * a 0 = z at ha
    change b 1 - d * b 0 = z at hb
    have h₀ : a 0 ≠ b 0 := by
      intro he
      rw [he] at ha
      have h₁ := sub_left_inj.mp (ha.trans hb.symm)
      apply h
      funext i
      fin_cases i <;> assumption
    have hd : d = (a 1 - b 1) / (a 0 - b 0) := by
      apply (eq_div_iff (sub_ne_zero.mpr h₀)).mpr
      linear_combination hb - ha
    simp [through, h₀, ← hd, ha]

variable {A : Type*} [Fintype A]

def secantLines (a : A → Fin 2 → F) : Finset (Option F × F) :=
  ({i : A × A | i.1 ≠ i.2} : Finset _).image (fun i => through (a i.1) (a i.2))

theorem mem_secantLines {a : A → Fin 2 → F} (ha : Function.Injective a) (k : Option F × F) :
    k ∈ secantLines a ↔ ∃ i j, i ≠ j ∧ projection (a i) k.1 = k.2 ∧
      projection (a j) k.1 = k.2 := by
  constructor
  · intro h
    obtain ⟨⟨i, j⟩, hij, rfl⟩ := mem_image.mp h
    exact ⟨i, j, (mem_filter.mp hij).2, through_left _ _, through_right _ _⟩
  · rintro ⟨i, j, hij, hi, hj⟩
    exact mem_image.mpr ⟨(i, j), mem_filter.mpr ⟨mem_univ _, hij⟩,
      (eq_through (ha.ne hij) hi hj).symm⟩

def pointSecants (a : A → Fin 2 → F) (i : A) : Finset (Option F × F) :=
  (secantLines a).filter fun k => projection (a i) k.1 = k.2

/-- Unit-mass conclusion of the secant argument, expressed with the
transport bounds for fused widths. `n+1` bounds the number of secants
through each marked point. -/
def Secants (F Y : Type*) [Field F] [MetricSpace Y] : Prop :=
  ∀ {A : Type} [Fintype A] (a : A → Fin 2 → F), Function.Injective a →
    ∀ n : ℕ, (∀ i, (pointSecants a i).card ≤ n + 1) →
    ∀ (x : A → Y) (o : Y), Bary x o →
    ∃ b : Option F × F → ℝ, (∑ k ∈ secantLines a, b k ^ 2) ≤ n * ∑ i, dist o (x i) ^ 2 ∧
      ∀ k ∈ secantLines a, ∀ m : Y, (∑ i with projection (a i) k.1 = k.2, dist o (x i) ^ 2) ≤
        b k * dist o m + ∑ i with projection (a i) k.1 = k.2, dist o (x i) * dist m (x i)

theorem Secants.widths {A L E : Type} [Fintype A] [Fintype L] [Fintype E] [DecidableEq L]
    {Y : Type*} [MetricSpace Y] (S : Secants F Y)
    (a : A → Fin 2 → F) (k : L → Option F × F)
    (ha : Function.Injective a) (hk : Function.Injective k)
    {n : ℕ} (hn : ∀ i, (pointSecants a i).card ≤ n + 1)
    (hmem : ∀ t, k t ∈ secantLines a) (p : E → A) (l : E → L)
    (he : Function.Injective fun i => (p i, l i))
    (hi : ∀ j t, projection (a j) (k t).1 = (k t).2 ↔ ∃ i, p i = j ∧ l i = t)
    (x : A → Y) (o : Y) (ho : Bary x o) : SecantBound p l x o n := by
  obtain ⟨b, hb, ht⟩ := S a ha n hn x o ho
  refine ⟨fun t => b (k t), ?_, fun t m => ?_⟩
  · refine le_trans ?_ hb
    rw [← sum_image (s := univ) (f := fun q => b q ^ 2) hk.injOn]
    exact sum_le_sum_of_subset_of_nonneg (image_subset_iff.mpr fun t _ => hmem t)
      (fun _ _ _ => sq_nonneg _)
  · have eqn (f : A → ℝ) :
        ∑ i with l i = t, f (p i) = ∑ j with projection (a j) (k t).1 = (k t).2, f j := by
      refine sum_bij (fun i _ => p i) ?_ ?_ ?_ (fun _ _ => rfl)
      · exact fun i h => mem_filter.mpr ⟨mem_univ _, (hi _ _).mpr ⟨i, rfl, (mem_filter.mp h).2⟩⟩
      · exact fun i h j h' e => he (Prod.ext e ((mem_filter.mp h).2.trans (mem_filter.mp h').2.symm))
      · intro j h
        obtain ⟨i, hp, hl⟩ := (hi _ _).mp (mem_filter.mp h).2
        exact ⟨i, mem_filter.mpr ⟨mem_univ _, hl⟩, hp⟩
    rw [eqn (fun j => dist o (x j) ^ 2), eqn (fun j => dist o (x j) * dist m (x j))]
    exact ht _ (hmem t) m

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Deleting singleton blocks

The collision parameters are the secant directions and infinity.
For a singleton block testing its own site in the transport inequality
shows that its width pays at least the distance from the center.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset
open scoped Classical

variable {F Y : Type*} [Field F] [MetricSpace Y] {A : Type} [Fintype A]

def directions (a : A → Fin 2 → F) : Finset (Option F) :=
  insert none ((secantLines a).image Prod.fst)

def blocks (a : A → Fin 2 → F) : Finset (Option F × F) :=
  (directions a ×ˢ univ).image (fun i => (i.1, projection (a i.2) i.1))

def pointsOn (a : A → Fin 2 → F) (k : Option F × F) : Finset A :=
  {i | projection (a i) k.1 = k.2}

theorem mem_blocks {a : A → Fin 2 → F} {k : Option F × F} :
    k ∈ blocks a ↔ k.1 ∈ directions a ∧ (pointsOn a k).Nonempty := by
  constructor
  · intro hk
    obtain ⟨⟨d, i⟩, hd, rfl⟩ := mem_image.mp hk
    exact ⟨(mem_product.mp hd).1, i, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩
  · rintro ⟨hd, i, hi⟩
    exact mem_image.mpr ⟨(k.1, i), mem_product.mpr ⟨hd, mem_univ _⟩,
      Prod.ext rfl (mem_filter.mp hi).2⟩

theorem secants_subset_blocks (a : A → Fin 2 → F) (ha : Function.Injective a) :
    secantLines a ⊆ blocks a := by
  intro k hk
  obtain ⟨i, _, _, hi, _⟩ := (mem_secantLines ha k).mp hk
  exact mem_blocks.mpr ⟨mem_insert_of_mem (mem_image_of_mem Prod.fst hk),
    i, mem_filter.mpr ⟨mem_univ i, hi⟩⟩

private theorem blocks_per_point (a : A → Fin 2 → F) (i : A) :
    #((blocks a).filter (fun k => projection (a i) k.1 = k.2)) = (directions a).card := by
  let f (d : Option F) := (d, projection (a i) d)
  have hf : Function.Injective f := fun _ _ e => congrArg Prod.fst e
  rw [← card_image_of_injective _ hf]
  congr 1
  ext k
  simp only [mem_filter, mem_image]
  constructor
  · rintro ⟨hk, hi⟩
    exact ⟨k.1, (mem_blocks.mp hk).1, Prod.ext rfl hi⟩
  · rintro ⟨d, hd, rfl⟩
    exact ⟨mem_blocks.mpr ⟨hd, i, mem_filter.mpr ⟨mem_univ _, rfl⟩⟩, rfl⟩

private theorem total_on_lines (a : A → Fin 2 → F) (r : A → ℝ)
    (s : Finset (Option F × F)) :
    ∑ k ∈ s, ∑ i ∈ pointsOn a k, r i =
      ∑ i, #({k ∈ s | projection (a i) k.1 = k.2}) * r i := by
  unfold pointsOn
  simp_rw [sum_filter]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [← sum_filter, sum_const, nsmul_eq_mul]

/-- Input from the rational-function fusion argument for sphere forms.
Finite collision parameters use the negative of the slope. -/
def CollisionBound (F Y : Type*) [Field F] [MetricSpace Y] : Prop :=
  ∀ {A : Type} [Fintype A] (a : A → Fin 2 → F), Function.Injective a → 1 < Fintype.card A →
    ∀ (x : A → Y) (o : Y), Bary x o →
    ∃ b : Option F × F → ℝ,
      (∑ k ∈ blocks a, b k ^ 2) ≤ ((directions a).card - 1 : ℝ) * ∑ i, dist o (x i) ^ 2 ∧
      ∀ k ∈ blocks a, ∀ m : Y, (∑ i ∈ pointsOn a k, dist o (x i) ^ 2) ≤
        b k * dist o m + ∑ i ∈ pointsOn a k, dist o (x i) * dist m (x i)

theorem CollisionBound.secants (H : CollisionBound F Y) : Secants F Y := by
  intro A _ a ha n hn x o ho
  rcases (secantLines a).eq_empty_or_nonempty with hempty | ⟨k, hk⟩
  · refine ⟨fun _ => 0, ?_, ?_⟩
    · rw [hempty, sum_empty]
      positivity
    · simp [hempty]
  obtain ⟨i, j, hij, _⟩ := (mem_secantLines ha k).mp hk
  have hcard : 1 < Fintype.card A := one_lt_card.mpr ⟨i, mem_univ _, j, mem_univ _, hij⟩
  obtain ⟨b, hbudget, ht⟩ := H a ha hcard x o ho
  have hsub := secants_subset_blocks a ha
  refine ⟨b, ?_, fun k hk => ht k (hsub hk)⟩
  let r (i : A) := dist o (x i) ^ 2
  let mass (k : Option F × F) := ∑ i ∈ pointsOn a k, r i
  have hall : ∑ k ∈ blocks a, mass k = (directions a).card * ∑ i, r i := by
    simp [mass, total_on_lines, blocks_per_point, ← mul_sum]
  have hsec : ∑ k ∈ secantLines a, mass k ≤ ((n : ℝ) + 1) * ∑ i, r i := by
    simp only [mass, total_on_lines, mul_sum]
    refine sum_le_sum fun i _ => mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
    exact_mod_cast hn i
  have hsing : ∑ k ∈ blocks a \ secantLines a, mass k ≤
      ∑ k ∈ blocks a \ secantLines a, b k ^ 2 := by
    refine sum_le_sum fun k hk => ?_
    obtain ⟨hb, hs⟩ := mem_sdiff.mp hk
    obtain ⟨i, hi⟩ := (mem_blocks.mp hb).2
    have he : pointsOn a k = {i} := by
      refine eq_singleton_iff_unique_mem.mpr ⟨hi, fun j hj => ?_⟩
      by_contra hne
      exact hs ((mem_secantLines ha k).mpr ⟨j, i, hne, (mem_filter.mp hj).2, (mem_filter.mp hi).2⟩)
    have hc := ht k hb (x i)
    simp only [he, sum_singleton, dist_self, mul_zero, add_zero] at hc
    simp only [mass, he, sum_singleton, r]
    nlinarith only [hc, sq_nonneg (b k - dist o (x i))]
  rw [← sum_sdiff hsub] at hall hbudget
  change _ ≤ (n : ℝ) * ∑ i, r i
  change _ ≤ _ * ∑ i, r i at hbudget
  linarith only [hall, hsec, hsing, hbudget]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-!
# Clearing all poles of the moving sphere form

A marked point (a,b) has moving position aX+bY. For each
pair of points remove its vanishing linear factor from the common
denominator. This gives a polynomial contraction kernel and works
over any coefficient algebra, including truncated local rings.
-/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Finset Polynomial Sphere
open scoped Classical

variable {F R : Type*} [Field F] [CommRing R] [Algebra F R]
variable {A : Type} [Fintype A] {r : ℕ}

def linearFactor (X Y : R) : Option F → R
  | none => Y
  | some s => X + algebraMap F R s * Y

def collisionOffset (a : Fin 2 → F) : Option F → F
  | none => a 1
  | some _ => a 0

def position (a : Fin 2 → F) (X Y : R) : R :=
  algebraMap F R (a 0) * X + algebraMap F R (a 1) * Y

def denominator (D : Finset (Option F)) (X Y : R) : R :=
  ∏ d ∈ D, linearFactor X Y d

def pole (a b : Fin 2 → F) := (through a b).1

def reciprocalPoly (D : Finset (Option F)) (a b : Fin 2 → F) (X Y : R) : R :=
  let d := pole a b
  algebraMap F R (collisionOffset b d - collisionOffset a d)⁻¹ * denominator (D.erase d) X Y

def polynomialKernel (a : A → Fin 2 → F) (X Y : R) (i j : A × Mode r) : R :=
  Sphere.coeff i.2 j.2 (reciprocalPoly (directions a) (a i.1) (a j.1) X Y)

def correlatorPoly (a : A → Fin 2 → F) (X Y : R) (xs : List (A × Mode r)) : R :=
  wick (polynomialKernel a X Y) xs

private theorem pole_comm (a b : Fin 2 → F) : pole b a = pole a b := by
  by_cases h : a = b
  · rw [h]
  exact congrArg Prod.fst (eq_through h (through_right b a) (through_left b a))

theorem polynomial_skew (a : A → Fin 2 → F) (x y : A × Mode r) :
    polynomialKernel a (Polynomial.X : Polynomial F) 1 y x =
      -polynomialKernel a Polynomial.X 1 x y := by
  unfold polynomialKernel reciprocalPoly
  rw [pole_comm (a x.1) (a y.1)]
  dsimp only
  rw [← neg_sub (collisionOffset (a y.1) _) (collisionOffset (a x.1) _), inv_neg, map_neg, neg_mul, coeff_skew]

theorem pole_mem (a : A → Fin 2 → F) (i j : A) : pole (a i) (a j) ∈ directions a := by
  by_cases h : i = j
  · simp [h, pole, through, directions]
  · exact mem_insert_of_mem (mem_image_of_mem Prod.fst
      (mem_image.mpr ⟨(i, j), mem_filter.mpr ⟨mem_univ _, h⟩, rfl⟩))

private theorem form_factor (d : Option F) :
    BinaryForm 1 (linearFactor (X : F[X]) 1 d) (linearFactor 1 X d) := by
  cases d with
  | none => simp [linearFactor, BinaryForm, reflect_one]
  | some s =>
    simp [linearFactor, BinaryForm, reflect_add, reflect_C]

private theorem form_denominator (D : Finset (Option F)) :
    BinaryForm D.card (denominator D (X : F[X]) 1) (denominator D 1 X) := by
  induction D using Finset.induction_on with
  | empty => simpa [denominator] using BinaryForm.const (1 : F)
  | @insert d D hd ih =>
    simpa [denominator, hd, Nat.add_comm] using (form_factor d).mul ih

theorem correlator_form (a : A → Fin 2 → F) (xs : List (A × Mode r)) :
    BinaryForm (((directions a).card - 1) * (weight xs / 2))
      (correlatorPoly a (X : F[X]) 1 xs) (correlatorPoly a 1 X xs) := by
  apply wick_form
  intro i j
  let D := directions a
  let d := pole (a i.1) (a j.1)
  let c := (collisionOffset (a j.1) d - collisionOffset (a i.1) d)⁻¹
  have hr := (BinaryForm.const c).mul (form_denominator (D.erase d))
  rw [zero_add, card_erase_of_mem (pole_mem a _ _)] at hr
  unfold polynomialKernel Sphere.coeff
  split
  · have ht := (BinaryForm.const
      ((-1 : F) ^ j.2.2 * (i.2.2 + j.2.2).choose j.2.2)).mul (hr.pow (i.2.2 + j.2.2 + 1))
    simpa [reciprocalPoly, c, d, D] using ht
  · exact BinaryForm.zero _

theorem correlator_map {S : Type*} [CommRing S] [Algebra F S] (f : R →ₐ[F] S)
    (a : A → Fin 2 → F) (X Y : R) (xs : List (A × Mode r)) :
    f (correlatorPoly a X Y xs) = correlatorPoly a (f X) (f Y) xs := by
  have hf (d : Option F) : f (linearFactor X Y d) = linearFactor (f X) (f Y) d := by
    cases d <;> simp [linearFactor]
  unfold correlatorPoly
  change f.toRingHom (wick _ _) = _
  rw [wick_hom]
  apply wick_eq_on
  intro i _ j _
  change f (polynomialKernel a X Y i j) = _
  simp only [polynomialKernel, Sphere.coeff]
  split <;> simp [reciprocalPoly, denominator, hf]

private theorem offset_ne (a b : Fin 2 → F) (h : a ≠ b) :
    collisionOffset b (pole a b) - collisionOffset a (pole a b) ≠ 0 := by
  by_cases h₀ : a 0 = b 0
  · have h₁ : a 1 ≠ b 1 := by
      intro he
      apply h
      funext j
      fin_cases j <;> assumption
    simpa [collisionOffset, pole, through, h₀] using sub_ne_zero.mpr h₁.symm
  · simpa [collisionOffset, pole, through, h₀] using sub_ne_zero.mpr (Ne.symm h₀)

private theorem factorization (a b : Fin 2 → F) (X Y : R) :
    let d := pole a b
    position b X Y - position a X Y =
      algebraMap F R (collisionOffset b d - collisionOffset a d) * linearFactor X Y d := by
  have eq : projection b (pole a b) = projection a (pole a b) :=
    (through_right a b).trans (through_left a b).symm
  generalize pole a b = d at *
  cases d with
  | none =>
    change b 0 = a 0 at eq
    simp only [collisionOffset, position, linearFactor, map_sub, eq]
    ring
  | some s =>
    change b 1 - s * b 0 = a 1 - s * a 0 at eq
    have e := congrArg (algebraMap F R) eq
    simp only [map_sub, map_mul] at e
    simp only [collisionOffset, position, linearFactor, map_sub]
    linear_combination Y * e

private theorem reciprocal_mul (D : Finset (Option F)) (a b : Fin 2 → F) (X Y : R)
    (h : a ≠ b) (hd : pole a b ∈ D) :
    reciprocalPoly D a b X Y * (position b X Y - position a X Y) = denominator D X Y := by
  rw [factorization]
  unfold reciprocalPoly
  dsimp only
  rw [mul_mul_mul_comm, ← map_mul, inv_mul_cancel₀ (offset_ne a b h), map_one, one_mul]
  exact prod_erase_mul _ _ hd

private theorem coeff_scale (x y : Mode r) (u v : R) :
    Sphere.coeff x y (u * v) = u ^ (x.2 + y.2 + 1) * Sphere.coeff x y v := by
  unfold Sphere.coeff
  split <;> simp [mul_pow, mul_left_comm, mul_assoc]

theorem correlator_specialize {E : Type*} [Field E] [Algebra F E] (a : A → Fin 2 → F) (X Y : E)
    (hD : denominator (directions a) X Y ≠ 0) (xs : List (A × Mode r)) :
    correlatorPoly a X Y xs = denominator (directions a) X Y ^ (weight xs / 2) *
      wick (fun i j => fieldKernel (position (a i.1) X Y, i.2) (position (a j.1) X Y, j.2)) xs := by
  rw [← wick_scale_energy]
  unfold correlatorPoly
  apply wick_eq_on
  intro i _ j _
  unfold polynomialKernel fieldKernel
  rw [← coeff_scale]
  congr 1
  by_cases h : a i.1 = a j.1
  · simp [h, reciprocalPoly]
  · have hm := reciprocal_mul (directions a) _ _ X Y h (pole_mem a _ _)
    have hn : position (a j.1) X Y - position (a i.1) X Y ≠ 0 := by
      intro hz
      exact hD (by rw [← hm, hz, mul_zero])
    exact (eq_mul_inv_iff_mul_eq₀ hn).mpr hm

def localX (z : R) : Option F → R
  | none => 1
  | some d => z - algebraMap F R d

def localY (z : R) : Option F → R
  | none => z
  | some _ => 1

theorem local_position (a : Fin 2 → F) (d : Option F) (z : R) :
    position a (localX z d) (localY z d) =
      algebraMap F R (projection a d) + z * algebraMap F R (collisionOffset a d) := by
  cases d <;> simp [position, projection, localX, localY, collisionOffset] <;> ring

private theorem shifted_inverse (u : R) (N : ℕ) (hu : u ^ N = 0) (δ Δ : F) (h : Δ ≠ 0) :
    (algebraMap F R Δ + u ^ 2 * algebraMap F R δ) *
      shifted u (algebraMap F R Δ⁻¹) (algebraMap F R (-δ)) N = 1 := by
  have he : algebraMap F R Δ⁻¹ * algebraMap F R Δ = 1 := by
    rw [← map_mul, inv_mul_cancel₀ h, map_one]
  rw [mul_comm, show algebraMap F R Δ + u ^ 2 * algebraMap F R δ =
    (1 - algebraMap F R (-δ) * u ^ 2 * algebraMap F R Δ⁻¹) * algebraMap F R Δ by
      rw [sub_mul, mul_assoc _ (algebraMap F R Δ⁻¹), he, map_neg]
      ring, ← mul_assoc, shifted_mul _ _ _ N hu, he]

private theorem local_reciprocal (D : Finset (Option F)) (a b : Fin 2 → F)
    (d : Option F) (hd : d ∈ D) (hp : pole a b ∈ D) (u : R) (N : ℕ) (hu : u ^ N = 0) :
    let X := localX (u ^ 2) d
    let Y := localY (u ^ 2) d
    let Δ := projection b d - projection a d
    let δ := collisionOffset b d - collisionOffset a d
    reciprocalPoly D a b X Y = denominator (D.erase d) X Y *
      (if Δ = 0 then algebraMap F R δ⁻¹
        else u ^ 2 * shifted u (algebraMap F R Δ⁻¹) (algebraMap F R (-δ)) N) := by
  intro X Y Δ δ
  by_cases he : a = b
  · simp [he, reciprocalPoly, Δ, δ]
  by_cases h : Δ = 0
  · rw [ite_eq_left h]
    have hpole : d = pole a b := congrArg Prod.fst
      (eq_through (k := (d, projection a d)) he rfl (sub_eq_zero.mp h))
    simp [reciprocalPoly, ← hpole, δ, mul_comm]
  · rw [ite_eq_right h]
    have eq : position b X Y - position a X Y =
        algebraMap F R Δ + u ^ 2 * algebraMap F R δ := by
      simp only [X, Y, Δ, δ, local_position, map_sub]
      ring
    have hm := reciprocal_mul D a b X Y he hp
    rw [eq, show denominator D X Y = denominator (D.erase d) X Y * u ^ 2 by
      rw [denominator, ← prod_erase_mul D _ hd]
      congr 1
      cases d <;> simp [linearFactor, X, Y, localX, localY]] at hm
    rw [← mul_assoc, ← hm, mul_assoc, shifted_inverse u N hu _ _ h, mul_one]

/-- After factoring a common scalar, the local polynomial is the
normalized motion kernel at every finite order. -/
theorem local_correlator (a : A → Fin 2 → F) (d : Option F) (hd : d ∈ directions a)
    (u : R) (N : ℕ) (hu : u ^ N = 0) (xs : List (A × Mode r)) :
    let X := localX (u ^ 2) d
    let Y := localY (u ^ 2) d
    correlatorPoly a X Y xs = denominator ((directions a).erase d) X Y ^ (weight xs / 2) *
      wick (clusterKernel u N (fun i => projection (a i) d) (fun i => collisionOffset (a i) d)) xs := by
  intro X Y
  rw [← wick_scale_energy]
  unfold correlatorPoly
  apply wick_eq_on
  intro i _ j _
  unfold polynomialKernel clusterKernel
  rw [local_reciprocal (directions a) _ _ d hd (pole_mem a _ _) u N hu, coeff_scale]

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! Reading polynomial coefficients from truncated local fusion identities. -/

noncomputable section

namespace OAI.LinearAlgebra.MatrixExponent.Routing

open Polynomial Sphere Finset
open scoped Classical

variable {F : Type*} [Field F] {A : Type} [Fintype A] {r : ℕ}

private theorem jet_local (a : A → Fin 2 → F) (d : Option F) (xs : List (A × Mode r))
    {i N : ℕ} (hi : i ≤ N) (hN : ((directions a).card - 1) * (weight xs / 2) = N) :
    jetAt N d i (correlatorPoly a (X : F[X]) 1 xs) =
      (correlatorPoly a (localX (X ^ 2 : F[X]) d) (localY (X ^ 2) d) xs).coeff (2 * i) := by
  have he := correlator_map (expand F 2) a (localX (X : F[X]) d) (localY X d) xs
  have he' : expand F 2 (correlatorPoly a (localX (X : F[X]) d) (localY X d) xs) =
      correlatorPoly a (localX (X ^ 2 : F[X]) d) (localY (X ^ 2) d) xs := by
    cases d <;> simpa [localX, localY] using he
  rw [← he', coeff_expand_mul' (by decide : 0 < 2)]
  cases d with
  | none =>
    change _ = (correlatorPoly a 1 X xs).coeff i
    rw [← (correlator_form a xs).2, hN, coeff_reflect, revAt_le hi]
    rfl
  | some s =>
    change ((taylor (-s)) (correlatorPoly a X 1 xs)).coeff i = _
    have hc := correlator_map (aeval (X - C s)) a X 1 xs
    simp only [aeval_X, map_one] at hc
    rw [taylor_apply, map_neg, ← sub_eq_add_neg]
    exact congrArg (fun P : F[X] => P.coeff i) hc

abbrev JetRing (F : Type*) [Field F] (M : ℕ) := AdjoinRoot (X ^ M : F[X])
def jetVar (F : Type*) [Field F] (M : ℕ) : JetRing F M := AdjoinRoot.mk (X ^ M) X

theorem jetVar_pow (F : Type*) [Field F] (M : ℕ) : jetVar F M ^ M = 0 := by
  rw [jetVar, ← map_pow, AdjoinRoot.mk_eq_zero]

private theorem jetRing_coeff {M i : ℕ} (hi : i < M) (P Q : F[X])
    (h : AdjoinRoot.mkₐ (X ^ M) P = AdjoinRoot.mkₐ (X ^ M) Q) : P.coeff i = Q.coeff i := by
  have e := X_pow_dvd_iff.mp (AdjoinRoot.mk_eq_mk.mp h) i hi
  rwa [coeff_sub, sub_eq_zero] at e

variable {B T : Type*} [Fintype T]

/-- The same scalar multiplies all coordinates, so after clearing the
denominator the jet still lies in the span of low energy terms. -/
theorem jets_of_fusion (a : A → Fin 2 → F) (xs : B → List (A × Mode r))
    (d : Option F) (hd : d ∈ directions a) (H N M : ℕ)
    (hw : ∀ b, weight (xs b) / 2 = H) (hN : ((directions a).card - 1) * H = N)
    (hM : 2 * N < M) (term : T → B → F) (cost : T → ℕ)
    (hf : ∀ b, wick (clusterKernel (jetVar F M) M
        (fun i => projection (a i) d) (fun i => collisionOffset (a i) d)) (xs b) =
      ∑ t, jetVar F M ^ cost t * algebraMap F (JetRing F M) (term t b))
    (i : ℕ) (hi : i ≤ N) :
    (fun b => jetAt N d i (correlatorPoly a (X : F[X]) 1 (xs b))) ∈
      Submodule.span F {v | ∃ t, cost t ≤ 2 * i ∧ term t = v} := by
  let f := AdjoinRoot.mkₐ (X ^ M : F[X])
  let u := jetVar F M
  let x := localX (X ^ 2 : F[X]) d
  let y := localY (X ^ 2 : F[X]) d
  let Q := denominator ((directions a).erase d) x y ^ H
  have hX : f X = u := rfl
  have hC (z : F) : f (C z) = AdjoinRoot.of (X ^ M) z := rfl
  have hx : f x = localX (u ^ 2) d := by cases d <;> simp [x, localX, hX, hC]
  have hy : f y = localY (u ^ 2) d := by cases d <;> simp [y, localY, hX]
  have hq : f Q = denominator ((directions a).erase d) (localX (u ^ 2) d) (localY (u ^ 2) d) ^ H := by
    have hl (k : Option F) : f (linearFactor x y k) = linearFactor (f x) (f y) k := by
      cases k <;> simp [linearFactor, hC]
    simp only [Q, denominator, map_pow, map_prod, hl, hx, hy]
  have he (b : B) : f (correlatorPoly a x y (xs b)) =
      f (∑ t, Q * X ^ (cost t) * C (term t b)) := by
    rw [correlator_map, hx, hy, local_correlator a d hd u M (jetVar_pow F M), hw, hf b,
      ← hq, mul_sum, map_sum]
    refine sum_congr rfl fun t _ => ?_
    rw [map_mul, map_mul, map_pow f X, hX, mul_assoc]
    rfl
  have eqn : (fun b => jetAt N d i (correlatorPoly a (X : F[X]) 1 (xs b))) =
      ∑ t, (Q * X ^ (cost t)).coeff (2 * i) • term t := by
    funext b
    rw [jet_local a d (xs b) hi (by rw [hw, hN]), jetRing_coeff (by omega : 2 * i < M) _ _ (he b)]
    simp only [finsetSum_coeff, coeff_mul_C, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [eqn]
  refine Submodule.sum_mem _ fun t _ => ?_
  by_cases h : cost t ≤ 2 * i
  · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨t, h, rfl⟩)
  · rw [coeff_mul_X_pow', ite_eq_right h, zero_smul]
    exact Submodule.zero_mem _

end OAI.LinearAlgebra.MatrixExponent.Routing
end
