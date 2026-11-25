import Mathlib.InformationTheory.Hamming
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Powerset
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.TreePrice
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.BigOperators.Field
import OAI.LinearAlgebra.MatrixExponent.Spectral.Span
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Rows
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

section
/-!
# Codes with prescribed slot words

A new word conflicts with an earlier word only if both the slot and
symbol match outside some set of `n` coordinates. Counting these sets
and the possibilities within them leaves room for a greedy assignment.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open Finset

variable {G H : Type*} [Fintype G] [Fintype H] [DecidableEq G] [DecidableEq H] {m n k b : ℕ}

private def vary (x : Fin m → G) (s : Finset (Fin m)) :=
  univ.filter fun y : Fin m → G => ∀ i ∉ s, y i = x i

private theorem vary_bound (x : Fin m → G) (s : Finset (Fin m)) :
    (vary x s).card ≤ Fintype.card G ^ s.card := by
  let f (y : vary x s) (i : s) := y.val i.val
  have hf : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ s
    · exact congrFun he ⟨i, hi⟩
    · exact ((mem_filter.mp y.property).2 i hi).trans ((mem_filter.mp z.property).2 i hi).symm
  simpa only [Fintype.card_fun, Fintype.card_coe] using Fintype.card_le_of_injective f hf

private theorem fresh (hn : n ≤ m)
    (hgap : 2 ^ m * (Fintype.card G ^ n * k * Fintype.card H ^ n) < Fintype.card H ^ m)
    (x : Fin m → G) (f : (Fin m → G) × Fin k → Fin m → H) :
    ∃ z : Fin m → H, ∀ p, n ≤ hammingDist (fun i => (x i, z i)) (fun i => (p.1 i, f p i)) := by
  let S := (univ : Finset (Fin m)).powersetCard n
  let bad (s : Finset (Fin m)) := ((vary x s) ×ˢ univ).biUnion (fun p => vary (f p) s)
  have hs : S.card ≤ 2 ^ m := by
    exact (card_le_card (show S ⊆ univ.powerset from fun _ h =>
      mem_powerset.mpr (mem_powersetCard.mp h).1)).trans_eq (by simp)
  have hc (s) (h : s ∈ S) : (bad s).card ≤ Fintype.card G ^ n * k * Fintype.card H ^ n := by
    have he := (mem_powersetCard.mp h).2
    calc
      _ ≤ ∑ p ∈ vary x s ×ˢ univ, (vary (f p) s).card := card_biUnion_le
      _ ≤ ∑ _ ∈ vary x s ×ˢ (univ : Finset (Fin k)), Fintype.card H ^ s.card :=
        sum_le_sum (fun p _ => vary_bound (f p) s)
      _ ≤ _ := by
        simp only [sum_const, nsmul_eq_mul, Nat.cast_id, card_product, card_univ, Fintype.card_fin, ← he]
        exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (vary_bound x s))
  have ht : (S.biUnion bad).card < (univ : Finset (Fin m → H)).card := by
    calc
      _ ≤ ∑ _ ∈ S, Fintype.card G ^ n * k * Fintype.card H ^ n :=
        card_biUnion_le.trans (sum_le_sum hc)
      _ ≤ 2 ^ m * (Fintype.card G ^ n * k * Fintype.card H ^ n) := by
        simpa using Nat.mul_le_mul_right _ hs
      _ < _ := by simpa using hgap
  obtain ⟨z, _, hz⟩ := exists_mem_notMem_of_card_lt_card ht
  refine ⟨z, fun p => ?_⟩
  by_contra! hh
  let D := univ.filter fun i => (x i, z i) ≠ (p.1 i, f p i)
  obtain ⟨s, hDs, hs, he⟩ := exists_subsuperset_card_eq (subset_univ D) hh.le (by simpa using hn)
  have hp i (hi : i ∉ s) : (x i, z i) = (p.1 i, f p i) := by
    by_contra h
    exact hi (hDs (mem_filter.mpr ⟨mem_univ _, h⟩))
  have hx : p.1 ∈ vary x s := mem_filter.mpr ⟨mem_univ _, fun i hi => (congrArg Prod.fst (hp i hi)).symm⟩
  have hy : z ∈ vary (f p) s := mem_filter.mpr ⟨mem_univ _, fun i hi => congrArg Prod.snd (hp i hi)⟩
  exact hz (mem_biUnion.mpr ⟨s, mem_powersetCard.mpr ⟨hs, he⟩, mem_biUnion.mpr
    ⟨p, mem_product.mpr ⟨hx, mem_univ _⟩, hy⟩⟩)

theorem code (hb : 0 < b) (hgap : 2 ^ b * Fintype.card G * Fintype.card H * k < Fintype.card H ^ b)
    (hn : 0 < n) :
    ∃ c : (Fin (b * n) → G) → Fin (k ^ n) → Fin (b * n) → H, ∀ x a y d, (x, a) ≠ (y, d) →
      n ≤ hammingDist (fun i => (x i, c x a i)) (fun i => (y i, c y d i)) := by
  classical
  have hH : 0 < Fintype.card H := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h, hb.ne'] at hgap
  let P := (Fin (b * n) → G) × Fin (k ^ n)
  have hsize : 2 ^ (b * n) * (Fintype.card G ^ n * k ^ n * Fintype.card H ^ n) <
      Fintype.card H ^ (b * n) := by
    rw [pow_mul, pow_mul]
    simpa only [mul_pow, mul_assoc, mul_comm, mul_left_comm] using
      pow_lt_pow_left₀ hgap zero_le hn.ne'
  have assign (s : Finset P) : ∃ f : P → Fin (b * n) → H, ∀ x ∈ s, ∀ y ∈ s, x ≠ y →
      n ≤ hammingDist (fun i => (x.1 i, f x i)) (fun i => (y.1 i, f y i)) := by
    induction s using Finset.induction_on with
    | empty => exact ⟨fun _ _ => Classical.choice (Fintype.card_pos_iff.mp hH), by simp⟩
    | @insert p s hp ih =>
      obtain ⟨f, hf⟩ := ih
      obtain ⟨z, hz⟩ := fresh (Nat.le_mul_of_pos_left _ hb) hsize p.1 f
      refine ⟨Function.update f p z, ?_⟩
      intro x hx y hy hxy
      rcases mem_insert.mp hx with rfl | hx <;> rcases mem_insert.mp hy with rfl | hy
      · exact (hxy rfl).elim
      · simpa [hxy.symm] using hz y
      · rw [hammingDist_comm]; simpa [hxy] using hz x
      · have hx' : x ≠ p := fun h => hp (h ▸ hx)
        have hy' : y ≠ p := fun h => hp (h ▸ hy)
        simpa [hx', hy'] using hf x hx y hy hxy
  obtain ⟨f, hf⟩ := assign univ
  exact ⟨fun x a => f (x, a), fun x a y d => hf (x, a) (mem_univ _) (y, d) (mem_univ _)⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-! # Sparse decoder rows and narrow factorizations with sparse right factors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open Finset Prices.Motion
open scoped Classical

variable {F X Y T I : Type} [Field F] [Fintype Y]

def Rows (M : Matrix X Y F) (p : ℝ) : Prop := ∀ x, (#{y | M x y ≠ 0} : ℝ) ≤ p

def Narrow (M : Matrix X Y F) (r p : ℝ) : Prop :=
  ∃ e : ℕ, e ≤ r ∧ ∃ (A : Matrix X (Fin e) F) (B : Matrix (Fin e) Y F), M = A * B ∧ Rows B p

def Packed (M : Matrix X Y F) (r p : ℝ) : Prop :=
  ∃ A B, M = A + B ∧ Rows A p ∧ Narrow B r p

variable {M N : Matrix X Y F} {p q r s : ℝ}

theorem Rows.bound (M : Matrix X Y F) : Rows M (Fintype.card Y) :=
  fun _ => Nat.cast_le.mpr (card_le_card (filter_subset _ _))

theorem Rows.mono (h : Rows M p) (hp : p ≤ q) : Rows M q := fun x => (h x).trans hp

theorem Rows.zero : Rows (0 : Matrix X Y F) 0 := by simp [Rows]

theorem Rows.add (h : Rows M p) (h' : Rows N q) : Rows (M + N) (p + q) := by
  intro x
  let A : Finset Y := {y | M x y ≠ 0}
  let B : Finset Y := {y | N x y ≠ 0}
  have hs : ({y | (M + N) x y ≠ 0} : Finset Y) ⊆ A ∪ B := by
    intro y hy
    simp only [A, B, mem_filter, mem_univ, true_and, mem_union, Matrix.add_apply] at *
    grind
  have he := (card_le_card hs).trans (card_union_le A B)
  exact (show (#{y | (M + N) x y ≠ 0} : ℝ) ≤ A.card + B.card by exact_mod_cast he).trans
    (add_le_add (h x) (h' x))

theorem Rows.sub (h : Rows M p) (h' : Rows N q) : Rows (M - N) (p + q) := by
  rw [sub_eq_add_neg]
  apply h.add
  simpa [Rows] using h'

theorem Narrow.of_factor [Fintype T] {A : Matrix X T F} {B : Matrix T Y F}
    (hM : M = A * B) (hT : (Fintype.card T : ℝ) ≤ r) (hB : Rows B p) : Narrow M r p := by
  let e := (Fintype.equivFin T).symm
  refine ⟨_, hT, fun x i => A x (e i), fun i => B (e i), ?_, fun i => hB (e i)⟩
  rw [hM]
  ext x y
  exact (e.sum_comp (fun i => A x i * B i y)).symm

theorem Narrow.mono (h : Narrow M r p) (hr : r ≤ s) (hp : p ≤ q) : Narrow M s q := by
  obtain ⟨e, he, A, B, hM, hB⟩ := h
  exact ⟨e, he.trans hr, A, B, hM, hB.mono hp⟩

theorem Narrow.trivial (M : Matrix X Y F) : Narrow M (Fintype.card Y) 1 := by
  apply Narrow.of_factor (Matrix.mul_one M).symm le_rfl
  intro y
  simp [Matrix.one_apply, show ({t | y = t} : Finset Y) = {y} by ext; simp [eq_comm]]

theorem Narrow.zero (p : ℝ) : Narrow (0 : Matrix X Y F) 0 p :=
  ⟨0, by simp, 0, 0, by simp, fun i => Fin.elim0 i⟩

theorem Narrow.add (h : Narrow M r p) (h' : Narrow N s p) : Narrow (M + N) (r + s) p := by
  obtain ⟨a, ha, A, B, rfl, hB⟩ := h
  obtain ⟨b, hb, C, D, rfl, hD⟩ := h'
  let L : Matrix X (Fin a ⊕ Fin b) F := fun x => Sum.elim (A x) (C x)
  let R : Matrix (Fin a ⊕ Fin b) Y F := Sum.elim B D
  apply Narrow.of_factor (A := L) (B := R) _ (by simpa using add_le_add ha hb)
  · rintro (i | i)
    · exact hB i
    · exact hD i
  · ext x y
    change (∑ i, A x i * B i y) + (∑ i, C x i * D i y) =
      ∑ i, L x i * R i y
    rw [Fintype.sum_sum_type]
    rfl

/-- A basis selected from the rows retains their support bound. -/
theorem Narrow.of_low [Fintype X] (h : Low M r) (hr : Rows M p) : Narrow M r p := by
  obtain ⟨T, _, hT, A, B, he⟩ := h
  have hdim : (M.rank : ℝ) ≤ r := by
    rw [he]
    exact (Nat.cast_le.mpr ((Matrix.rank_mul_le_left _ _).trans A.rank_le_card_width)).trans hT
  rw [Matrix.rank_eq_finrank_span_row] at hdim
  obtain ⟨v, hv, heq, _⟩ := Submodule.exists_fun_fin_finrank_span_eq F (Set.range M.row)
  choose e he using hv
  have hx (x) : M.row x ∈ Submodule.span F (Set.range v) := by
    rw [heq]
    exact Submodule.subset_span ⟨x, rfl⟩
  choose c hc using fun x => (Submodule.mem_span_range_iff_exists_fun _).mp (hx x)
  refine ⟨_, hdim, c, fun i => M (e i), ?_, fun i => hr (e i)⟩
  ext x y
  change M x y = ∑ i, c x i * M (e i) y
  have hh (i) : M (e i) y = v i y := congrFun (he i) y
  simp_rw [hh]
  simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row] using (congrFun (hc x) y).symm

theorem Packed.sum {ι : Type} {M : ι → Matrix X Y F} (t : Finset ι)
    (h : ∀ i ∈ t, Packed (M i) r p) (hp : 0 ≤ p) : Packed (∑ i ∈ t, M i) (t.card * r) (t.card * p) := by
  induction t using Finset.induction_on with
  | empty => simpa using (show Packed (0 : Matrix X Y F) 0 0 from ⟨0, 0, by simp, Rows.zero, Narrow.zero _⟩)
  | @insert i t hi ih =>
    obtain ⟨A, B, h₁, ha, hb⟩ := h i (mem_insert_self _ _)
    obtain ⟨C, D, h₂, hc, hd⟩ := ih (fun j hj => h j (mem_insert_of_mem hj))
    rw [sum_insert hi, card_insert_of_notMem hi, Nat.cast_add, Nat.cast_one, add_mul, add_mul, one_mul, one_mul]
    refine ⟨C + A, D + B, by rw [h₁, h₂]; abel, hc.add ha, ?_⟩
    exact (hd.mono le_rfl (le_add_of_nonneg_right hp)).add
      (hb.mono le_rfl (le_add_of_nonneg_left (by positivity)))


variable [Fintype I] [DecidableEq I]

private theorem product_rows (f : I → Y → F) (p : I → ℝ)
    (h : ∀ i, (#{y | f i y ≠ 0} : ℝ) ≤ p i) :
    (#{y : I → Y | (∏ i, f i (y i)) ≠ 0} : ℝ) ≤ ∏ i, p i := by
  let B i : Finset Y := {y | f i y ≠ 0}
  have he : ({y : I → Y | (∏ i, f i (y i)) ≠ 0} : Finset _) = Fintype.piFinset B := by
    ext y
    simp [B, prod_ne_zero_iff]
  rw [he, Fintype.card_piFinset, Nat.cast_prod]
  exact prod_le_prod₀ (by intros; positivity) (fun i _ => h i)

theorem Rows.prod (M : I → Matrix Y Y F) (p : I → ℝ) (h : ∀ i, Rows (M i) (p i)) :
    Rows (matPower M) (∏ i, p i) :=
  fun x => product_rows (fun i y => M i (x i) y) _ (fun i => h i _)

theorem Narrow.prod (M : I → Matrix Y Y F) (r p : I → ℝ) (h : ∀ i, Narrow (M i) (r i) (p i)) :
    Narrow (matPower M) (∏ i, r i) (∏ i, p i) := by
  choose e he A B hd hs using h
  let T := ∀ i, Fin (e i)
  let L : Matrix (I → Y) T F := fun x t => ∏ i, A i (x i) (t i)
  let R : Matrix T (I → Y) F := fun t y => ∏ i, B i (t i) (y i)
  apply Narrow.of_factor (A := L) (B := R)
  · ext x y
    change ∏ i, M i (x i) (y i) = ∑ t : T, L x t * R t y
    simp only [hd, Matrix.mul_apply, Fintype.prod_sum, prod_mul_distrib, L, R, T]
  · simp only [T, Fintype.card_pi, Fintype.card_fin, Nat.cast_prod]
    exact prod_le_prod₀ (by intros; positivity) (fun i _ => he i)
  · exact fun t => product_rows (fun i y => B i (t i) y) _ (fun i => hs i _)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-! # Multiscale approximation of a decoder -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open Finset Prices.Motion
open scoped Classical

variable {F Y : Type} [Field F] [Fintype Y] {M : Matrix Y Y F} {q : ℕ}

/-- Consecutive approximants give an exact expansion. Each difference
has controlled support and rank, including the two end terms. -/
theorem layers {D : ℝ} (hD : 1 ≤ D) (hc : (Fintype.card Y : ℝ) ≤ D)
    (P R : ℕ → Matrix Y Y F → Prop) (hz : P 0 0) (he : P (q + 1) M)
    (hs : ∀ j A B, P (j + 1) A → P j B → R j (A - B))
    (h : ∀ j : ℕ, 0 < j → j ≤ q → ∃ A, Low (M - A) (D ^ (1 - (j : ℝ) / q)) ∧ P j A) :
    ∃ W : Fin (q + 1) → Matrix Y Y F, M = ∑ j, W j ∧
      ∀ j, Low (W j) (2 * D ^ (1 - (j.val : ℝ) / q)) ∧ R j.val (W j) := by
  have hex (j : ℕ) : ∃ A, (j = 0 → A = 0) ∧ (j = q + 1 → A = M) ∧
      Low (M - A) (D ^ (1 - (j : ℝ) / q)) ∧ (j ≤ q + 1 → P j A) := by
    by_cases hj : j = 0
    · subst j
      refine ⟨0, fun _ => rfl, by omega, ?_, fun _ => hz⟩
      simpa using (Low.full M).mono hc
    by_cases hj' : j ≤ q
    · obtain ⟨A, hA, hP⟩ := h j (by omega) hj'
      exact ⟨A, by omega, by omega, hA, fun _ => hP⟩
    · refine ⟨M, by omega, fun _ => rfl, ?_, fun hlt => by rwa [show j = q + 1 by omega]⟩
      rw [sub_self]
      exact Low.zero.mono (by positivity)
  choose N h₀ h₁ hN hP using hex
  refine ⟨fun j => N (j.val + 1) - N j.val, ?_, fun j => ⟨?_, hs _ _ _ (hP _ (by omega)) (hP _ (by omega))⟩⟩
  · rw [Fin.sum_univ_eq_sum_range (fun i => N (i + 1) - N i), sum_range_sub, h₀ _ rfl, h₁ _ rfl, sub_zero]
  · change Low (N (j.val + 1) - N j.val) _
    rw [show N (j.val + 1) - N j.val = (M - N j.val) - (M - N (j.val + 1)) by abel, two_mul]
    apply (hN j.val).sub
    refine (hN (j.val + 1)).mono (Real.rpow_le_rpow_of_exponent_le hD ?_)
    gcongr
    omega

/-- Linear envelopes for the row costs suffice on the square grid. -/
theorem row_layers {D C l : ℝ} (hD : 1 ≤ D) (hc : (Fintype.card Y : ℝ) ≤ D)
    (hl : 1 ≤ l) (hq : (q : ℝ) = l * l) (hC : 1 ≤ C)
    (h : ∀ j : ℕ, 0 < j → j ≤ q → ∃ A, Low (M - A) (D ^ (1 - (j : ℝ) / q)) ∧
      Rows A (D ^ (C * Real.sqrt ((j : ℝ) / q)))) :
    ∃ W : Fin (q + 1) → Matrix Y Y F, M = ∑ j, W j ∧ ∀ j,
      Low (W j) (2 * D ^ (1 - (j.val : ℝ) / q)) ∧ Rows (W j) (2 * D ^ (C * ((j.val : ℝ) + 1) / l)) := by
  let p (j : ℕ) := D ^ (C * (j : ℝ) / l)
  have hp : Monotone p := by
    intro a b hab
    exact Real.rpow_le_rpow_of_exponent_le hD (by gcongr)
  have hlast : D ≤ p (q + 1) := by
    apply le_trans _ (hp (Nat.le_succ q))
    change D ≤ D ^ (C * q / l)
    rw [hq, ← mul_assoc, mul_div_cancel_right₀ _ (by linarith : l ≠ 0)]
    exact Real.self_le_rpow_of_one_le hD (one_le_mul_of_one_le_of_one_le hC hl)
  apply layers hD hc (fun j A => Rows A (p j)) (fun j A => Rows A (2 * D ^ (C * ((j : ℝ) + 1) / l)))
    (Rows.zero.mono (by dsimp [p]; positivity)) ((Rows.bound M).mono (hc.trans hlast))
  · intro j A B ha hb
    have H := ha.sub (hb.mono (hp (Nat.le_succ j)))
    simpa only [p, Nat.succ_eq_add_one, Nat.cast_add, Nat.cast_one, two_mul] using H
  · intro j hj hjq
    obtain ⟨A, he, ha⟩ := h j hj hjq
    refine ⟨A, he, ha.mono (Real.rpow_le_rpow_of_exponent_le hD ?_)⟩
    have h1 : (1 : ℝ) ≤ j := Nat.one_le_cast.mpr hj
    rw [hq, Real.sqrt_div (by positivity), Real.sqrt_mul_self (by linarith), ← mul_div_assoc]
    gcongr
    exact Real.sqrt_le_iff.mpr ⟨by positivity, by nlinarith⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-!
# Packing short rows on both sides of the decomposition

For a product of layers of total index below the threshold, pay for
every row. Otherwise select just enough high layers to reach the
threshold. Use a sparse row basis on those coordinates and the
identity on the rest.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
open Finset Prices.Motion
open scoped Classical

variable {F Y : Type} [Field F] [Fintype Y] {M : Matrix Y Y F} {q : ℕ}

private theorem select (v : Fin q → ℝ) (hv : ∀ i, v i ≤ q) (s : Finset (Fin q))
    (h : (q : ℝ) ≤ ∑ i ∈ s, v i) :
    ∃ t ⊆ s, (q : ℝ) ≤ ∑ i ∈ t, v i ∧ ∑ i ∈ t, v i ≤ 2 * q := by
  induction s using Finset.induction_on with
  | empty => exact ⟨∅, Subset.rfl, h, by simp⟩
  | @insert a s ha ih =>
    by_cases hs : (q : ℝ) ≤ ∑ i ∈ s, v i
    · obtain ⟨t, ht, hv⟩ := ih hs
      exact ⟨t, ht.trans (subset_insert _ _), hv⟩
    · refine ⟨_, Subset.rfl, h, ?_⟩
      rw [sum_insert ha]
      linarith [hv a]

private theorem product_bound {D b : ℝ} (hD : 1 ≤ D) (a : Fin q → ℝ)
    (ha : ∑ i, a i ≤ b) : ∏ i, (2 * D ^ (a i)) ≤ 2 ^ q * D ^ b := by
  rw [prod_mul_distrib, prod_const, card_fin, ← Real.rpow_sum_of_pos (by linarith)]
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hD ha) (by positivity)

private theorem collect_word {D C l : ℝ} (hD : 1 ≤ D) (hc : (Fintype.card Y : ℝ) ≤ D)
    (hl : 1 ≤ l) (hq : (q : ℝ) = l * l) (hC : 1 ≤ C)
    (W : Fin q → Matrix Y Y F) (v : Fin q → ℝ) (hv : ∀ i, v i ≤ q)
    (h : ∀ i, Low (W i) (2 * D ^ (1 - v i / q)) ∧ Rows (W i) (2 * D ^ (C * (v i + 1) / l))) :
    Packed (matPower W) (2 ^ q * D ^ ((q : ℝ) - 1)) (2 ^ q * D ^ (3 * C * l)) := by
  have hq' : 0 < (q : ℝ) := by rw [hq]; positivity
  have cost (u : Fin q → ℝ) (hu : ∑ i, u i ≤ 2 * q) :
      ∏ i, (2 * D ^ (C * (u i + 1) / l)) ≤ 2 ^ q * D ^ (3 * C * l) := by
    apply product_bound hD
    rw [← sum_div, ← mul_sum, sum_add_distrib, sum_const, card_fin, nsmul_eq_mul, mul_one]
    apply (div_le_iff₀ (by linarith)).mpr
    calc
      _ ≤ C * (2 * q + q) := by gcongr
      _ = _ := by rw [hq]; ring
  by_cases hsum : (q : ℝ) ≤ ∑ i, v i
  · obtain ⟨s, _, hlo, hhi⟩ := select v hv univ hsum
    let u i := if i ∈ s then v i else 0
    have hs : ∑ i, u i = ∑ i ∈ s, v i := by simp [u]
    have hh i : Narrow (W i) (2 * D ^ (1 - u i / q)) (2 * D ^ (C * (u i + 1) / l)) := by
      by_cases hi : i ∈ s
      · simp only [u, ite_eq_left hi]
        exact Narrow.of_low (h i).1 (h i).2
      · simp only [u, ite_eq_right hi, zero_div, sub_zero, Real.rpow_one, zero_add, mul_one]
        exact (Narrow.trivial _).mono (by linarith)
          (by linarith [Real.one_le_rpow hD (by positivity : 0 ≤ C / l)])
    have hr : ∑ i, (1 - u i / q) ≤ (q : ℝ) - 1 := by
      rw [sum_sub_distrib, sum_const, card_fin, nsmul_eq_mul, mul_one, ← sum_div, hs]
      exact sub_le_sub_left ((le_div_iff₀ hq').mpr (by simpa using hlo)) _
    exact ⟨0, _, by simp, Rows.zero.mono (by positivity),
      (Narrow.prod W _ _ hh).mono (product_bound hD _ hr) (cost u (hs.le.trans hhi))⟩
  · exact ⟨_, 0, by simp, (Rows.prod W _ (fun i => (h i).2)).mono (cost v (by linarith)),
      (Narrow.zero _).mono (by positivity) le_rfl⟩

theorem collect {D C l : ℝ} (hD : 1 ≤ D) (hc : (Fintype.card Y : ℝ) ≤ D)
    (hl : 1 ≤ l) (hq : (q : ℝ) = l * l) (hC : 1 ≤ C)
    (h : ∀ j : ℕ, 0 < j → j ≤ q → ∃ A, Low (M - A) (D ^ (1 - (j : ℝ) / q)) ∧
      Rows A (D ^ (C * Real.sqrt ((j : ℝ) / q)))) :
    Packed (matPower (fun _ : Fin q => M))
      ((2 * ((q : ℝ) + 1)) ^ q * D ^ ((q : ℝ) - 1)) ((2 * ((q : ℝ) + 1)) ^ q * D ^ (3 * C * l)) := by
  obtain ⟨W, he, hw⟩ := row_layers hD hc hl hq hC h
  have H (v : Fin q → Fin (q + 1)) := collect_word hD hc hl hq hC (W ∘ v)
    (fun i => ((v i).val : ℝ)) (fun i => Nat.cast_le.mpr (Nat.lt_succ_iff.mp (v i).isLt))
    (fun i => hw (v i))
  have eqn : matPower (fun _ : Fin q => M) = ∑ v : Fin q → Fin (q + 1), matPower (W ∘ v) := by
    ext x y
    simp only [matPower, he, Matrix.sum_apply, Fintype.prod_sum, Function.comp_apply]
  rw [eqn]
  have hh := Packed.sum univ (fun v _ => H v) (by positivity)
  simpa [mul_pow, mul_left_comm, mul_comm, mul_assoc] using hh

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Interior
end

/-! # Finite decompositions and polynomial paths for grouped speedup -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
open Spectral Finset

abbrev Leg := Fin 3
abbrev Family (R : Type) (X : Leg → Type) (n : ℕ) := Fin n → (s : Leg) → X s → R

def form {R : Type} [CommSemiring R] {X : Leg → Type} {n : ℕ} (A : Family R X n)
    (x : ∀ s, X s) : R := ∑ l, ∏ s, A l s (x s)

variable {K : Type} [Field K] {X : Leg → Type} [∀ s, Fintype (X s)] {n : ℕ}

abbrev table (T : (∀ s, X s) → K) := Tensor.ofRaw (Raw.ofTable X T)

def raw (A : Family K X n) : Raw K Leg := ⟨X, Fin n, A⟩

theorem table_form (A : Family K X n) : table (form A) = Tensor.ofRaw (raw A) :=
  Tensor.ofRaw_eq (Raw.equiv_coeff (fun _ => Equiv.refl _) (Raw.coeff_ofTable _ _))

theorem form_le (A : Family K X n) : table (form A) ≤ n := by
  rw [table_form]
  have h := Tensor.le_term_count (raw A)
  change _ ≤ (Fintype.card (Fin n) : Tensor K Leg) at h
  rwa [Fintype.card_fin] at h

theorem exists_form {T : (∀ s, X s) → K} (h : table T ≤ n) : ∃ A : Family K X n, T = form A := by
  rw [← Tensor.diag_fin] at h
  obtain ⟨L, hL⟩ := h
  change (s : Leg) → X s → Fin n → K at L
  refine ⟨fun l s y => L s y l, funext fun x => ?_⟩
  have he := (Raw.coeff_ofTable X T x).symm.trans (hL x)
  change T x = ∑ i : Fin n, ∏ s, ∑ j : Fin n, L s (x s) j * if j = i then 1 else 0 at he
  simpa [form, mul_ite] using he

theorem table_add_le (A B : (∀ s, X s) → K) : table (A + B) ≤ table A + table B := by
  simpa using Tensor.span_le X (A + B) (fun i : Bool => if i then A else B)
    (fun _ => 1) (fun _ => by simp)

theorem wire_le (A : Family K X n) (a b : Leg)
    (h : ∀ l m s, s ≠ a → s ≠ b → A l s = A m s) :
    table (form A) ≤ Tensor.wire K a b n := by
  rw [table_form]
  refine ⟨fun s x l => A l s x, fun x => ?_⟩
  change ∑ i, ∏ s, A i s (x s) =
    ∑ i, ∏ s, ∑ j, A j s (x s) * if j = Raw.port {a, b} s i then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, Fintype.sum_ite_eq']
  refine sum_congr rfl fun i _ => prod_congr rfl fun s _ => ?_
  by_cases he : s ∈ ({a, b} : Finset Leg)
  · rw [Raw.port, ite_eq_left he]
  · simp only [mem_insert, mem_singleton, not_or] at he
    exact congrFun (h i _ s he.1 he.2) _

/-- A polynomial path stays in the Zariski closure if it is in the
set except possibly at the finitely many roots of a nonzero polynomial. -/
theorem path_closure {K : Type*} [Field K] [Infinite K] {ι : Type} {A : Set (ι → K)} (P : ι → Polynomial K)
    (Q : Polynomial K) (hQ : Q ≠ 0) (hP : ∀ t, Q.eval t ≠ 0 → (fun i => (P i).eval t) ∈ A) :
    ZClosure A (fun i => (P i).eval 0) := by
  intro p hp
  let R := MvPolynomial.eval₂ Polynomial.C P p
  have he (t : K) : R.eval t = MvPolynomial.eval (fun i => (P i).eval t) p := by
    change Polynomial.evalRingHom t R = _
    unfold R
    rw [MvPolynomial.hom_eval₂, show (Polynomial.evalRingHom t).comp Polynomial.C =
      RingHom.id K by ext; simp]
    rfl
  have hzero : Q * R = 0 := by
    apply Polynomial.funext
    intro t
    rw [Polynomial.eval_mul, Polynomial.eval_zero, he]
    by_cases ht : Q.eval t = 0
    · rw [ht, zero_mul]
    · rw [hp _ (hP t ht), mul_zero]
  rw [← he, (mul_eq_zero.mp hzero).resolve_left hQ, Polynomial.eval_zero]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
end

/-! # Adjoining a disjoint wire to the original three legs -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
open Spectral Finset

variable {K : Type} [Field K] {X : Leg → Type} {m n d : ℕ} {a b c : Leg}

theorem third (h : a ≠ b) : ∃ c : Leg, a ≠ c ∧ b ≠ c := by
  fin_cases a <;> fin_cases b <;> first | contradiction | decide

theorem prod_three (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c) (f : Leg → K) :
    ∏ s, f s = f a * f b * f c := by
  have he : {a, b, c} = (univ : Finset Leg) := by
    apply eq_univ_of_card
    simp [hab, hac, hbc, Leg]
  rw [← he]
  simp [hab, hac, hbc, mul_assoc]

def Spans (P : Family K X d) (A : Family K X m) : Prop :=
  ∀ s, ∃ u : Fin m → Fin d → K, ∀ j x, ∑ l, u j l * P l s x = A j s x

def extend (m : ℕ) (A : Family K X n) : Family K (fun s => X s ⊕ Fin m) n :=
  fun l s => Sum.elim (A l s) (fun _ => 0)

def extra (X : Leg → Type) (a b : Leg) (m : ℕ) : Family K (fun s => X s ⊕ Fin m) m :=
  fun l s => Sum.elim (fun _ => 0) (fun x => if x = Raw.port {a, b} s l then 1 else 0)

theorem Spans.extend {P : Family K X d} {A : Family K X m} (h : Spans P A) :
    Spans (extend m P) (extend m A) := by
  intro s
  obtain ⟨u, hu⟩ := h s
  refine ⟨u, fun j x => ?_⟩
  cases x <;> simp [Speedup.extend, hu]

theorem extra_const (a b : Leg) (l j : Fin m) (s : Leg) (ha : s ≠ a) (hb : s ≠ b) :
    extra (K := K) X a b m l s = extra X a b m j s := by
  have he : Raw.port {a, b} s l = Raw.port {a, b} s j := by simp [Raw.port, ha, hb]
  simp only [extra, he]

theorem form_append (P : Family K X d) (A : Family K X m) :
    form (Fin.append P A) = form P + form A := by
  funext x
  rw [form, Fin.sum_univ_add]
  simp [form]

theorem table_extra [∀ s, Fintype (X s)] (P : Family K X d) (A : Family K X m) (a b : Leg) :
    table (form (extend m P) + form (extend m A) + form (extra X a b m)) =
      table (form P + form A) + Tensor.wire K a b m := by
  let H := Fin.append P A
  have he : extend m H = Fin.append (extend m P) (extend m A) := by
    funext l s x
    refine Fin.addCases (fun i => ?_) (fun j => ?_) l <;> simp [H, extend]
  rw [← form_append, ← he, ← form_append P A, table_form]
  change _ = Tensor.ofRaw (raw H + Raw.wire K a b m)
  apply Tensor.ofRaw_eq
  refine Raw.equiv_coeff (fun _ => Equiv.refl _) ?_
  intro x
  change (∀ s, X s ⊕ Fin m) at x
  refine (Raw.coeff_ofTable _ _ x).trans ?_
  change _ = ∑ l : Fin (d + m) ⊕ Fin m, ∏ s, (raw H + Raw.wire K a b m).factor l s (x s)
  rw [Fintype.sum_sum_type]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
end

/-!
# Spanning pivot columns suffice

Interpolate the first `d` columns at each site to a padded basis.
Away from the roots of three minors, these columns span the whole leg.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
open Finset

variable {K : Type} [Field K] [Infinite K] {X : Leg → Type} [∀ s, Fintype (X s)] {d m : ℕ}

theorem spanning_dense (P : Family K X d) (A : Family K X m) (hd : ∀ s, Fintype.card (X s) ≤ d) :
    ZClosure {T | ∃ B : Family K X d, Spans B A ∧ T = form B + form A}
      (form P + form A) := by
  classical
  let e (s : Leg) : X s ↪ Fin d :=
    (Fintype.equivFin (X s)).toEmbedding.trans (Fin.castLEEmb (hd s))
  let B : Family (Polynomial K) X d := fun l s x =>
    (1 - Polynomial.X) * Polynomial.C (P l s x) + Polynomial.X * (if e s x = l then 1 else 0)
  let V (t : K) : Family K X d := fun l s x => (B l s x).eval t
  let M (s : Leg) : Matrix (X s) (X s) (Polynomial K) := fun x y => B (e s y) s x
  let N (t : K) (s : Leg) : Matrix (X s) (X s) K := fun x y => V t (e s y) s x
  have heval (t : K) (s : Leg) : (M s).det.eval t = (N t s).det :=
    (Polynomial.evalRingHom t).map_det (M s)
  have hone (s : Leg) : N 1 s = 1 := by
    ext x y
    simp [N, V, B, Matrix.one_apply, apply_ite]
  let Q := ∏ s, (M s).det
  have hQ : Q ≠ 0 := by
    have : Q.eval 1 = 1 := by simp [Q, Polynomial.eval_prod, heval, hone]
    intro hz
    simp [hz] at this
  let W x := form B x + Polynomial.C (form A x)
  have he (t : K) : (fun x => (W x).eval t) = form (V t) + form A := by
    funext x
    simp only [W, Pi.add_apply, form, V, Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_finsetSum, Polynomial.eval_prod]
  have hv : V 0 = P := by funext l s x; simp [V, B, apply_ite]
  rw [← hv, ← he]
  apply path_closure W Q hQ
  intro t ht
  refine ⟨V t, ?_, he t⟩
  intro s
  have hdet : (N t s).det ≠ 0 := by
    simp only [Q, Polynomial.eval_prod, heval, prod_ne_zero_iff] at ht
    exact ht s (mem_univ _)
  have hsurj : Function.Surjective (N t s).mulVec :=
    Matrix.mulVec_surjective_iff_isUnit.mpr ((Matrix.isUnit_iff_isUnit_det _).mpr
      (isUnit_iff_ne_zero.mpr hdet))
  choose c hc using fun j => hsurj (A j s)
  refine ⟨fun j l => ∑ y, if e s y = l then c j y else 0, fun j x => ?_⟩
  simp_rw [sum_mul, ite_mul, zero_mul]
  rw [sum_comm]
  simp only [Fintype.sum_ite_eq]
  simpa only [Matrix.mulVec, dotProduct, N, mul_comm] using congrFun (hc j) x

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
end

/-!
# Pole cancellation in one group

The pivot columns `P,Q` span the remaining columns `X,Y`. A pairing
of size `d` cancels all the poles from the perturbation. Its only
uncancelled correction is divisible by the path parameter.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
open Finset

variable {K : Type} [Field K] {d m : ℕ}

private theorem exchange (u : Fin m → Fin d → K) (P : Fin d → K) (X Y : Fin m → K)
    (h : ∀ j, ∑ l, u j l * P l = X j) :
    ∑ l, P l * (∑ j, u j l * Y j) = ∑ j, X j * Y j := by
  simp_rw [mul_sum, ← h, sum_mul]
  rw [sum_comm]
  exact sum_congr rfl fun _ _ => sum_congr rfl fun _ _ => by ring

theorem pole (P Q H : Fin d → K) (X Y Z E F : Fin m → K) (G : K)
    (u v : Fin m → Fin d → K) (hu : ∀ j, ∑ l, u j l * P l = X j)
    (hv : ∀ j, ∑ l, v j l * Q l = Y j) :
    ∃ W : Polynomial K,
      W.eval 0 = (∑ l, P l * Q l * H l) + (∑ j, X j * Y j * Z j) + (∑ j, E j * F j * G) ∧
      ∀ t : K, t ≠ 0 → W.eval t =
        (∑ l, P l * Q l * (H l + G / t ^ 4)) +
        (∑ j, (X j + t * E j) * (Y j + t * F j) * (Z j + G / t ^ 2)) +
        (∑ l, (P l + t ^ 3 * ∑ j, v j l * E j) *
          (Q l + t ^ 2 * ∑ j, u j l * (Y j + t * F j)) * (-G / t ^ 4)) := by
  let A l := ∑ j, v j l * E j
  let B t l := ∑ j, u j l * (Y j + t * F j)
  let C := Polynomial.C (R := K)
  let T := Polynomial.X (R := K)
  let W := C (∑ l, P l * Q l * H l) +
    (∑ j, (C (X j) + T * C (E j)) * (C (Y j) + T * C (F j)) * C (Z j)) +
    C (∑ j, E j * F j * G) -
    (∑ l, C (A l) * (∑ j, C (u j l) * (C (Y j) + T * C (F j)))) * (T * C G)
  have he (t : K) : W.eval t = (∑ l, P l * Q l * H l) +
      (∑ j, (X j + t * E j) * (Y j + t * F j) * Z j) +
      (∑ j, E j * F j * G) - (∑ l, A l * B t l) * (t * G) := by
    simp only [W, C, T, B, Polynomial.eval_finsetSum, Polynomial.eval_add, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
  refine ⟨W, by simp [he], fun t ht => ?_⟩
  have hB : ∑ l, P l * B t l = ∑ j, X j * (Y j + t * F j) := exchange u P X _ hu
  have hA : ∑ l, Q l * A l = ∑ j, Y j * E j := exchange v Q Y E hv
  have h₁ l : P l * Q l * (H l + G / t ^ 4) +
      (P l + t ^ 3 * A l) * (Q l + t ^ 2 * B t l) * (-G / t ^ 4) =
      P l * Q l * H l - P l * B t l * (G / t ^ 2) - Q l * A l * (G / t) - A l * B t l * (t * G) := by
    field_simp; ring
  have h₂ j : (X j + t * E j) * (Y j + t * F j) * (Z j + G / t ^ 2) =
      (X j + t * E j) * (Y j + t * F j) * Z j + X j * (Y j + t * F j) * (G / t ^ 2) +
        Y j * E j * (G / t) + E j * F j * G := by field_simp; ring
  change _ = _ + _ + ∑ l, (P l + t ^ 3 * A l) * (Q l + t ^ 2 * B t l) * (-G / t ^ 4)
  rw [add_right_comm, ← sum_add_distrib]
  simp only [h₁, h₂, sum_sub_distrib, sum_add_distrib, ← sum_mul, hA, hB, he]
  ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
end

/-! # A group of rank-one terms returns a larger disjoint pairing -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
open Spectral Finset

variable {K : Type} [Field K] [Infinite K] {X : Leg → Type} [∀ s, Fintype (X s)]
    {d m : ℕ} {a b : Leg}

theorem degeneration (P : Family K X d) (A E : Family K X m) (hm : 0 < m) (hab : a ≠ b)
    (hs : Spans P A) (he : ∀ j l s, s ≠ a → s ≠ b → E j s = E l s) :
    ZClosure {T | table T ≤ (d : Tensor K Leg) + (m : Tensor K Leg) + Tensor.wire K a b d}
      (form P + form A + form E) := by
  obtain ⟨c, hac, hbc⟩ := third hab
  obtain ⟨u, hu⟩ := hs a
  obtain ⟨v, hv⟩ := hs b
  let G := E ⟨0, hm⟩
  have hG j : E j c = G c := he j _ c hac.symm hbc.symm
  let P' (t : K) : Family K X d := fun l s x =>
    if s = c then P l s x + G s x / t ^ 4 else P l s x
  let A' (t : K) : Family K X m := fun j s x =>
    if s = c then A j s x + G s x / t ^ 2 else A j s x + t * E j s x
  let B' (t : K) : Family K X d := fun l s x =>
    if s = a then P l s x + t ^ 3 * ∑ j, v j l * E j s x
    else if s = b then P l s x + t ^ 2 * ∑ j, u j l * (A j s x + t * E j s x)
    else -G s x / t ^ 4
  have hpath (x : ∀ s, X s) : ∃ W : Polynomial K,
      W.eval 0 = form P x + form A x + form E x ∧
      ∀ t, t ≠ 0 → W.eval t = form (P' t) x + form (A' t) x + form (B' t) x := by
    let atX {n : ℕ} (M : Family K X n) (s : Leg) l := M l s (x s)
    obtain ⟨W, h₀, hW⟩ := pole (atX P a) (atX P b) (atX P c) (atX A a) (atX A b)
      (atX A c) (atX E a) (atX E b) (G c (x c)) u v (fun j => hu j _) (fun j => hv j _)
    refine ⟨W, ?_, fun t ht => ?_⟩
    · simpa only [form, prod_three hab hac hbc, hG, atX] using h₀
    · simpa only [form, prod_three hab hac hbc, P', A', B', hac, hbc, hab.symm,
        hac.symm, hbc.symm, ↓reduceIte, atX] using hW t ht
  choose W h₀ hW using hpath
  rw [show form P + form A + form E = (fun x => (W x).eval 0) from (funext h₀).symm]
  apply path_closure W Polynomial.X Polynomial.X_ne_zero
  intro t ht
  rw [Polynomial.eval_X] at ht
  change table _ ≤ _
  rw [show (fun x => (W x).eval t) = form (P' t) + form (A' t) + form (B' t) from
    funext (fun x => hW x t ht)]
  have hB := wire_le (B' t) a b (fun l j s ha hb => by funext x; simp [B', ha, hb])
  have hadd {x y x' y' : Tensor K Leg} (hx : x ≤ x') (hy : y ≤ y') : x + y ≤ x' + y' :=
    (Tensor.add_le_add_right _ _ _ hx).trans (by
      rw [add_comm x' y, add_comm x' y']
      exact Tensor.add_le_add_right _ _ _ hy)
  exact (table_add_le _ _).trans (hadd
    ((table_add_le _ _).trans (hadd (form_le (P' t)) (form_le (A' t)))) hB)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup
end
