import OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding.Transfer
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile.Pairing
import OAI.LinearAlgebra.MatrixExponent.Upper.Tensor.Semiring
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Poly

/-!
# Graded actions on nested blocks

The distance counts all blocks on which two words differ, including
individual positions. This gives an edit bound without a logarithmic
charge per changed position.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Finset Prices.Motion
open scoped Classical

abbrev Tree : ℕ → Type → Type
  | 0, X => X
  | j + 1, X => Tree j (Block X)

instance treeFinite : (j : ℕ) → (X : Type) → [Fintype X] → Fintype (Tree j X)
  | 0, _, h => h
  | j + 1, X, _ => treeFinite j (Block X)

instance treeNonempty : (j : ℕ) → (X : Type) → [Nonempty X] → Nonempty (Tree j X)
  | 0, _, h => h
  | j + 1, X, _ => treeNonempty j (Block X)

variable {X Y F : Type} [Field F]

def treeOrder : (j : ℕ) → {X : Type} → Order X → Order (Tree j X)
  | 0, _, o => o
  | j + 1, _, o => treeOrder j o.block

def action : (j : ℕ) → {X : Type} → Matrix X X F → Matrix (Tree j X) (Tree j X) F
  | 0, _, A => A
  | j + 1, _, A => action j (matPower (fun _ : Fin 100 => A))

theorem action_mul [Fintype X] (j : ℕ) (A B : Matrix X X F) :
    action j (A * B) = action j A * action j B := by
  induction j generalizing X with
  | zero => rfl
  | succ j ih =>
    simp only [action]
    rw [matPower_mul, ih]

theorem tree_mono (j : ℕ) {p o : Order X} (h : ∀ x y, p.rel x y → o.rel x y) (x y : Tree j X)
    (he : (treeOrder j p).rel x y) : (treeOrder j o).rel x y := by
  induction j generalizing X with
  | zero => exact h x y he
  | succ j ih => exact ih (p := p.block) (o := o.block) (fun _ _ e i => h _ _ (e i)) x y he

theorem tree_focus [Fintype X] (j : ℕ) (o : Order X) {K : ℝ} (h : Focus o.grade K) :
    Focus (treeOrder j o).grade (10 ^ j * K) := by
  induction j generalizing X K with
  | zero => simpa [treeOrder] using h
  | succ j ih =>
    rw [pow_succ, mul_assoc]
    exact ih o.block h.block

theorem card_tree [Fintype X] (j : ℕ) : Fintype.card (Tree j X) = Fintype.card X ^ (100 ^ j) := by
  induction j generalizing X with
  | zero => simp [Tree]
  | succ j ih =>
    change Fintype.card (Tree j (Block X)) = _
    rw [ih, Fintype.card_fun, Fintype.card_fin, ← pow_mul, pow_succ']

def mismatch (x y : X) : ℝ := if x = y then 0 else 1

def next (c : X → X → ℝ) (x y : Block X) := mismatch x y + ∑ i, c (x i) (y i)

def fee : (j : ℕ) → {X : Type} → (X → X → ℝ) → Tree j X → Tree j X → ℝ
  | 0, _, c => c
  | j + 1, _, c => fee j (next c)

theorem fee_refl (j : ℕ) {c : X → X → ℝ} (h : ∀ x, c x x = 0) (x : Tree j X) :
    fee j c x x = 0 := by
  induction j generalizing X with
  | zero => exact h x
  | succ j ih => exact ih (c := next c) (by intro y; simp [next, mismatch, h]) x

theorem fee_nonneg (j : ℕ) {c : X → X → ℝ} (h : ∀ x y, 0 ≤ c x y) (x y : Tree j X) :
    0 ≤ fee j c x y := by
  induction j generalizing X with
  | zero => exact h x y
  | succ j ih =>
    apply ih (c := next c) _ x y
    intro u v
    exact add_nonneg (by unfold mismatch; positivity) (sum_nonneg (fun _ _ => h _ _))

theorem mismatch_triangle (x y z : X) : mismatch x z ≤ mismatch x y + mismatch y z := by
  unfold mismatch
  grind

theorem fee_triangle (j : ℕ) {c : X → X → ℝ} (h : ∀ x y z, c x z ≤ c x y + c y z)
    (x y z : Tree j X) : fee j c x z ≤ fee j c x y + fee j c y z := by
  induction j generalizing X with
  | zero => exact h _ _ _
  | succ j ih =>
    apply ih (c := next c) _ x y z
    intro u v w
    have hh := sum_le_sum (s := univ) fun i _ => h (u i) (v i) (w i)
    rw [sum_add_distrib] at hh
    unfold next
    linarith only [hh, mismatch_triangle u v w]

theorem mismatch_grade (o : Order X) {x y : X} (hr : o.rel x y) :
    mismatch x y ≤ (o.grade y : ℝ) - o.grade x := by
  unfold mismatch
  split_ifs with h
  · simp [h]
  have he : (o.grade x : ℝ) + 1 ≤ o.grade y := by exact_mod_cast o.inc hr h
  linarith

private theorem fee_grade (j : ℕ) (o : Order X) (d e : X → X → ℝ)
    (h : ∀ x y, o.rel x y → d x y ≤ e x y + ((o.grade y : ℝ) - o.grade x))
    (x y : Tree j X) (hr : (treeOrder j o).rel x y) :
    fee j d x y ≤ fee j e x y + (((treeOrder j o).grade y : ℝ) - (treeOrder j o).grade x) := by
  induction j generalizing X with
  | zero => exact h _ _ hr
  | succ j ih =>
    apply ih o.block (next d) (next e) _ x y hr
    intro u v h'
    have hh := sum_le_sum (s := univ) fun i _ => h (u i) (v i) (h' i)
    rw [sum_add_distrib, sum_sub_distrib] at hh
    simp only [next, Order.block, blockGrade, Nat.cast_sum]
    linarith only [hh]

theorem refine_fee (j : ℕ) (o : Order X) (x y : Tree j (Block X))
    (hr : (treeOrder j o.block).rel x y) :
    fee (j + 1) (@mismatch X) x y ≤ fee j (@mismatch (Block X)) x y +
      (((treeOrder j o.block).grade y : ℝ) - (treeOrder j o.block).grade x) := by
  apply fee_grade j o.block (next mismatch) mismatch _ x y hr
  intro u v h
  simp only [next, Order.block, blockGrade, Nat.cast_sum, ← sum_sub_distrib]
  exact add_le_add_right (sum_le_sum (fun i _ => mismatch_grade o (h i))) _

abbrev Word (m j : ℕ) (X : Type) := Fin m → Tree j X

def bits (m j : ℕ) := m * 100 ^ j

theorem card_word [Fintype X] (m j : ℕ) : Fintype.card (Word m j X) = Fintype.card X ^ bits m j := by
  rw [Fintype.card_fun, Fintype.card_fin, card_tree, ← pow_mul, mul_comm, bits]

def edits (m j : ℕ) (X : Type) (x y : Word m j X) := ∑ i, fee j (@mismatch X) (x i) (y i)

theorem edits_refl (m j : ℕ) (X : Type) (x : Word m j X) : edits m j X x x = 0 :=
  sum_eq_zero fun _ _ => fee_refl _ (fun _ => by simp [mismatch]) _

theorem edits_triangle (m j : ℕ) (X : Type) (x y z : Word m j X) :
    edits m j X x z ≤ edits m j X x y + edits m j X y z := by
  unfold edits; rw [← sum_add_distrib]
  exact sum_le_sum (fun _ _ => fee_triangle _ mismatch_triangle _ _ _)

def run (m j : ℕ) (A : Matrix X X F) : Matrix (Word m j X) (Word m j X) F :=
  matPower (fun _ => action j A)

theorem run_mul [Fintype X] (m j : ℕ) (A B : Matrix X X F) :
    run m j (A * B) = run m j A * run m j B := by
  unfold run; rw [action_mul, matPower_mul]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # Counting words by the blocks on which they differ -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Finset Real
open scoped Classical

variable {X : Type} [Fintype X]

private def Mass (c : X → X → ℝ) : Prop := ∀ x, ∑ y, exp (-100 * c x y) ≤ 2

private theorem Mass.parallel {c : X → X → ℝ} (h : Mass c) {m : ℕ} (x : Fin m → X) :
    ∑ y : Fin m → X, exp (-100*∑ i, c (x i) (y i)) ≤ 2 ^ m := by
  simp_rw [mul_sum, exp_sum]
  rw [← Fintype.prod_sum (fun i t => exp (-100 * c (x i) t))]
  simpa using prod_le_prod₀ (s := univ) (fun i _ => by positivity) (fun i _ => h (x i))

private theorem Mass.block {c : X → X → ℝ} (h : Mass c) (hr : ∀ x, c x x = 0) : Mass (next c) := by
  intro x
  have he : (2 : ℝ) ^ 100 ≤ exp 100 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2)
      (show (2 : ℝ) ≤ exp 1 by linarith [add_one_le_exp 1]) 100
    simpa only [← exp_nat_mul, Nat.cast_ofNat, mul_one] using hh
  calc
    _ ≤ ∑ y : Block X, ((if x = y then 1 else 0) + exp (-100) * exp (-100*∑ i, c (x i) (y i))) := by
      apply sum_le_sum
      intro y _
      unfold next mismatch
      by_cases hy : x = y
      · subst y; simp [hr, (exp_pos _).le]
      · simp [hy, mul_add, exp_add]
    _ ≤ 1 + exp (-100) * 2 ^ 100 := by
      rw [sum_add_distrib, ← mul_sum, Fintype.sum_ite_eq]
      exact add_le_add_right (mul_le_mul_of_nonneg_left (h.parallel x) (exp_nonneg _)) _
    _ ≤ 2 := by
      rw [exp_neg]
      linarith [(inv_mul_le_one₀ (exp_pos 100)).mpr he]

private theorem Mass.tree {c : X → X → ℝ} (h : Mass c) (hr : ∀ x, c x x = 0) (j : ℕ) :
    Mass (fee j c) := by
  induction j generalizing X with
  | zero => exact h
  | succ j ih => exact ih (h.block hr) (fun x => by simp [next, mismatch, hr])

theorem edits_mass (m j : ℕ) (x : Word m j Bool) :
    ∑ y, exp (-100 * edits m j Bool x y) ≤ 2 ^ m := by
  have h : Mass (@mismatch Bool) := by
    intro x
    simpa using sum_le_sum (s := univ) (fun y _ => show exp (-100 * mismatch x y) ≤ 1 from
      exp_le_one_iff.mpr (by unfold mismatch; split <;> norm_num))
  exact (h.tree (fun _ => by simp [mismatch]) j).parallel x

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # Pairing the corresponding bits of two registers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Prices.Motion Finset
open scoped Classical

variable {X Y F : Type} [Field F]

private def liftPair : (j : ℕ) → {X Y : Type} → (X → X → Y) → Tree j X → Tree j X → Tree j Y
  | 0, _, _, f => f
  | j + 1, _, _, f => liftPair j (fun x y i => f (x i) (y i))

def paired (m j : ℕ) (x : Word m j Bool × Word m j Bool) : Word m j (Col 1) :=
  fun i => liftPair j (fun a b => ![a, b]) (x.1 i) (x.2 i)

private theorem pair_cost (j : ℕ) (f : X → X → Y) (d : X → X → ℝ) (e : Y → Y → ℝ)
    (h : ∀ a b x y, f a b = f x y → a = x)
    (hle : ∀ a b x y, d a x ≤ e (f a b) (f x y)) (a b x y : Tree j X) :
    fee j d a x ≤ fee j e (liftPair j f a b) (liftPair j f x y) := by
  induction j generalizing X Y with
  | zero => exact hle _ _ _ _
  | succ j ih =>
    let g (u v : Block X) : Block Y := fun i => f (u i) (v i)
    have hg (u v r s : Block X) (he : g u v = g r s) : u = r :=
      funext fun i => h _ _ _ _ (congrFun he i)
    apply ih g (next d) (next e) hg _ a b x y
    intro u v r s
    apply add_le_add _ (sum_le_sum (fun i _ => hle (u i) (v i) (r i) (s i)))
    change mismatch u r ≤ mismatch (g u v) (g r s)
    by_cases he : g u v = g r s
    · rw [he, hg _ _ _ _ he]; simp [mismatch]
    · simp only [mismatch, ite_eq_right he]; split <;> norm_num

theorem paired_cost (m j : ℕ) (x y : Word m j Bool × Word m j Bool) :
    edits m j Bool x.1 y.1 ≤ edits m j (Col 1) (paired m j x) (paired m j y) := by
  have h (a b x y : Bool) (he : ![a, b] = ![x, y]) : a = x := congrFun he 0
  have hle (a b x y : Bool) : mismatch a x ≤ mismatch ![a, b] ![x, y] := by
    unfold mismatch
    split_ifs with h₁ h₂ <;> grind
  exact sum_le_sum (fun _ _ => pair_cost j _ _ _ h hle _ _ _ _)

private theorem pair_swap (j : ℕ) (f : X → X → Y) (A : Matrix Y Y F)
    (h : ∀ a b x y, A (f a b) (f x y) = if a = y ∧ b = x then 1 else 0)
    (a b x y : Tree j X) :
    action j A (liftPair j f a b) (liftPair j f x y) = if a = y ∧ b = x then 1 else 0 := by
  induction j generalizing X Y with
  | zero => exact h _ _ _ _
  | succ j ih =>
    let g (a b : Block X) : Block Y := fun i => f (a i) (b i)
    apply ih g (matPower (fun _ : Fin 100 => A)) _ a b x y
    intro a b x y
    simp only [matPower, g, h, Fintype.prod_ite_zero, prod_const_one, forall_and, ← funext_iff]
    split_ifs <;> rfl

theorem paired_swap (m j : ℕ) (x y : Word m j Bool × Word m j Bool) :
    run m j (exchange F Bool (1 : Fin 2)) (paired m j x) (paired m j y) =
      if x = (y.2, y.1) then 1 else 0 := by
  have h (a b x y : Bool) :
      exchange F Bool (1 : Fin 2) ![a, b] ![x, y] = if a = y ∧ b = x then 1 else 0 := by
    simp [exchange, swap, funext_iff, Fin.forall_fin_succ, eq_comm, and_comm]
  have he := pair_swap j (fun a b : Bool => ![a, b]) (exchange F Bool (1 : Fin 2))
    (by intro a b x y; rw [h]; split_ifs <;> rfl)
  simp only [run, matPower, paired, he, Fintype.prod_ite_zero, prod_const_one,
    forall_and, ← funext_iff, Prod.ext_iff]

theorem run_diagonal (m j : ℕ) (A : Matrix X X F) (h : ∀ x y, A x y ≠ 0 → x = y)
    (x y : Word m j X) (he : run m j A x y ≠ 0) : x = y := by
  induction j generalizing X with
  | zero =>
    change (∏ i, A (x i) (y i)) ≠ 0 at he
    exact funext fun i => h _ _ (prod_ne_zero_iff.mp he i (mem_univ _))
  | succ j ih =>
    apply ih (matPower (fun _ : Fin 100 => A)) _ x y he
    exact fun _ _ he => funext fun i => h _ _ (prod_ne_zero_iff.mp he i (mem_univ _))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # Composing ordered approximations and cutting off exceptional grades -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Finset Prices.Motion
open scoped Classical

variable {X F : Type} [Field F] [Fintype X]

/-- Discarding all transitions with either endpoint in an exceptional
set increases the rank loss by at most twice the size of the set. -/
theorem trim {A B : Matrix X X F} {b : ℝ} (h : Low (A - B) b) (S : Finset X) :
    ∃ C, Low (A - C) (b + 2 * S.card) ∧ ∀ x y, C x y ≠ 0 → x ∉ S ∧ y ∉ S ∧ B x y ≠ 0 := by
  let P := Matrix.diagonal (fun x : X => if x ∈ S then (1 : F) else 0)
  let Q := Matrix.diagonal (fun x : X => if x ∈ S then (0 : F) else 1)
  have hq : P = 1 - Q := by
    ext x y
    by_cases he : x = y
    · subst y; by_cases hx : x ∈ S <;> simp [P, Q, hx]
    · simp [P, Q, he]
  refine ⟨Q * B * Q, ?_, ?_⟩
  · have hp : Low P S.card := diag_low S
    rw [show A - Q * B * Q = (A - B) + (P * B + Q * B * P) by rw [hq, sub_mul, mul_sub, one_mul, mul_one]; abel,
      two_mul]
    exact h.add ((hp.right B).add (hp.left _))
  · intro x y hxy
    simpa [Q, Matrix.mul_diagonal, Matrix.diagonal_mul, mul_ite, ite_mul, and_comm, and_left_comm]
      using hxy

/-- The retained paths respect the order at every site. This controls
the finer blocks after the three parity factors are multiplied. -/
def Plan (j : ℕ) (o : Order X) (A : Matrix X X F) (K : ℝ) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (m : ℕ) (t : ℝ), 0 < t →
    ∃ B : Matrix (Word m j X) (Word m j X) F,
      Low (run m j A - B) (C * Fintype.card (Word m j X) * Real.exp (-t ^ 2 * bits m j)) ∧
      ∀ x y, B x y ≠ 0 →
        (∀ i, (treeOrder j o).rel (x i) (y i)) ∧ edits m j X x y ≤ K * t * bits m j

variable {j : ℕ} {o p : Order X} {A B : Matrix X X F} {K L : ℝ}

theorem Plan.of_order (h : Plan j o A K) (hp : ∀ x y, o.rel x y → p.rel x y) :
    Plan j p A K := by
  obtain ⟨C, hC, h⟩ := h
  refine ⟨C, hC, fun m t ht => ?_⟩
  obtain ⟨P, hP, hs⟩ := h m t ht
  refine ⟨P, hP, fun x y he => ?_⟩
  exact ⟨fun i => tree_mono _ hp _ _ ((hs x y he).1 i), (hs x y he).2⟩

theorem Plan.mul (h : Plan j o A K) (h' : Plan j o B L) : Plan j o (A * B) (K + L) := by
  obtain ⟨C, hC, h⟩ := h
  obtain ⟨D, hD, h'⟩ := h'
  refine ⟨C + D, add_nonneg hC hD, fun m t ht => ?_⟩
  obtain ⟨P, hP, hs⟩ := h m t ht
  obtain ⟨Q, hQ, hs'⟩ := h' m t ht
  refine ⟨P * Q, ?_, fun x y he => ?_⟩
  · rw [run_mul, add_mul, add_mul]
    exact approx_mul hP hQ
  · obtain ⟨z, _, hz⟩ := exists_ne_zero_of_sum_ne_zero he
    obtain ⟨hr, hd⟩ := hs x z (left_ne_zero_of_mul hz)
    obtain ⟨hr', hd'⟩ := hs' z y (right_ne_zero_of_mul hz)
    refine ⟨fun i => (treeOrder j o).trans (hr i) (hr' i), ?_⟩
    rw [add_mul, add_mul]
    exact (edits_triangle _ _ _ x z y).trans (add_le_add hd hd')

/-- Rescale the test on the coarse alphabet to the original word length. -/
theorem Focus.test (h : Focus o.grade K) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m (t : ℝ), 0 < t →
      ∃ S : Finset (Word m j X), (S.card : ℝ) ≤
        C * Fintype.card (Word m j X) * Real.exp (-t ^ 2 * bits m j) ∧
      ∀ x ∉ S, ∀ y ∉ S, height (treeOrder j o).grade y - height (treeOrder j o).grade x ≤
        K * t * bits m j := by
  obtain ⟨C, hC, h⟩ := tree_focus j o h
  refine ⟨C, hC, fun m t ht => ?_⟩
  obtain ⟨S, hS, hs⟩ := h (Fin m) (10 ^ j * t) (by positivity)
  have hb : (bits m j : ℝ) = m * ((10 : ℝ) ^ j) ^ 2 := by
    rw [bits, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, ← pow_mul, mul_comm j 2, pow_mul]
    norm_num
  simp only [Fintype.card_fin] at hS hs
  refine ⟨S, ?_, fun x hx y hy => (hs x hx y hy).trans_eq ?_⟩
  · rw [hb, show -t ^ 2 * (m * ((10 : ℝ) ^ j) ^ 2) = -(10 ^ j * t) ^ 2 * m by ring]
    exact hS
  · rw [hb]; ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-!
# Hierarchical elimination

Grouping a hundred blocks multiplies a grade's deviation coefficient
by ten. After parity elimination the middle coefficient is at most
`5K+2`, and the two outer coefficients are four each. Since
`5K+10 ≤ 7.5K`, there is room to charge one more level of edits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Finset Prices.Motion
open scoped Classical

variable {X F : Type} [Field F] [Fintype X] {o : Order X} {A : Matrix X X F} {K L : ℝ}

private theorem base (h : o.Unitriangular A) (hk : Focus o.grade K) (hK : 0 ≤ K) :
    Plan 0 o A (4 * K) := by
  obtain ⟨C, hC, hF⟩ := hk.test 0
  refine ⟨2 * C, by positivity, fun m t ht => ?_⟩
  obtain ⟨S, hS, hs⟩ := hF m t ht
  have hp : Low (run m 0 A - run m 0 A) 0 := by rw [sub_self]; exact Low.zero
  obtain ⟨P, hP, hp⟩ := trim hp S
  refine ⟨P, hP.mono (by linarith only [hS]), fun x y he => ?_⟩
  obtain ⟨hx, hy, hxy⟩ := hp x y he
  change (∏ i, A (x i) (y i)) ≠ 0 at hxy
  have hr i : o.rel (x i) (y i) := h.2 _ _ (prod_ne_zero_iff.mp hxy i (mem_univ _))
  refine ⟨hr, ?_⟩
  have hd := sum_le_sum (s := univ) fun i _ => mismatch_grade o (hr i)
  rw [sum_sub_distrib] at hd
  exact (hd.trans (hs x hx y hy)).trans (by gcongr; linarith)

private theorem refine_plan {j : ℕ} (hk : Focus o.grade K) (hL : L ≤ 30 * K)
    (hp : Plan j o.block (matPower (fun _ : Fin 100 => A)) L) : Plan (j + 1) o A (4 * K) := by
  obtain ⟨C, hC, hF⟩ := hk.test (j + 1)
  obtain ⟨D, hD, hP⟩ := hp
  refine ⟨D + 2 * C, by positivity, fun m t ht => ?_⟩
  have hb : (bits m (j + 1) : ℝ) = 100 * (bits m j : ℝ) := by
    simp only [bits, pow_succ, Nat.cast_mul, Nat.cast_ofNat]; ring
  obtain ⟨S, hS, hs⟩ := hF m t ht
  obtain ⟨P, hP, hp⟩ := hP m (10 * t) (by positivity)
  have he : -(10 * t) ^ 2 * bits m j = -t ^ 2 * bits m (j + 1) := by rw [hb]; ring
  rw [he] at hP
  change Low (run m (j + 1) A - P)
    (D * Fintype.card (Word m (j + 1) X) * Real.exp (-t ^ 2 * bits m (j + 1))) at hP
  obtain ⟨Q, hQ, hq⟩ := trim hP S
  refine ⟨Q, hQ.mono (by linarith only [hS]), fun x y he => ?_⟩
  obtain ⟨hx, hy, hxy⟩ := hq x y he
  obtain ⟨hr, hd⟩ := hp x y hxy
  refine ⟨hr, ?_⟩
  have hu := sum_le_sum (s := univ) fun i _ => refine_fee j o (x i) (y i) (hr i)
  rw [sum_add_distrib, sum_sub_distrib] at hu
  have hg := hs x hx y hy
  have hcost : L * (10 * t) * bits m j ≤ 3 * K * t * bits m (j + 1) := by
    rw [hb]
    linarith only [mul_le_mul_of_nonneg_right hL (by positivity : 0 ≤ t * bits m j)]
  exact (hu.trans (add_le_add (hd.trans hcost) hg)).trans_eq (by ring)

theorem elimination [Nonempty X] (j : ℕ) (h : o.Unitriangular A) (hk : Focus o.grade K)
    (hK : 4 ≤ K) : Plan j o A (4 * K) := by
  induction j generalizing X K with
  | zero => exact base h hk (by linarith)
  | succ j ih =>
    obtain ⟨P, Q, R, hP, hQ, hR, he⟩ := Order.factor (o.block_unit h)
    have hb (a : ℕ) : Focus (o.block.outer a).grade 4 :=
      binary_focus _ fun x => by unfold Order.outer; dsimp; split <;> omega
    have hm : Focus o.block.middle.grade ((10 * K + 4) / 2) := hk.block.half
    have h₁ : Plan j o.block P (4 * 4) := (ih hP (hb 1) le_rfl).of_order fun _ _ h => h.1
    have h₂ : Plan j o.block Q (4 * ((10 * K + 4) / 2)) :=
      (ih hQ hm (by linarith)).of_order fun _ _ h => h.1
    have h₃ : Plan j o.block R (4 * 4) := (ih hR (hb 0) le_rfl).of_order fun _ _ h => h.1
    exact refine_plan hk (by linarith) (he.symm ▸ (h₁.mul h₂).mul h₃)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # The dimension-independent swap estimate over an arbitrary field -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Prices.Motion Finset
open scoped Classical

private def shearOrder (b : Bool) : Order (Col 1) where
  rel x y := x = y ∨ x 0 = b ∧ y 0 ≠ b
  grade x := if x 0 = b then 0 else 1
  refl _ := Or.inl rfl
  trans h k := by grind
  inc h he := by obtain ⟨hx, hy⟩ := h.resolve_left he; simp [hx, hy]

variable {F : Type} [Field F]

private theorem triangular (b : Bool) (v : F) :
    (shearOrder b).Unitriangular (shear (1 : Fin 2) b v) := by
  have h (x : Col 1) (hx : starts 1 b x) : swap 1 x 0 ≠ b := by simpa [swap] using hx.2
  constructor
  · intro x
    by_cases hx : starts 1 b x
    · have he : x ≠ swap 1 x := fun he => h x hx ((congrFun he.symm 0).trans hx.1)
      simp [shear, hx, he]
    · simp [shear, hx]
  · intro x y he
    by_cases hxy : x = y
    · exact Or.inl hxy
    have hh : starts 1 b x ∧ y = swap 1 x := by
      by_contra h'
      by_cases hx : starts 1 b x
      · have hy : y ≠ swap 1 x := fun e => h' ⟨hx, e⟩
        simp [shear, hx, hy, Ne.symm hxy] at he
      · simp [shear, hx, Ne.symm hxy] at he
    exact Or.inr ⟨hh.1.1, hh.2 ▸ h x hh.1⟩

private theorem shear_plan (j : ℕ) (b : Bool) (v : F) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m (t : ℝ), 0 < t →
      Within (edits m j (Col 1)) (run m j (shear (1 : Fin 2) b v))
        (C * Fintype.card (Word m j (Col 1)) * Real.exp (-t ^ 2 * bits m j)) (16 * t * bits m j) := by
  have hu : Focus (shearOrder b).grade 4 :=
    binary_focus _ fun x => by unfold shearOrder; dsimp; split <;> omega
  obtain ⟨C, hC, h⟩ := elimination j (triangular b v) hu le_rfl
  refine ⟨C, hC, fun m t ht => ?_⟩
  obtain ⟨B, hB, hp⟩ := h m t ht
  refine ⟨B, hB, fun x y h => ?_⟩
  simpa only [show (4 : ℝ) * 4 = 16 by norm_num] using (hp x y h).2

theorem swap_bound (F : Type) [Field F] (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, SwapBound F (Word m j Bool) (edits m j Bool) (bits m j) C := by
  obtain ⟨C, hC, h⟩ := shear_plan j false (1 : F)
  obtain ⟨D, hD, h'⟩ := shear_plan j true (-1 : F)
  refine ⟨2 * C + D, by positivity, fun m t ht => ?_⟩
  have hd : Within (edits m j (Col 1)) (run m j (signs F (1 : Fin 2))) 0 0 := by
    apply Within.exact
    intro x y he
    have hh : x = y := run_diagonal m j _ (by
      intro u v hu
      by_contra hne
      simp [signs, hne] at hu) x y he
    rw [hh, edits_refl]
  have hs := h m t ht
  have hs' := h' m t ht
  have tri := edits_triangle m j (Col 1)
  have he := hs.mul (hs'.mul (hs.mul hd tri) tri) tri
  rw [← run_mul, ← run_mul, ← run_mul, ← exchange_shears] at he
  have hcard : (Fintype.card (Word m j (Col 1)) : ℝ) = (Fintype.card (Word m j Bool) : ℝ) ^ 2 := by
    rw [card_word, card_word]
    simp only [Col, Fintype.card_fun, Fintype.card_fin, Nat.reduceAdd, Nat.cast_pow]
    rw [← pow_mul, ← pow_mul, mul_comm]
  have hm : (run m j (exchange F Bool (1 : Fin 2))).submatrix (paired m j) (paired m j) =
      swapMatrix F (Word m j Bool) := by
    ext x y
    simp only [Matrix.submatrix_apply, paired_swap, swapMatrix]
    split_ifs <;> rfl
  obtain ⟨B, hB, hp⟩ := he.pull (paired m j)
  rw [hm, hcard] at hB
  refine ⟨B, hB.mono (by linarith), fun x y hxy => (paired_cost m j x y).trans ?_⟩
  linarith only [hp x y hxy]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # From displacement to row support on a binary alphabet -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Finset Prices.Motion Interior Real
open scoped Classical

variable {F W : Type} [Field F] [Fintype W]

private theorem volume {n : ℕ} [NeZero n] (d : W → W → ℝ) {V p : ℝ}
    (hV : 1 ≤ V) (hm : ∀ x, ∑ y, exp (-100 * d x y) ≤ V)
    {M : Matrix (Fin n → W) (Fin n → W) F}
    (h : ∀ x y, M x y ≠ 0 → ∑ i ∈ univ.erase 0, d (x i) (y i) ≤ p) :
    Rows M (Fintype.card W * V ^ n * exp (100 * p)) := by
  intro x
  let S : Finset (Fin n → W) := {y | M x y ≠ 0}
  let f (i : Fin n) (z : W) := if i = 0 then 1 else exp (-100 * d (x i) z)
  have hf i z : 0 ≤ f i z := by unfold f; split <;> positivity
  have hl (y) (hy : y ∈ S) : exp (-(100 * p)) ≤ ∏ i, f i (y i) := by
    rw [← prod_erase_mul _ _ (mem_univ 0), show f 0 (y 0) = 1 by simp [f], mul_one]
    have he : ∏ i ∈ univ.erase 0, f i (y i) = exp (-100*∑ i ∈ univ.erase 0, d (x i) (y i)) := by
      rw [mul_sum, exp_sum]
      exact prod_congr rfl (fun i hi => ite_eq_right (mem_erase.mp hi).1)
    rw [he, exp_le_exp]
    linarith [h x y (mem_filter.mp hy).2]
  have hr : ∏ i ∈ univ.erase (0 : Fin n), (∑ y, f i y) ≤ V ^ n := by
    apply le_trans (b := ∏ _i ∈ univ.erase (0 : Fin n), V)
    · apply prod_le_prod₀ (fun i _ => sum_nonneg fun y _ => hf i y)
      intro i hi
      simpa only [f, ite_eq_right (mem_erase.mp hi).1] using hm (x i)
    · rw [prod_const]
      exact pow_le_pow_right₀ hV (by simp)
  have hh : (S.card : ℝ) * exp (-(100 * p)) ≤ Fintype.card W * V ^ n := calc
    _ = ∑ _y ∈ S, exp (-(100 * p)) := by simp
    _ ≤ ∑ y ∈ S, ∏ i, f i (y i) := sum_le_sum hl
    _ ≤ ∑ y : Fin n → W, ∏ i, f i (y i) :=
      sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun y _ _ => prod_nonneg (fun i _ => hf _ _))
    _ ≤ _ := by
      rw [← Fintype.prod_sum, ← mul_prod_erase _ _ (mem_univ 0)]
      rw [show ∑ y, f 0 y = (Fintype.card W : ℝ) by simp [f]]
      exact mul_le_mul_of_nonneg_left hr (by positivity)
  rwa [exp_neg, ← div_eq_mul_inv, div_le_iff₀ (exp_pos _)] at hh

def coefficient : ℝ := 100000 / log 2

theorem one_le_coefficient : 1 ≤ coefficient := by
  rw [coefficient, le_div_iff₀ (log_pos (by norm_num))]
  linarith [log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

theorem binary_power (k : ℕ) {C η : ℝ} (hC : 0 ≤ C) (hη : 0 < η)
    (h : ∀ m, SwapBound F (Word m k Bool) (edits m k Bool) (bits m k) C) :
    ∃ H : ℝ, 0 ≤ H ∧ ∀ (m : ℕ) (M : Matrix (Word m k Bool) (Word m k Bool) F), ∃ N,
      Low (matPower (fun _ : Fin (2 ^ k) => M) - N) (H * ((2 : ℝ) ^ bits m k) ^ ((2 : ℝ) ^ k - 2 * η ^ 2)) ∧
      Rows N (((2 : ℝ) ^ bits m k) ^ (2 + coefficient * η * Real.sqrt ((2 : ℝ) ^ k))) := by
  obtain ⟨H, hH, hf⟩ := fold k hC (mul_pos (by norm_num : (0 : ℝ) < 2) hη)
  refine ⟨H, hH, fun m M => ?_⟩
  let b := bits m k
  let R := (2 : ℝ) ^ b
  have hR : 0 < R := by unfold R; positivity
  obtain ⟨N, hN, hcost⟩ := hf F _ _ b (edits_refl _ _ _) (edits_triangle _ _ _) (h m) M
  have hcard : (Fintype.card (Word m k Bool) : ℝ) = R := by rw [card_word]; simp [R, b]
  have hs := volume (edits m k Bool) (one_le_pow₀ (by norm_num)) (edits_mass _ _) hcost
  rw [hcard] at hN hs
  have he (x : ℝ) : R ^ x = exp (b * log 2 * x) := by rw [rpow_def_of_pos hR, show log R = b * log 2 from log_pow _ _]
  refine ⟨N, hN.mono ?_, hs.mono ?_⟩
  · change _ ≤ H * R ^ ((2 : ℝ) ^ k - 2 * η ^ 2)
    have hu : exp (-(2 * η) ^ 2 * b) ≤ R ^ (-(2 * η ^ 2)) := by
      rw [he, exp_le_exp]
      have hlog : log 2 ≤ 2 := (log_le_sub_one_of_pos (by norm_num)).trans (by norm_num)
      linarith only [mul_le_mul_of_nonneg_right hlog (show 0 ≤ 2 * η ^ 2 * b by positivity)]
    rw [sub_eq_add_neg, rpow_add hR, show (2 : ℝ) ^ k = ((2 ^ k : ℕ) : ℝ) by norm_cast, rpow_natCast, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hu (by positivity)
  · change _ ≤ R ^ (2 + coefficient * η * Real.sqrt ((2 : ℝ) ^ k))
    have hn : ((2 : ℝ) ^ m) ^ (2 ^ k : ℕ) ≤ R := by
      rw [← pow_mul]
      apply pow_le_pow_right₀ (by norm_num)
      exact Nat.mul_le_mul_left m (Nat.pow_le_pow_left (by norm_num : 2 ≤ 100) _)
    rw [rpow_add hR, rpow_two, pow_two, he]
    apply mul_le_mul (mul_le_mul_of_nonneg_left hn hR.le) _ (by positivity) (by positivity)
    apply le_of_eq
    congr 1
    unfold coefficient
    field_simp
    ring

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # Restricting from the next geometric alphabet size -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
open Finset Prices.Motion Interior Filter
open scoped Classical

variable {F W : Type} [Field F] [Fintype W]

private theorem restrict_power (n d : ℕ) (hd : 0 < d) (hd' : d ≤ Fintype.card W)
    {r p : ℝ} (h : ∀ M : Matrix W W F, ∃ N, Low (matPower (fun _ : Fin n => M) - N) r ∧ Rows N p)
    (B : Matrix (Fin d) (Fin d) F) : ∃ A, Low (matPower (fun _ : Fin n => B) - A) r ∧ Rows A p := by
  have : Nonempty (Fin d) := Fin.pos_iff_nonempty.mp hd
  let e : Fin d ↪ W := (Fin.castLEEmb hd').trans (Fintype.equivFin W).symm.toEmbedding
  let f (x : Fin n → Fin d) := e ∘ x
  have hf : Function.Injective f := fun _ _ he => funext fun i => e.injective (congrFun he i)
  let M := B.submatrix (Function.invFun e) (Function.invFun e)
  have he (x) := Function.leftInverse_invFun e.injective x
  obtain ⟨N, hr, hp⟩ := h M
  refine ⟨N.submatrix f f, ?_, fun x => ?_⟩
  · convert low_pull hr f using 1
    ext x y
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, M, f, matPower, Function.comp_apply, he]
  · apply le_trans _ (hp (f x))
    apply Nat.cast_le.mpr
    rw [← card_image_of_injective _ hf]
    apply card_le_card
    rintro y hy
    obtain ⟨z, hz, rfl⟩ := mem_image.mp hy
    exact mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hz).2⟩

private theorem upper_size (k d : ℕ) (hd : 1 ≤ d) : ∃ m : ℕ, d ≤ Fintype.card (Word m k Bool) ∧
    (2 : ℝ) ^ bits m k ≤ (2 : ℝ) ^ (100 ^ k : ℕ) * d := by
  let b := (2 : ℝ) ^ (100 ^ k : ℕ)
  have hb : 1 < b := one_lt_pow₀ (by norm_num) (by positivity)
  obtain ⟨j, hlo, hhi⟩ := exists_nat_pow_near (by exact_mod_cast hd : 1 ≤ (d : ℝ)) hb
  have he (m : ℕ) : (2 : ℝ) ^ bits m k = b ^ m := by rw [bits, mul_comm, pow_mul]
  refine ⟨j + 1, ?_, ?_⟩
  · rw [card_word, Fintype.card_bool]
    rw [← he] at hhi
    exact_mod_cast hhi.le
  · rw [he, pow_succ']
    exact mul_le_mul_of_nonneg_left hlo (by positivity)

/-- Constant-factor padding and the fixed interpolation cost are
absorbed by an arbitrarily small positive exponent. -/
private theorem absorb (k : ℕ) {H a b : ℝ} (hH : 0 ≤ H) (ha : 0 ≤ a) (hb : a < b) :
    ∀ᶠ d : ℕ in atTop, ∀ R : ℝ, 0 ≤ R → R ≤ (2 : ℝ) ^ (100 ^ k : ℕ) * d → H * R ^ a ≤ (d : ℝ) ^ b := by
  let U := (2 : ℝ) ^ (100 ^ k : ℕ)
  have hg := (tendsto_rpow_atTop (sub_pos.mpr hb)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop 1, hg.eventually_ge_atTop (H * U ^ a)] with d hd hh R hR hR'
  calc
    _ ≤ H * (U * d) ^ a := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hR hR' ha) hH
    _ = (H * U ^ a) * (d : ℝ) ^ a := by rw [Real.mul_rpow (by positivity) (by positivity), mul_assoc]
    _ ≤ (d : ℝ) ^ (b - a) * (d : ℝ) ^ a := mul_le_mul_of_nonneg_right hh (by positivity)
    _ = _ := by rw [← Real.rpow_add (by positivity), sub_add_cancel]

theorem of_swap (h : ∀ (F : Type) [Field F] (k : ℕ), ∃ C : ℝ, 0 ≤ C ∧
    ∀ m : ℕ, SwapBound F (Word m k Bool) (edits m k Bool) (bits m k) C) : Folds coefficient := by
  intro F _ k η hη he
  obtain ⟨C, hC, hs⟩ := h F k
  obtain ⟨H, hH, hh⟩ := binary_power k hC hη hs
  let p := coefficient * η * Real.sqrt ((2 : ℝ) ^ k)
  have hp : 0 ≤ p := by have := one_le_coefficient; unfold p; positivity
  have hr := absorb k hH (show 0 ≤ (2 : ℝ) ^ k - 2 * η ^ 2 by linarith)
    (show (2 : ℝ) ^ k - 2 * η ^ 2 < (2 : ℝ) ^ k - η ^ 2 by nlinarith)
  have hm := absorb k zero_le_one (show 0 ≤ 2 + p by linarith) (show 2 + p < 3 + p by linarith)
  filter_upwards [eventually_ge_atTop 1, hr, hm] with d hd h₁ h₂ B
  obtain ⟨m, hlo, hhi⟩ := upper_size k d hd
  obtain ⟨A, ha, hb⟩ := restrict_power _ _ (by omega) hlo (hh m) B
  exact ⟨A, ha.mono (h₁ _ (by positivity) hhi), hb.mono (by simpa only [one_mul] using h₂ _ (by positivity) hhi)⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Folding
end

/-! # Interpreting the three-leg tensor semiring on labelled sites -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Upper Spectral

local notation "CT" => OAI.MatrixMultiplication.Foundation.Tensor
variable {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z] [Fintype U] [Fintype V] [Fintype W]

private theorem restricts {A : CT Coeff X Y Z} {B : CT Coeff U V W}
    (h : CoefficientTensor.Restricts A B) : (triple A).Restricts (triple B) := by
  obtain ⟨a, b, c, rfl⟩ := h
  exact restricts_triple _ _ a b c fun _ _ _ => rfl

private def interp : TensorClass → Tensor Coeff Site :=
  Quotient.lift (fun A : TensorRep => Tensor.ofRaw (triple A.coeff))
    (fun _ _ h => Tensor.ofRaw_eq ⟨restricts h.1, restricts h.2⟩)

private theorem interp_tensor (T : CT Coeff X Y Z) :
    interp (TensorClass.ofTensor T) = Tensor.ofRaw (triple T) :=
  Tensor.ofRaw_eq ⟨restricts (TensorRep.ofTensor_restricts T), restricts (TensorRep.restricts_ofTensor T)⟩

private theorem read_mul (A B : Raw Coeff Site) :
    read (A * B) = OAI.MatrixMultiplication.Foundation.Tensor.product (read A) (read B) := by
  funext x y z
  rw [read, Raw.coeff_mul]
  unfold OAI.MatrixMultiplication.Foundation.Tensor.product read
  congr 2 <;> funext s <;> rcases s with _ | (_ | _) <;> rfl

private theorem read_add (A B : Raw Coeff Site) :
    read (A + B) = CoefficientTensor.blockSum (read A) (read B) := by
  funext x y z
  rw [read_apply]
  change (∑ i : A.term ⊕ B.term, (A + B).factor i (some false) x *
    (A + B).factor i (some true) y * (A + B).factor i none z) = _
  have h₁ (l : A.term) s (u : A.leg s ⊕ B.leg s) :
      (A + B).factor (.inl l) s u = Sum.elim (A.factor l s) (fun _ => 0) u := rfl
  have h₂ (l : B.term) s (u : A.leg s ⊕ B.leg s) :
      (A + B).factor (.inr l) s u = Sum.elim (fun _ => 0) (B.factor l s) u := rfl
  rw [Fintype.sum_sum_type]
  change A.leg (some false) ⊕ B.leg (some false) at x
  change A.leg (some true) ⊕ B.leg (some true) at y
  change A.leg none ⊕ B.leg none at z
  rcases x with x | x <;> rcases y with y | y <;> rcases z with z | z <;>
    simp [h₁, h₂, CoefficientTensor.blockSum, read_apply]

def interpret : TensorClass →+* Tensor Coeff Site where
  toFun := interp
  map_zero' := by
    change interp (TensorClass.ofTensor TensorClass.emptyTensor) = 0
    rw [interp_tensor, Tensor.ofRaw_eq_zero]
    exact fun x => Empty.elim (x none)
  map_one' := by
    change interp (TensorClass.ofTensor TensorClass.unitTensor) = Tensor.ofRaw 1
    rw [interp_tensor, ← triple_read (1 : Raw Coeff Site)]
    have he : read (1 : Raw Coeff Site) = TensorClass.unitTensor := by
      funext x y z
      change (∑ _ : Unit, ∏ _ : Site, (1 : Coeff)) = 1
      simp
    rw [he]
  map_mul' X Y := by
    refine Quotient.inductionOn₂ X Y fun A B => ?_
    change interp (TensorClass.ofTensor (OAI.MatrixMultiplication.Foundation.Tensor.product A.coeff B.coeff)) =
      Tensor.ofRaw (triple A.coeff * triple B.coeff)
    rw [interp_tensor, ← triple_read (triple A.coeff * triple B.coeff), read_mul,
      read_triple, read_triple]
    rfl
  map_add' X Y := by
    refine Quotient.inductionOn₂ X Y fun A B => ?_
    change interp (TensorClass.ofTensor (CoefficientTensor.blockSum A.coeff B.coeff)) =
      Tensor.ofRaw (triple A.coeff + triple B.coeff)
    rw [interp_tensor, ← triple_read (triple A.coeff + triple B.coeff), read_add,
      read_triple, read_triple]
    rfl

theorem interpret_tensor (T : CT Coeff X Y Z) :
    interpret (TensorClass.ofTensor T) = Tensor.ofRaw (triple T) := interp_tensor T

theorem interpret_mono : Monotone interpret :=
  fun X Y => Quotient.inductionOn₂ X Y fun _ _ h => restricts h

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end

/-! # Determinant and tripling for spectral points on labelled sites -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
open Upper Upper.TensorClass Spectral

private theorem interpret_dot :
    interpret (dotX 2) = Tensor.wire Coeff (some true) none 2 := by
  let W := Raw.wire Coeff (some true) none 2
  let T (x y z : Fin 2) : Coeff := if x = 0 ∧ y = z then 1 else 0
  have he : read W = T := by
    funext x y z
    change Fin 2 at x y z
    refine (read_apply W x y z).trans ?_
    change (∑ i : Fin 2, (if x = 0 then (1 : Coeff) else 0) *
      (if y = i then 1 else 0) * (if z = i then 1 else 0)) = T x y z
    by_cases he : x = 0 <;> simp [T, he, mul_ite]
  rw [dotX, interpret_tensor]
  change _ = Tensor.ofRaw W
  rw [← triple_read W, he]
  change Tensor.ofRaw (triple (CoefficientTensor.dotXCoeff 2)) = Tensor.ofRaw (triple T)
  let δ (x y : Fin 2) : Coeff := if x = y then 1 else 0
  apply Tensor.ofRaw_eq
  constructor
  · refine restricts_triple _ _ (fun x _ => δ x 0) δ δ fun x y z => ?_
    fin_cases x <;> fin_cases y <;> fin_cases z <;> simp [δ, T, CoefficientTensor.dotXCoeff]
  · refine restricts_triple _ _ (fun _ x => δ x 0) δ δ fun x y z => ?_
    fin_cases y <;> fin_cases z <;> simp [δ, T, CoefficientTensor.dotXCoeff, Fin.sum_univ_two]

theorem coeff_binary : BinaryLaw Coeff := by
  intro f hf p hp he m
  let g : Character := ⟨f.comp interpret, hf.comp interpret_mono⟩
  have hg : g.pX = p := by
    apply (Real.rpow_right_inj (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)).mp
    have hd := g.dotXValue_eq_rpow 2 (by decide)
    change (f (interpret (dotX 2)) : ℝ) = (2 : ℝ) ^ g.pX at hd
    rw [interpret_dot, he] at hd
    exact hd.symm
  have h := poly_row g (hg.symm ▸ hp) m
  rw [hg] at h
  change Row (fun n => (f (interpret (ofTensor (polynomialTensor (m + 1) (n + 1)))) : ℝ) ^ (1 / p))
    (fun n => (f (interpret (swapYZ (ofTensor (polynomialTensor (m + 1) (n + 1))))) : ℝ) ^ (1 / p)) m at h
  simp only [swapYZ_ofTensor, interpret_tensor] at h
  exact h

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Profile
end
