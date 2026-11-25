import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Geometry.SimpleLift
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Gaps
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Model
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Speedup.Dense
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Mask
import OAI.LinearAlgebra.MatrixExponent.Rectangle.FiniteModel
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Border.Price
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Geometry.Jacobian
import Mathlib.Algebra.BigOperators.Fin

universe u

/-!
# One small isolated system for generic matrix multiplication

The shared affine products come from a single accepting path.
The additional measurements lose at most the stated number of
independent output coordinates.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open scoped Classical
variable {F K : Type*} [Field F] [Field K] [Algebra F K]
  [CharZero K] [IsAlgClosed F] [IsAlgClosed K] {n : ℕ}

theorem isolated_jet (hn : 0 < n)
    {ι : Type*} {w : ι → ℝ} {S : Finset ι} {A : ι → Verifier F n} {c : ℝ}
    (hw : ∀ i ∈ S, 0 ≤ w i) (hc : ∀ i ∈ S, (A i).cost c)
    (gap : Gap w (fun i => (A i).accept) Correct S)
    {X : PairIndex n → K} (hx : AlgebraicIndependent F X) :
    ∃ q d : ℕ, (q : ℝ) ≤ 2 * c ∧ d ≤ n * n ∧ n * n ≤ S.card * (n * n - d) ∧
      ∃ (σ : Type) (_ : Fintype σ) (J : Jet F (PairIndex n) σ q d)
        (m : Fin d → K) (y : σ → K) (pos : Pos n n → σ),
          y ∘ pos = beta X ∧ Isolated y (Ideal.span (Set.range (J.system X m))) := by
  obtain ⟨l, hl, hs, p, hp, he⟩ := specialization hn hw hc gap hx
  obtain ⟨i, d, hd, hr, b, y, H, h⟩ := path_cut hl p X (beta X) he
  obtain ⟨J, m, hJ⟩ := (p i).jet X b (beta X) y H h
  have size : ((p i).equations.length : ℝ) ≤ 2 * (p i).code.length := by
    exact_mod_cast (p i).equations_length
  exact ⟨_, d, size.trans (mul_le_mul_of_nonneg_left (hp i) (by norm_num)), hd,
    hr.trans (Nat.mul_le_mul_right _ hs), (p i).Unk, inferInstance, J, m, _, Sum.inl, rfl, hJ⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Arithmetic verification with a public random seed

The seed distribution is input independent. Each outcome selects a
finite collection of accepting paths with a uniform bound on their
lengths. Accuracy is pointwise, allowing error on either answer.
Entropy uses natural logarithms in both the budget and its rate.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Filter
variable (F : Type*) [Field F]

def SupportPossible (ρ v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (ι : Type) (_ : Fintype ι) (w : ι → ℝ) (A : ι → Verifier F n),
      (Fintype.card ι : ℝ) ≤ (n : ℝ) ^ (ρ + ε) ∧ (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧
      (∀ i, (A i).cost ((n : ℝ) ^ (v + ε))) ∧ Accurate w (fun i => (A i).accept) Correct

def EntropyPossible (η v : ℝ) : Prop :=
  ∀ ε > (0 : ℝ), ∀ᶠ n : ℕ in atTop,
    ∃ (ι : Type) (_ : Countable ι) (w : ι → ℝ) (A : ι → Verifier F n),
      (∃ E, HasSum (fun i => -w i * Real.log (w i)) E ∧ E ≤ (η + ε) * Real.log n) ∧
      (∀ i, 0 ≤ w i) ∧ HasSum w 1 ∧ (∀ i, (A i).cost ((n : ℝ) ^ (v + ε))) ∧
      Accurate w (fun i => (A i).accept) Correct

def supportExponent (ρ : ℝ) := sInf {v : ℝ | SupportPossible F ρ v}
def entropyExponent (η : ℝ) := sInf {v : ℝ | EntropyPossible F η v}

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # Cost of detecting single-entry errors in a proposed product -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open Filter Finset
open scoped Classical
variable {ι X J : Type*} {w : ι → ℝ} {accept : ι → X → Prop} {good : X → Prop}
  (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (ha : Accurate w accept good)

include hw hs ha in
/-- Every error must be detected on at least one third of the seed
mass. Count errors first on a finite subset, then take its mass to one. -/
private theorem detect [Fintype J] (x : X) (y : J → X) (hx : good x) (hy : ∀ j, ¬good (y j))
    (C : ℝ) (hc : ∀ i, accept i x → ((univ.filter (fun j => ¬accept i (y j))).card : ℝ) ≤ C) :
    (Fintype.card J : ℝ) ≤ 3 * C := by
  have hC : 0 ≤ C := by
    by_contra! h
    have hn (i) : ¬accept i x := fun hi =>
      h.not_ge ((Nat.cast_nonneg _).trans (hc i hi))
    have := ha x
    simp only [hx, iff_true, hn, ite_false, tsum_zero] at this
    norm_num at this
  let δ i j := (if accept i x then w i else 0) - (if accept i (y j) then w i else 0)
  have ht (i : ι) : ∑ j, δ i j ≤ C * w i := by
    by_cases hi : accept i x
    · have he (j) : δ i j = if ¬accept i (y j) then w i else 0 := by
        by_cases h : accept i (y j) <;> simp [δ, hi, h]
      simp_rw [he]
      rw [← sum_filter, sum_const, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hc i hi) (hw i)
    · apply le_trans _ (mul_nonneg hC (hw i))
      apply sum_nonpos
      intro j _
      by_cases h : accept i (y j) <;> simp [δ, hi, h, hw]
  have bound (S : Finset ι) : (Fintype.card J : ℝ) * ((∑ i ∈ S, w i) - 2 / 3) ≤ C := by
    calc
      _ = ∑ _j : J, ((∑ i ∈ S, w i) - 2 / 3) := by simp only [sum_const, card_univ, nsmul_eq_mul]
      _ ≤ ∑ j, ∑ i ∈ S, δ i j := by
        apply sum_le_sum
        intro j _
        simpa only [δ, sum_sub_distrib] using retained_gap hw hs ha S hx (hy j)
      _ = ∑ i ∈ S, ∑ j, δ i j := sum_comm
      _ ≤ ∑ i ∈ S, C * w i := sum_le_sum (fun i _ => ht i)
      _ ≤ C := by
        rw [← mul_sum]
        exact mul_le_of_le_one_right hC (sum_le_hasSum S (fun i _ => hw i) hs)
  have htend : Tendsto (fun S : Finset ι => ∑ i ∈ S, w i) atTop (nhds 1) := hs
  have := le_of_tendsto ((htend.sub_const (2 / 3)).const_mul (Fintype.card J : ℝ))
    (Eventually.of_forall bound)
  linarith

variable {F : Type*} [Field F] {n : ℕ}

private def wrong (p : Rectangle.Pos n n) (i : Index n) : F :=
  if i = (2, p) then 1 else 0

private theorem wrong_not_correct (p : Rectangle.Pos n n) : ¬ Correct (wrong (F := F) p) := by
  intro h
  have := h p.1 p.2
  simp [wrong, Prod.ext_iff] at this

include hw hs in
/-- This bound uses no restriction on support size or entropy. -/
theorem read_bound (A : ι → Verifier F n) {c : ℝ} (hc : ∀ i, (A i).cost c)
    (ha : Accurate w (fun i => (A i).accept) Correct) : (n : ℝ) ^ 2 ≤ 9 * c := by
  let z : Index n → F := fun _ => 0
  have hz : Correct z := by simp [Correct, z]
  have h : (Fintype.card (Rectangle.Pos n n) : ℝ) ≤ 3 * (3 * c) := by
    apply detect hw hs ha z wrong hz wrong_not_correct (3 * c)
    intro i hi
    obtain ⟨W, hW, hread⟩ := (A i).read (hc i) hi
    apply le_trans _ hW
    apply Nat.cast_le.mpr
    apply card_le_card_of_injOn (fun p => (2, p))
    · intro p hp
      by_contra hn
      apply (mem_filter.mp hp).2
      apply hread
      intro j hj
      have : j ≠ (2, p) := by rintro rfl; exact hn hj
      simp [wrong, z, this]
    · exact fun _ _ _ _ he => congrArg Prod.snd he
  simp only [Rectangle.Pos, Fintype.card_prod, Fintype.card_fin, Nat.cast_mul] at h
  linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Simulating an arithmetic tree by existential paths

Each path keeps the constraints accumulated on its branch.
A fresh register is uniquely determined by its instruction.
A failed division costs a single equality test.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open scoped Classical
variable {F : Type*} {n t : ℕ}

private def Instruction.raise : Instruction F n t → Instruction F n (t + 1)
  | .eq a b => .eq a.raise b.raise
  | .ne a b => .ne a.raise b.raise
  | .op f a b c => .op f a.raise b.raise c.raise
  | .div a b c => .div a.raise b.raise c.raise

namespace Tree

variable [Field F]
private abbrev Code (F : Type*) (n t : ℕ) := List (Instruction F n t)

private def paths {t : ℕ} : Tree F n t → Code F n t → Verifier F n
  | .yes, p => [⟨t, p⟩]
  | .no, _ => []
  | .test a b u v, p => paths u (.eq a b :: p) ++ paths v (.ne a b :: p)
  | .op f a b u, p => paths u (.op f a.raise b.raise (.aux (Fin.last t)) :: p.map Instruction.raise)
  | .divide a b u v, p => paths v (.eq b (.scalar 0) :: p) ++
      paths u (.div a.raise b.raise (.aux (Fin.last t)) :: p.map Instruction.raise)

private theorem paths_length (u : Tree F n t) (p : Code F n t) (q : Path F n)
    (h : q ∈ paths u p) : q.code.length ≤ p.length + u.depth := by
  induction u with
  | yes =>
    simp only [paths, List.mem_singleton] at h
    subst q
    simp [depth]
  | no => simp [paths] at h
  | test _ _ _ _ hu hv =>
    rcases List.mem_append.mp h with hl|hr
    · have := hu _ hl
      simp only [depth, List.length_cons] at *
      omega
    · have := hv _ hr
      simp only [depth, List.length_cons] at *
      omega
  | op _ _ _ _ hu =>
    have := hu _ h
    simp only [depth, List.length_cons, List.length_map] at *
    omega
  | divide _ _ _ _ hu hv =>
    rcases List.mem_append.mp h with hl|hr
    · have := hv _ hl
      simp only [depth, List.length_cons] at *
      omega
    · have := hu _ hr
      simp only [depth, List.length_cons, List.length_map] at *
      omega

private def valid (p : Code F n t) (x : Index n → F) (w : Fin t → F) :=
  ∀ i ∈ p, i.holds x w

private theorem valid_cons (p : Code F n t) (i : Instruction F n t) (x w) :
    valid (i::p) x w ↔ i.holds x w ∧ valid p x w := by
  simp [valid]

private theorem valid_raise (p : Code F n t) (x w) :
    valid (p.map Instruction.raise) x w ↔ valid p x (Fin.init w) := by
  have h (i : Instruction F n t) : i.raise.holds x w ↔ i.holds x (Fin.init w) := by
    cases i <;> simp [Instruction.raise, Instruction.holds]
  simp only [valid, List.forall_mem_map, h]

private theorem append (A B : Verifier F n) (x) :
    (A++B).accept x ↔ A.accept x ∨ B.accept x := by
  simp only [Verifier.accept, List.mem_append, or_and_right, exists_or]

omit [Field F] in
private theorem exists_snoc (P : (Fin (t + 1) → F) → Prop) :
    (∃ w, P w) ↔ ∃ w : Fin t → F, ∃ y, P (Fin.snoc w y) := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨Fin.init w, w (Fin.last t), by rwa [Fin.snoc_init_self]⟩
  · rintro ⟨w, y, hy⟩
    exact ⟨_, hy⟩

private theorem branch {α : Type*} (P C U V : α → Prop) :
    (∃ w, (P w ∧ C w) ∧ U w) ∨ (∃ w, (¬P w ∧ C w) ∧ V w) ↔
      ∃ w, C w ∧ (if P w then U w else V w) := by
  rw [← exists_or]
  apply exists_congr
  intro w
  by_cases h : P w <;> simp [h]

private theorem paths_accept (u : Tree F n t) (p : Code F n t) (x : Index n → F) :
    (paths u p).accept x ↔ ∃ w, valid p x w ∧ u.run x w := by
  induction u with
  | yes => simp [paths, Verifier.accept, Path.accept, valid, run]
  | no => simp [paths, Verifier.accept, run]
  | test a b u v hu hv =>
    simp only [paths, append, hu, hv, valid_cons, Instruction.holds, run]
    exact branch _ _ _ _
  | op f a b u hu =>
    rw [paths, hu, exists_snoc]
    simp only [valid_cons, valid_raise, Instruction.holds, Operand.eval_raise, Operand.eval.eq_3,
      Fin.init_snoc, Fin.snoc_last, and_assoc, exists_eq_left', run]
  | divide a b u v hu hv =>
    rw [paths, append, hu, hv, exists_snoc]
    simp only [valid_cons, valid_raise, Instruction.holds, Operand.eval_raise, Operand.eval.eq_1, Operand.eval.eq_3,
      Fin.init_snoc, Fin.snoc_last, and_assoc, exists_and_left, exists_eq_left', run]
    simpa only [and_assoc] using branch (fun w => b.eval x w = 0) (valid p x)
      (v.run x) (fun w => u.run x (Fin.snoc w (a.eval x w / b.eval x w)))

/-- Every finite tree has an existential path verifier of at most its depth. -/
theorem simulate (u : Tree F n t) : ∃ A : Verifier F n, A.cost u.depth ∧ A.accept = u.accept := by
  refine ⟨paths u [], ?_, funext fun x => propext ?_⟩
  · intro q h
    have hh := paths_length u [] q h
    simp only [List.length_nil, zero_add] at hh
    exact_mod_cast hh
  · simp [paths_accept, accept, valid]

end Tree
end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Simulating division-free tests by witness-free decision trees

After a prefix of arithmetic operations, each available polynomial
can be read from a scalar, input, or register. Prepending this prefix
to any subsequent tree fixes all its initial registers and adds one
level per operation.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open scoped Classical
variable {F : Type*} [Field F] {n m : ℕ} {T : Set (Poly F n)}

private def Implements (m : ℕ) (T : Set (Poly F n)) : Prop :=
  ∃ w : (Index n → F) → Fin m → F,
    (∀ a ∈ T, ∃ b : Operand F n m, ∀ x, b.eval x (w x) = MvPolynomial.eval x a) ∧
    ∀ next : Tree F n m, ∃ v : Tree F n 0,
      v.depth = m + next.depth ∧ ∀ x, v.accept x ↔ next.run x (w x)

private theorem Implements.step (h : Implements m T) (f : Op)
    {a b : Poly F n} (ha : a ∈ T) (hb : b ∈ T) : Implements (m + 1) (insert (f.eval a b) T) := by
  obtain ⟨w, read, attach⟩ := h
  obtain ⟨u, hu⟩ := read _ ha
  obtain ⟨v, hv⟩ := read _ hb
  let val x := f.eval (u.eval x (w x)) (v.eval x (w x))
  let reg (x : Index n → F) : Fin (m + 1) → F := Fin.snoc (w x) (val x)
  refine ⟨reg, ?_, ?_⟩
  · rintro q (rfl | hq)
    · refine ⟨.aux (Fin.last m), fun x => ?_⟩
      change reg x (Fin.last m) = _
      simp only [reg, Fin.snoc_last, val, hu, hv]
      cases f <;> simp [Op.eval]
    · obtain ⟨s, hs⟩ := read _ hq
      exact ⟨s.raise, fun x => by simp [reg, hs]⟩
  · intro next
    obtain ⟨t, ht, he⟩ := attach (.op f u v next)
    exact ⟨t, by rw [ht, Tree.depth]; omega, he⟩

private theorem implements (h : Integral.Build (inputs F n) m T) : Implements m T := by
  induction h with
  | nil =>
    refine ⟨fun _ => Fin.elim0, ?_, ?_⟩
    · rintro _ (⟨a, rfl⟩ | ⟨i, rfl⟩)
      · exact ⟨.scalar a, by simp [Operand.eval]⟩
      · exact ⟨.input i, by simp [Operand.eval]⟩
    · intro next
      refine ⟨next, by simp, fun x => ?_⟩
      exact ⟨fun ⟨w, hw⟩ => Subsingleton.elim w Fin.elim0 ▸ hw, fun h => ⟨_, h⟩⟩
  | add _ ha hb ih => exact ih.step .add ha hb
  | sub _ ha hb ih => exact ih.step .sub ha hb
  | mul _ ha hb ih => exact ih.step .mul ha hb

private theorem tests {j : ℕ} (l r : Fin j → Operand F n m) :
    ∃ v : Tree F n m, v.depth = j ∧ ∀ x w, v.run x w ↔ ∀ i, (l i).eval x w = (r i).eval x w := by
  induction j with
  | zero => exact ⟨.yes, rfl, by simp [Tree.run]⟩
  | succ j ih =>
    obtain ⟨v, hv, he⟩ := ih (l ∘ Fin.succ) (r ∘ Fin.succ)
    refine ⟨.test (l 0) (r 0) v .no, by simp [Tree.depth, hv], fun x w => ?_⟩
    rw [Fin.forall_fin_succ]
    by_cases h : (l 0).eval x w = (r 0).eval x w <;> simp [Tree.run, h, he]

/-- The deterministic tree needs no witness. Its depth counts one step
per arithmetic operation and one per final equality. -/
theorem Test.tree (A : Test F n) {c : ℝ} (hc : A.cost c) :
    ∃ v : Tree F n 0, (v.depth : ℝ) ≤ c ∧ v.accept = A.accept := by
  obtain ⟨m, T, hb, ha, hc⟩ := hc
  obtain ⟨w, read, attach⟩ := implements hb
  choose l left using fun i => read _ (ha i).1
  choose r right using fun i => read _ (ha i).2
  obtain ⟨t, ht, he⟩ := tests l r
  obtain ⟨v, hv, hv'⟩ := attach t
  refine ⟨v, by simpa only [hv, ht, Nat.cast_add] using hc, funext fun x => propext ?_⟩
  simp only [hv', he, left, right, Test.accept]

theorem Test.simulate (A : Test F n) {c : ℝ} (hc : A.cost c) :
    ∃ V : Verifier F n, V.cost c ∧ V.accept = A.accept := by
  obtain ⟨t, ht, e⟩ := A.tree hc
  obtain ⟨v, hv, e'⟩ := t.simulate
  exact ⟨v, fun i hi => (hv i hi).trans ht, e'.trans e⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # Independent output combinations in a matrix product -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

def projection {F : Type*} [Field F] {n : ℕ} (P : Matrix (Pos n n) (Pos n n) F) :
    Coordinates n n n → F :=
  fun (x, y, z) => if x.2 = y.1 then P z (x.1, y.2) else 0

/-- The linear combinations need not be individual output entries.
The closure here uses polynomials and decompositions over F itself. -/
def Projected (F : Type*) [Field F] (n q r : ℕ) : Prop :=
  ∃ P : Matrix (Pos n n) (Pos n n) F, q ≤ P.rank ∧
    ZClosure (rankSet F n n n r) (projection P)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # Selecting independent leading output cells -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset
open scoped Classical

variable {F : Type*} [Field F] {I : Type} [Fintype I]

/-- Restriction to all possible leading indices is injective on the
row space. Use any requested number of them as normalized pivots. -/
theorem pivots (v : I → ℕ) (P : Matrix I I F) {q : ℕ} (hq : q ≤ P.rank) :
    ∃ (S : Finset I) (A : Matrix I I F), S.card = q ∧
      (∀ i, (A * P) i i = if i ∈ S then 1 else 0) ∧
      ∀ i j, v j < v i → (A * P) i j = 0 := by
  let V := Submodule.span F (Set.range P.row)
  let t : Finset I := {i | ∃ w ∈ V, w i ≠ 0 ∧ ∀ j, v j < v i → w j = 0}
  let f : V →ₗ[F] (t → F) :=
    { toFun := fun w i => w.val i, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hinj : Function.Injective f := by
    apply LinearMap.ker_eq_bot.mp
    apply bot_unique
    intro w hw
    have hz : f w = 0 := hw
    change w = 0
    apply Subtype.ext
    funext i
    change w.val i = 0
    by_contra h
    let U : Finset I := {j | w.val j ≠ 0}
    obtain ⟨j, hj, hmin⟩ := U.exists_min_image v ⟨i, by simp [U, h]⟩
    have hj' : w.val j ≠ 0 := (mem_filter.mp hj).2
    have hlead : j ∈ t := by
      refine mem_filter.mpr ⟨mem_univ _, w.val, w.property, hj', fun l hl => ?_⟩
      by_contra hn
      exact hl.not_ge (hmin l (by simp [U, hn]))
    exact hj' (congrFun hz ⟨j, hlead⟩)
  have hdim := LinearMap.finrank_le_finrank_of_injective hinj
  rw [Matrix.rank_eq_finrank_span_row] at hq
  obtain ⟨S, hS, he⟩ := exists_subset_card_eq (show q ≤ t.card by simpa using hq.trans hdim)
  have hl (i : I) : ∃ w ∈ V, (w i = if i ∈ S then 1 else 0) ∧ ∀ j, v j < v i → w j = 0 := by
    by_cases hi : i ∈ S
    · obtain ⟨w, hw, hi', hj⟩ := (mem_filter.mp (hS hi)).2
      exact ⟨(w i)⁻¹ • w, V.smul_mem _ hw, by simp [hi, hi'], fun j h => by simp [hj j h]⟩
    · exact ⟨0, V.zero_mem, by simp [hi], fun _ _ => rfl⟩
  choose w hw hdiag htri using hl
  choose c hc using fun i => (Submodule.mem_span_range_iff_exists_fun _).mp (hw i)
  let A : Matrix I I F := c
  have heq (i j) : (A * P) i j = w i j := by
    rw [Matrix.mul_apply]
    simpa only [A, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.row] using congrFun (hc i) j
  exact ⟨S, A, he, by simpa only [heq] using hdiag, by simpa only [heq] using htri⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # Degenerating an output projection to its leading cells -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset
open scoped Classical

variable {F : Type*} [Field F] {n q r : ℕ}

private def transform (a b : Fin n → F) (P : Matrix (Pos n n) (Pos n n) F)
    (v : Coordinates n n n → F) : Coordinates n n n → F :=
  fun (x, y, z) => a x.1 * b y.2 * ∑ o, P z o * v (x, y, o)

private theorem transform_rank (a b : Fin n → F) (P : Matrix (Pos n n) (Pos n n) F)
    {v : Coordinates n n n → F} (h : v ∈ rankSet F n n n r) :
    transform a b P v ∈ rankSet F n n n r := by
  obtain ⟨A, B, C, h⟩ := h
  refine ⟨fun i x => a x.1 * A i x, fun i y => b y.2 * B i y, fun i z => ∑ o, P z o * C i o, ?_⟩
  intro x y z
  simp only [transform, ← h, mul_sum]
  rw [sum_comm]
  exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => by ring))

open MvPolynomial in
private theorem transform_closure (a b : Fin n → F) (P : Matrix (Pos n n) (Pos n n) F)
    {v : Coordinates n n n → F} (h : ZClosure (rankSet F n n n r) v) :
    ZClosure (rankSet F n n n r) (transform a b P v) := by
  intro p hp
  let f : Coordinates n n n → MvPolynomial (Coordinates n n n) F :=
    fun (x, y, z) => C (a x.1 * b y.2) * ∑ o, C (P z o) * X (x, y, o)
  have he (u : Coordinates n n n → F) : eval u (eval₂ C f p) = eval (transform a b P u) p := by
    rw [hom_eval₂, show (eval u).comp C = RingHom.id F by ext; simp]
    have hh : (fun i => eval u (f i)) = transform a b P u := by
      funext ⟨x, y, z⟩
      simp [transform, f]
    rw [hh]
    rfl
  rw [← he]
  exact h _ fun u hu => (he u).trans (hp _ (transform_rank _ _ _ hu))

private def degree (i : Pos n n) := (finProdFinEquiv i).val

/-- The additive weight of a cell is distinct for each pair of
indices. Negative powers cancel by the leading-index property. -/
theorem Projected.cells [Infinite F] (h : Projected F n q r) :
    ∃ S : Finset (Pos n n), S.card = q ∧
      ZClosure (rankSet F n n n r) (coefficients (mask (ordinary F n n n) S)) := by
  obtain ⟨P, hq, hP⟩ := h
  obtain ⟨S, A, he, hd, ht⟩ := pivots degree P hq
  let path : Coordinates n n n → Polynomial F := fun (x, y, z) =>
    Polynomial.C (projection (A * P) (x, y, z)) * Polynomial.X ^ (degree (x.1, y.2) - degree z)
  have hs (t : F) (hne : t ≠ 0) : ZClosure (rankSet F n n n r) (fun i => (path i).eval t) := by
    let a (i : Fin n) := t ^ (n * i.val)
    let b (j : Fin n) := t ^ j.val
    let L : Matrix (Pos n n) (Pos n n) F := fun z o => (t ^ degree z)⁻¹ * A z o
    convert transform_closure a b L hP using 1
    funext ⟨x, y, z⟩
    simp only [path, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      transform, projection]
    by_cases hh : x.2 = y.1
    · simp only [ite_eq_left hh, L, mul_assoc, ← mul_sum]
      rw [← Matrix.mul_apply]
      by_cases hlt : degree (x.1, y.2) < degree z
      · simp [ht z (x.1, y.2) hlt]
      · rw [pow_sub₀ t hne (le_of_not_gt hlt)]
        change _ * (t ^ (y.2.val + n * x.1.val) * _) = _
        rw [pow_add]
        unfold a b
        ring
    · simp [hh]
  have hzero : (fun i => (path i).eval 0) = coefficients (mask (ordinary F n n n) S) := by
    funext ⟨x, y, z⟩
    simp only [path, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X,
      projection, coefficients, mask, ordinary]
    by_cases hxy : x.2 = y.1
    · by_cases he : (x.1, y.2) = z
      · subst z
        simp [hd, hxy]
      · have he' : degree (x.1, y.2) ≠ degree z := fun h => he (finProdFinEquiv.injective (Fin.ext h))
        have hn : ¬ (x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2) := fun h => he (Prod.ext h.1 h.2.2)
        rw [ite_eq_right hn, ite_eq_left hxy]
        rcases lt_or_gt_of_ne he' with hl | hl
        · rw [ht _ _ hl, zero_mul]
        · rw [zero_pow (by omega), mul_zero]
    · simp [hxy]
  refine ⟨S, he, ?_⟩
  rw [← hzero]
  have hc := Speedup.path_closure (A := {v | ZClosure (rankSet F n n n r) v})
    path Polynomial.X Polynomial.X_ne_zero (fun t h => hs t (by simpa using h))
  exact fun p hp => hc p (fun _ h => h p hp)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # Descending projections by isolating their output cells -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset MvPolynomial
open scoped Classical

variable {F K E : Type*} [Field F] [Field K] [Field E] {n q r : ℕ}

theorem rank_minor {I : Type} [Fintype I] [DecidableEq I] (S : Finset I) (P : Matrix I I F)
    (h : ∀ i ∈ S, ∀ j ∈ S, P i j = if i = j then 1 else 0) : S.card ≤ P.rank := by
  let f : ↥S → I := Subtype.val
  have he : P.submatrix f f = 1 := by
    ext i j
    simp [Matrix.submatrix_apply, h _ i.property _ j.property, f, Matrix.one_apply]
  simpa only [he, Matrix.rank_one, Fintype.card_coe] using P.rank_submatrix_le f f

/-- A leading-cell tensor descends to the ground field because its
coefficients are zeros and ones. No descent of the original
projection matrix is required. -/
theorem Projected.descend [Infinite F] (f : F →+* K) (h : Projected K n q r) : Projected F n q r := by
  have : Infinite K := Infinite.of_injective f f.injective
  obtain ⟨S, he, hS⟩ := h.cells
  let P : Matrix (Pos n n) (Pos n n) F := fun i j => if i = j ∧ j ∈ S then 1 else 0
  have hr : S.card ≤ P.rank := rank_minor S P (fun _ _ _ hj => by simp [P, hj])
  refine ⟨P, he ▸ hr, ?_⟩
  have hc : f ∘ projection P = coefficients (mask (ordinary K n n n) S) := by
    funext ⟨x, y, z⟩
    simp only [Function.comp_apply, projection, P, apply_ite f, map_one, map_zero, coefficients, mask, ordinary,
      ← ite_and, Prod.ext_iff]
    congr 1
    exact propext (by grind)
  intro p hp
  apply f.injective
  rw [map_zero, eval₂_comp, hc, ← eval_map]
  exact hS _ (fun z hz => by rw [eval_map]; exact Border.identity_of_rank hp f hz)

/-- Specialize entries integral at a place, allowing arbitrary poles
in the rank decomposition itself. -/
theorem specialize_rank [Infinite K] [Algebra K E] (A : Subalgebra K E) (ρ : A →ₐ[K] K)
    (T : Coordinates n n n → A) (h : (fun z => (T z : E)) ∈ rankSet E n n n r) :
    ZClosure (rankSet K n n n r) (ρ ∘ T) := by
  intro p hp
  have he := Border.identity_of_rank hp (algebraMap K E) h
  have hA : eval₂ (algebraMap K A) T p = 0 := by
    apply Subtype.val_injective
    change A.val.toRingHom _ = A.val.toRingHom 0
    rw [map_zero, hom_eval₂]
    exact he
  have hh := congrArg ρ.toRingHom hA
  rw [hom_eval₂, show ρ.toRingHom.comp (algebraMap K A) = RingHom.id K by ext; simp, map_zero] at hh
  exact hh

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Specializing a projected quadratic term

Some terms separate only in the output index. Eliminate their
output vectors over the valuation ring before specializing. The
remaining projection has an identity minor and bounded border rank.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset

variable {F K E : Type*} [Field F] [Infinite F] [Field K] [Algebra F K] [Field E] [Algebra K E]

theorem specialize_projection (A : Subalgebra K E) (hA : ∀ x : E, x ∈ A ∨ x⁻¹ ∈ A)
    (ρ : A →ₐ[K] K) {n r d : ℕ} (T : Pos n n → Pos n n → Pos n n → A)
    (hT : ∀ x y z, ρ (T x y z) = coefficients (ordinary K n n n) (x, y, z))
    (a b c : Fin r → Pos n n → E) (v : Fin d → Pos n n → Pos n n → E) (w : Fin d → Pos n n → E)
    (he : ∀ x y z, (T x y z : E) = (∑ i, a i x * b i y * c i z) + ∑ i, v i x y * w i z) :
    Projected F n (n * n - d) r := by
  classical
  have : Infinite K := Infinite.of_injective (algebraMap F K) (algebraMap F K).injective
  obtain ⟨S, P, hs, hP, hkill⟩ := eliminate A hA w
  let g := A.val.toRingHom
  let Q : Matrix (Pos n n) (Pos n n) K := fun i j => ρ (P i j)
  let v' : Coordinates n n n → A := fun (x, y, z) => ∑ o, P z o * T x y o
  have hq : S.card ≤ Q.rank := rank_minor S Q (fun i hi j hj => by simp [Q, hP i hi j hj])
  have hh : (fun z => (v' z : E)) ∈ rankSet E n n n r := by
    refine ⟨a, b, fun i z => ∑ o, (P z o : E) * c i o, fun x y z => ?_⟩
    have hz : (∑ o, (P z o : E) * (∑ i, v i x y * w i o)) = 0 := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_eq_zero
      intro i _
      simp_rw [mul_left_comm _ (v i x y), ← mul_sum, hkill, mul_zero]
    change _ = g (∑ o, P z o * T x y o)
    rw [map_sum]
    simp_rw [map_mul]
    change _ = ∑ o, (P z o : E) * (T x y o : E)
    simp only [he, mul_add, sum_add_distrib, hz, add_zero]
    simp only [mul_sum]
    rw [sum_comm]
    exact sum_congr rfl (fun _ _ => sum_congr rfl (fun _ _ => by ring))
  have heq : ρ ∘ v' = projection Q := by
    funext ⟨x, y, z⟩
    simp only [v', projection, Function.comp_apply, map_sum, map_mul, hT, coefficients, ordinary]
    by_cases hxy : x.2 = y.1
    · have hj (o : Pos n n) : (x.1 = o.1 ∧ x.2 = y.1 ∧ y.2 = o.2) ↔ (x.1, y.2) = o := by
        simp [Prod.ext_iff, hxy]
      simp_rw [hj]
      simp [hxy, Q, mul_ite]
    · simp [hxy]
  have hl := specialize_rank A ρ v' hh
  rw [heq] at hl
  apply Projected.descend (algebraMap F K)
  exact ⟨Q, by simpa [Pos] using hs.trans hq, hl⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # Inverting a Jacobian preserves the count of mixed products -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset Matrix
open scoped Matrix

variable {F K E : Type*} [Field F] [Infinite F] [Field K] [Algebra F K] [Field E] [Algebra K E]

/-- Each quadratic term has two separated mixed derivatives.
Auxiliary measurements separate only in the output index. -/
theorem linearized_projection (A : Subalgebra K E) (hA : ∀ x : E, x ∈ A ∨ x⁻¹ ∈ A)
    (ρ : A →ₐ[K] K) {σ : Type} [Fintype σ] [DecidableEq σ] {n q d : ℕ}
    (pos : Pos n n → σ) (T : Pos n n → Pos n n → σ → A)
    (hT : ∀ x y z, ρ (T x y (pos z)) = coefficients (ordinary K n n n) (x, y, z))
    (J : Matrix σ σ E) (hJ : IsUnit J) (l₁ l₂ r₁ r₂ : Fin q → Pos n n → E)
    (c : Matrix σ (Fin q) E) (f : Matrix σ (Fin d) E) (m : Fin d → Pos n n → Pos n n → E)
    (he : ∀ x y i, (∑ t, J i t * (T x y t : E)) +
      (∑ j, c i j * (l₁ j x * r₂ j y + r₁ j x * l₂ j y)) = ∑ j, f i j * m j x y) :
    Projected F n (n * n - d) (2 * q) := by
  let B : Matrix σ σ E := ↑(hJ.unit⁻¹)
  have hi : B * J = 1 := by simpa [B] using hJ.unit.inv_mul
  let g (j : Fin q) (z : Pos n n) := -(B * c) (pos z) j
  rw [two_mul]
  apply specialize_projection A hA ρ (fun x y z => T x y (pos z)) hT
    (Fin.append l₁ r₁) (Fin.append r₂ l₂) (Fin.append g g) m (fun i z => (B * f) (pos z) i)
  intro x y z
  let X i := (T x y i : E)
  let Y j := l₁ j x * r₂ j y + r₁ j x * l₂ j y
  let Z j := m j x y
  have h : J *ᵥ X + c *ᵥ Y = f *ᵥ Z := funext (he x y)
  have hh := congrArg B.mulVec h
  rw [mulVec_add, mulVec_mulVec, mulVec_mulVec, mulVec_mulVec, hi, one_mulVec] at hh
  have hz := congrFun hh (pos z)
  change (T x y (pos z) : E) + ∑ j, (B * c) (pos z) j * Y j = ∑ j, (B * f) (pos z) j * m j x y at hz
  rw [eq_sub_of_add_eq hz, Fin.sum_univ_add]
  simp only [Fin.append_left, Fin.append_right, g, Y, mul_add, sum_add_distrib, mul_neg, sum_neg_distrib]
  simp only [mul_comm]
  abel

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Differentiating the deformed verification equations

A left and a right coordinate derivation lift to the generic point
of the curve, fixing the parameter. Their action commutes with
specialization at the chosen branch. Therefore the mixed derivative
of the output specializes to the matrix multiplication tensor.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial
variable {F L E : Type u} [Field F] [Field L] [Algebra F L] {n : ℕ}

private theorem mixed_beta (X : PairIndex n → L) (x y z : Pos n n)
    (D D' : Derivation F L L)
    (h : ∀ i, D (X i) = if i = (0, x) then 1 else 0)
    (h' : ∀ i, D' (X i) = if i = (1, y) then 1 else 0) :
    D' (D (beta X z)) = coefficients (ordinary L n n n) (x, y, z) := by
  obtain ⟨a, b⟩ := x
  obtain ⟨c, d⟩ := y
  by_cases hz : z.1 = a
  · have first : D (beta X z) = X (1, b, z.2) := by
      simp [beta, map_sum, D.leibniz, smul_eq_mul, h, hz]
    rw [first, h']
    simp [coefficients, ordinary, hz, eq_comm]
  · have first : D (beta X z) = 0 := by
      simp [beta, map_sum, D.leibniz, smul_eq_mul, h, hz]
    simp [first, coefficients, Ne.symm hz]

variable [Infinite F] [CharZero L] [Field E] [Algebra L E] [Algebra F E] [IsScalarTower F L E]
    {σ : Type} [Fintype σ] [DecidableEq σ] {q d : ℕ}

theorem Jet.project (J : Jet F (PairIndex n) σ q d) (X : PairIndex n → L)
    (m : Fin d → L) {t : E} (b : Branch L E t) (Y : σ → b.ring) (pos : Pos n n → σ) (c : σ → L)
    (ht : Transcendental L t)
    (hy : ∀ j, b.res (Y (pos j)) = beta X j)
    (heq : ∀ i, aeval (fun j => (Y j : E)) (J.system X m i) = t * algebraMap L E (c i))
    (hinv : IsUnit (jacobian (J.system X m) (fun j => (Y j : E))))
    (hd : ∀ j : PairIndex n, ∃ D : Derivation F L L,
      (∀ i, D (X i) = if i = j then 1 else 0) ∧ ∀ i, D (c i) = 0) :
    Projected F n (n * n - d) (2 * q) := by
  classical
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap L E).injective
  choose D hX hc using hd
  choose H ext fixed using fun i => exists_derivation_extension ht (D i)
  let lift i := b.lift (H i) (D i) (ext i) (fixed i)
  let T (x y : Pos n n) (s : σ) := lift (1, y) (lift (0, x) (Y s))
  have sample (x y z : Pos n n) : b.res (T x y (pos z)) = coefficients (ordinary L n n n) (x, y, z) := by
    unfold T lift
    rw [b.specialize, b.specialize, hy]
    exact mixed_beta X x y z _ _ (hX (0, x)) (hX (1, y))
  let a (j : σ) : E := Y j
  let left (i : Fin 2) (j : Fin q) (x : Pos n n) := H (i, x) (aeval a ((J.left j).specialize X))
  let right (i : Fin 2) (j : Fin q) (x : Pos n n) := H (i, x) (aeval a ((J.right j).specialize X))
  refine linearized_projection b.ring b.val b.res pos T sample _ hinv
    (left 0) (left 1) (right 0) (right 1)
    (fun i j => algebraMap F E (J.c i j)) (fun i j => algebraMap F E (J.f i j))
    (fun j x y => H (1, y) (H (0, x) (algebraMap L E (m j)))) ?_
  intro x y i
  apply J.mixed X m a (H (0, x)) (H (1, y)) i
  · rw [heq, Derivation.leibniz, fixed, ext, hc, map_zero, smul_zero, smul_zero, add_zero, map_zero]
  · intro j
    rw [ext, hX]
    split_ifs <;> simp

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Independent projected outputs from equality-test verification

An isolated system at a generic input comes from just one accepting
path. A second family of independent constants gives the direction
of a simple deformation. Input derivations fix these new constants.
The mixed derivatives recover matrix multiplication upon specialization.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial
variable {F K : Type u} [Field F] [CharZero F] [Field K] [Algebra F K] [CharZero K] {n : ℕ}

theorem Jet.project_isolated {σ : Type} [Fintype σ] {q d : ℕ}
    (J : Jet F (PairIndex n) σ q d) (X : PairIndex n → K) (hx : AlgebraicIndependent F X)
    (m : Fin d → K) (y : σ → K) (pos : Pos n n → σ)
    (hy : y ∘ pos = beta X) (isolated : Isolated y (Ideal.span (Set.range (J.system X m)))) :
    Projected F n (n * n - d) (2 * q) := by
  classical
  have : Infinite F := Infinite.of_injective (fun n : ℕ => (n : F)) Nat.cast_injective
  let L := Free K σ
  let c := Free.point K σ
  let Y := algebraMap K L ∘ X
  let m' := algebraMap K L ∘ m
  have eq : MvPolynomial.map (algebraMap K L) ∘ J.system X m = J.system Y m' :=
    funext (J.map_system X m)
  have h := simple_lift (J.system X m) y isolated c (Free.independent K σ)
  dsimp only at h
  rw [eq] at h
  obtain ⟨E, field, alg, t, b, z, ht, hz, heq, hinv⟩ := h
  let _ : Algebra F E := ((algebraMap L E).comp (algebraMap F L)).toAlgebra
  have : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq' rfl
  refine J.project Y m' b z pos c ht ?_ heq hinv ?_
  · intro i
    have hi : y (pos i) = beta X i := congrFun hy i
    rw [hz, hi]
    simp only [beta, Y, L, Function.comp_apply, map_sum, map_mul]
  · intro j
    obtain ⟨D, hD⟩ := derivation_of_independent hx (fun i => if i = j then (1 : K) else 0)
    obtain ⟨d, hd, hc⟩ := Free.derivation σ D
    refine ⟨d, fun i => ?_, hc⟩
    change d (algebraMap K L (X i)) = _
    rw [hd, hD]
    split <;> simp

/-- A strict gap on a finite set of seeds suffices. The rank bound
uses the maximum length of one path, independently of the seed count. -/
theorem gap_projection [IsAlgClosed F] (hn : 0 < n) {ι : Type*}
    {w : ι → ℝ} {S : Finset ι} {A : ι → Verifier F n} {c : ℝ}
    (hw : ∀ i ∈ S, 0 ≤ w i) (hc : ∀ i ∈ S, (A i).cost c)
    (gap : Gap w (fun i => (A i).accept) Correct S) :
    ∃ q r : ℕ, (r : ℝ) ≤ 4 * c ∧ n * n ≤ S.card * q ∧ Projected F n q r := by
  let X := Free.point F (PairIndex n)
  have hx := Free.independent F (PairIndex n)
  obtain ⟨q, d, hs, _, hd, σ, finite, J, m, y, pos, hy, hi⟩ := isolated_jet hn hw hc gap hx
  refine ⟨n * n - d, 2 * q, ?_, hd, J.project_isolated X hx m y pos hy hi⟩
  push_cast
  linarith

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end
