import Mathlib.Analysis.SpecialFunctions.Pow.Real
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Model
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Restricting a public seed to finitely many outcomes

A retained set of mass greater than two thirds still strictly
separates every correct input from every incorrect one. The weights
need not be normalized again.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open Finset
open scoped Classical
variable {ι X : Type*}

def Accurate (w : ι → ℝ) (accept : ι → X → Prop) (good : X → Prop) : Prop :=
  ∀ x, 2 / 3 ≤ ∑' i, if (accept i x ↔ good x) then w i else 0

def Gap (w : ι → ℝ) (accept : ι → X → Prop) (good : X → Prop) (S : Finset ι) : Prop :=
  ∀ x y, good x → ¬good y →
    (∑ i ∈ S, if accept i y then w i else 0) < ∑ i ∈ S, if accept i x then w i else 0

variable {w : ι → ℝ} {accept : ι → X → Prop} {good : X → Prop}
  (hw : ∀ i, 0 ≤ w i) (hs : HasSum w 1) (ha : Accurate w accept good)

include hw hs ha in
private theorem mistake (S : Finset ι) (x : X) :
    (∑ i ∈ S, if (accept i x ↔ good x) then 0 else w i) ≤ 1 / 3 := by
  let f i := if (accept i x ↔ good x) then w i else 0
  have hf : Summable f := Summable.of_nonneg_of_le
    (fun i => by unfold f; split <;> simp [hw])
    (fun i => by unfold f; split <;> simp [hw]) hs.summable
  have he (i) : w i - f i = if (accept i x ↔ good x) then 0 else w i := by
    unfold f; split <;> simp_all
  have ht := hs.sub hf.hasSum
  simp_rw [he] at ht
  refine (sum_le_hasSum S (fun i _ => by split <;> simp [hw]) ht).trans ?_
  have hh : 2 / 3 ≤ ∑' i, f i := ha x
  linarith

include hw hs ha in
theorem retained_gap (S : Finset ι) {x y : X} (hx : good x) (hy : ¬good y) :
    (∑ i ∈ S, w i) - 2 / 3 ≤
      (∑ i ∈ S, if accept i x then w i else 0) - (∑ i ∈ S, if accept i y then w i else 0) := by
  have h := mistake hw hs ha S x
  have k := mistake hw hs ha S y
  simp only [hx, iff_true] at h
  simp only [hy, iff_false, ite_not] at k
  have he : (∑ i ∈ S, if accept i x then w i else 0) +
      (∑ i ∈ S, if accept i x then 0 else w i) = ∑ i ∈ S, w i := by
    rw [← sum_add_distrib]
    exact sum_congr rfl (fun i _ => by split <;> simp_all)
  linarith

include hw hs ha in
theorem mass_gap (S : Finset ι) (hm : 2 / 3 < ∑ i ∈ S, w i) : Gap w accept good S :=
  fun _ _ hx hy => sub_pos.mp ((sub_pos.mpr hm).trans_le (retained_gap hw hs ha S hx hy))

include hw hs ha in
theorem finite_gap [Fintype ι] : Gap w accept good univ := by
  apply mass_gap hw hs ha
  have hm := hs.tsum_eq
  rw [tsum_fintype] at hm
  rw [hm]
  norm_num

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Acceptance by a finite family of paths

A path is a conjunction on scalar coordinates. Both intermediate
registers and post-seed witnesses are existentially quantified.
A verifier is their finite disjunction. Its cost bounds the longest
path, even if a different path accepts each input.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

inductive Operand (F : Type*) (n t : ℕ)
  | scalar (a : F)
  | input (i : Index n)
  | aux (j : Fin t)

inductive Op
  | add | sub | mul

inductive Instruction (F : Type*) (n t : ℕ)
  | eq (a b : Operand F n t)
  | ne (a b : Operand F n t)
  | op (f : Op) (a b c : Operand F n t)
  | div (a b c : Operand F n t)

structure Path (F : Type*) (n : ℕ) where
  vars : ℕ
  code : List (Instruction F n vars)

abbrev Verifier (F : Type*) (n : ℕ) := List (Path F n)

variable {F : Type*} {n t : ℕ}

def Operand.eval (x : Index n → F) (w : Fin t → F) : Operand F n t → F
  | .scalar a => a
  | .input i => x i
  | .aux j => w j

def Op.eval [Ring F] (f : Op) (a b : F) : F :=
  match f with
  | .add => a + b
  | .sub => a - b
  | .mul => a * b

variable [Field F]

def Instruction.holds (x : Index n → F) (w : Fin t → F) : Instruction F n t → Prop
  | .eq a b => a.eval x w = b.eval x w
  | .ne a b => a.eval x w ≠ b.eval x w
  | .op f a b c => f.eval (a.eval x w) (b.eval x w) = c.eval x w
  | .div a b c => b.eval x w ≠ 0 ∧ a.eval x w / b.eval x w = c.eval x w

def Path.accept (p : Path F n) (x : Index n → F) : Prop :=
  ∃ w, ∀ i ∈ p.code, i.holds x w

def Verifier.accept (A : Verifier F n) (x : Index n → F) : Prop :=
  ∃ p ∈ A, p.accept x

def Verifier.cost (A : Verifier F n) (c : ℝ) : Prop :=
  ∀ p ∈ A, (p.code.length : ℝ) ≤ c

private def Operand.names : Operand F n t → Finset (Index n)
  | .input i => {i}
  | _ => ∅

omit [Field F] in
private theorem Operand.read (a : Operand F n t) :
    a.names.card ≤ 1 ∧ ∀ x y w, (∀ i ∈ a.names, x i = y i) → a.eval x w = a.eval y w := by
  cases a <;> simp [names, eval]

private theorem Instruction.read (a : Instruction F n t) :
    ∃ W : Finset (Index n), W.card ≤ 3 ∧
      ∀ x y w, (∀ i ∈ W, x i = y i) → a.holds x w → a.holds y w := by
  have pick (a b c : Operand F n t) :
      ∃ W : Finset (Index n), W.card ≤ 3 ∧ ∀ x y w, (∀ i ∈ W, x i = y i) →
        a.eval x w = a.eval y w ∧ b.eval x w = b.eval y w ∧ c.eval x w = c.eval y w := by
    refine ⟨a.names ∪ b.names ∪ c.names, ?_, fun x y w h => ?_⟩
    · exact (Finset.card_union_le ..).trans (Nat.add_le_add
        ((Finset.card_union_le ..).trans (Nat.add_le_add a.read.1 b.read.1)) c.read.1)
    · exact ⟨a.read.2 _ _ _ (fun i hi => h i (by simp [hi])),
        b.read.2 _ _ _ (fun i hi => h i (by simp [hi])),
        c.read.2 _ _ _ (fun i hi => h i (by simp [hi]))⟩
  cases a with
  | eq a b | ne a b =>
    obtain ⟨W, hW, h⟩ := pick a b b
    refine ⟨W, hW, fun x y w he => ?_⟩
    simp only [holds, (h x y w he).1, (h x y w he).2.1, imp_self]
  | op _ a b c | div a b c =>
    obtain ⟨W, hW, h⟩ := pick a b c
    refine ⟨W, hW, fun x y w he => ?_⟩
    simp only [holds, (h x y w he).1, (h x y w he).2.1, (h x y w he).2.2, imp_self]

private theorem read_code (p : List (Instruction F n t)) :
    ∃ W : Finset (Index n), W.card ≤ 3 * p.length ∧ ∀ x y w, (∀ i ∈ W, x i = y i) →
      ∀ i ∈ p, i.holds x w → i.holds y w := by
  induction p with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons a p ih =>
    obtain ⟨A, hA, ha⟩ := a.read
    obtain ⟨B, hB, hb⟩ := ih
    refine ⟨A ∪ B, (Finset.card_union_le ..).trans (by simp only [List.length_cons]; omega), ?_⟩
    intro x y w h i hi
    rcases List.mem_cons.mp hi with rfl|hi
    · exact ha _ _ _ (fun j hj => h j (Finset.mem_union_left _ hj))
    · exact hb _ _ _ (fun j hj => h j (Finset.mem_union_right _ hj)) _ hi

/-- One accepting assignment continues to work on any change outside
the coordinates read by its path. -/
theorem Verifier.read (A : Verifier F n) {c : ℝ} (hc : A.cost c) {x} (hx : A.accept x) :
    ∃ W : Finset (Index n), (W.card : ℝ) ≤ 3 * c ∧ ∀ y, (∀ i ∈ W, x i = y i) → A.accept y := by
  obtain ⟨p, hp, w, hw⟩ := hx
  obtain ⟨W, hW, h⟩ := read_code p.code
  refine ⟨W, ?_, fun y he => ⟨p, hp, w, fun i hi => h x y w he i hi (hw i hi)⟩⟩
  exact (show (W.card : ℝ) ≤ 3 * p.code.length by exact_mod_cast hW).trans
    (mul_le_mul_of_nonneg_left (hc p hp) (by norm_num))

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Finite arithmetic trees with equality branches

The initial auxiliary coordinates are existential witnesses. Each
arithmetic operation appends a register. Division branches on a
zero denominator and appends a register only on success.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification

open scoped Classical

inductive Tree (F : Type*) (n : ℕ) : ℕ → Type _
  | yes {t} : Tree F n t
  | no {t} : Tree F n t
  | test {t} (a b : Operand F n t) (equal unequal : Tree F n t) : Tree F n t
  | op {t} (f : Op) (a b : Operand F n t) (next : Tree F n (t + 1)) : Tree F n t
  | divide {t} (a b : Operand F n t) (next : Tree F n (t + 1)) (failure : Tree F n t) : Tree F n t

variable {F : Type*} {n t : ℕ}

def Operand.raise : Operand F n t → Operand F n (t + 1)
  | .scalar a => .scalar a
  | .input i => .input i
  | .aux j => .aux j.castSucc

@[simp] theorem Operand.eval_raise (a : Operand F n t) (x : Index n → F) (w : Fin (t + 1) → F) :
    a.raise.eval x w = a.eval x (Fin.init w) := by
  cases a <;> rfl

def Tree.depth {t : ℕ} : Tree F n t → ℕ
  | .yes | .no => 0
  | .test _ _ u v => max u.depth v.depth + 1
  | .op _ _ _ u => u.depth + 1
  | .divide _ _ u v => max u.depth v.depth + 1

variable [Field F]

def Tree.run {t : ℕ} : Tree F n t → (Index n → F) → (Fin t → F) → Prop
  | .yes, _, _ => True
  | .no, _, _ => False
  | .test a b u v, x, w => if a.eval x w = b.eval x w then u.run x w else v.run x w
  | .op f a b u, x, w => u.run x (Fin.snoc w (f.eval (a.eval x w) (b.eval x w)))
  | .divide a b u v, x, w => if b.eval x w = 0 then v.run x w
      else u.run x (Fin.snoc w (a.eval x w / b.eval x w))

def Tree.accept (u : Tree F n t) (x : Index n → F) := ∃ w, u.run x w

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end
