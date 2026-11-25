import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Gaps
import Mathlib.Algebra.MvPolynomial.Equiv
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Geometry.Jacobian
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Geometry.Cuts
import OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification.Geometry.Ray
import Mathlib.Tactic.LinearCombination
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Algebra.MvPolynomial.Funext

universe u

/-! # Equations with at most one product of affine forms -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open scoped Classical

abbrev Affine (I : Type) (F : Type*) := F × (I → F)

structure Equation (I : Type) (F : Type*) where
  left : Affine I F
  right : Affine I F
  value : Affine I F

variable {I : Type} [Fintype I] {F K : Type*} [Field F] [Field K] [Algebra F K]

namespace Affine

def eval (a : Affine I F) (x : I → K) : K :=
  algebraMap F K a.1 + ∑ i, algebraMap F K (a.2 i) * x i

def const (x : F) : Affine I F := (x, 0)
def coord (i : I) : Affine I F := (0, fun j => if j = i then 1 else 0)

@[simp] theorem eval_const (z : F) (x : I → K) : (const z).eval x = algebraMap F K z := by
  simp [eval, const]

@[simp] theorem eval_coord (i : I) (x : I → K) : (coord (F:=F) i).eval x = x i := by
  simp [eval, coord, apply_ite]

@[simp] theorem eval_add (a b : Affine I F) (x : I → K) :
    eval (a + b) x = a.eval x + b.eval x := by
  simp [eval, add_mul, Finset.sum_add_distrib, add_add_add_comm]

@[simp] theorem eval_sub (a b : Affine I F) (x : I → K) :
    eval (a - b) x = a.eval x - b.eval x := by
  simp only [eval, Prod.fst_sub, Prod.snd_sub, Pi.sub_apply, map_sub, sub_mul, Finset.sum_sub_distrib]
  abel

def poly (a : Affine I F) : MvPolynomial I F :=
  MvPolynomial.C a.1 + ∑ i, MvPolynomial.C (a.2 i) * MvPolynomial.X i

@[simp] theorem aeval_poly (a : Affine I F) (x : I → K) :
    MvPolynomial.aeval x a.poly = a.eval x := by
  simp [poly, eval]

end Affine

def Equation.holds (a : Equation I F) (x : I → K) := a.left.eval x * a.right.eval x = a.value.eval x

def Equation.poly (a : Equation I F) : MvPolynomial I F :=
  a.left.poly * a.right.poly - a.value.poly

theorem Equation.zero (a : Equation I F) (x : I → K) :
    MvPolynomial.aeval x a.poly = 0 ↔ a.holds x := by
  simp only [Equation.poly, map_sub, map_mul, Affine.aeval_poly, sub_eq_zero, holds]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Covering correct products by conjunctions of accepting paths

For a given correct input, retain one path for each accepting seed.
Any input accepted by all of those paths has at least the same
accepting weight, so the strict gap forces it to be correct.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset
open scoped Classical

theorem packet_cover {F : Type*} [Field F] {n : ℕ} (hn : 0 < n)
    {ι : Type*} {w : ι → ℝ} {S : Finset ι} {A : ι → Verifier F n} {c : ℝ}
    (hw : ∀ i ∈ S, 0 ≤ w i) (hc : ∀ i ∈ S, (A i).cost c)
    (gap : Gap w (fun i => (A i).accept) Correct S) :
    ∃ B : Finset (Finset (Path F n)),
      (∀ t ∈ B, 0 < t.card ∧ t.card ≤ S.card ∧ (∀ p ∈ t, (p.code.length : ℝ) ≤ c) ∧
        ∀ y, (∀ p ∈ t, p.accept y) → Correct y) ∧
      ∀ x, Correct x → ∃ t ∈ B, ∀ p ∈ t, p.accept x := by
  let paths := S.biUnion fun i => (A i).toFinset
  let sound (t : Finset (Path F n)) := ∀ y, (∀ p ∈ t, p.accept y) → Correct y
  refine ⟨paths.powerset.filter (fun t => t.card ≤ S.card ∧ sound t), ?_, ?_⟩
  · intro t ht
    obtain ⟨ht, hs, hy⟩ := mem_filter.mp ht
    refine ⟨?_, hs, ?_, hy⟩
    · by_contra! he
      have hempty : t = ∅ := card_eq_zero.mp (Nat.eq_zero_of_le_zero he)
      let y : Index n → F := fun i => if i.1 = 2 then 1 else 0
      have h := hy y (by simp [hempty]) ⟨0, hn⟩ ⟨0, hn⟩
      simp [y] at h
    · intro p hp
      obtain ⟨i, hi, hp⟩ := mem_biUnion.mp (mem_powerset.mp ht hp)
      exact hc i hi p (List.mem_toFinset.mp hp)
  · intro x hx
    let I := S.filter (fun i => (A i).accept x)
    have ex (i : ↥I) : ∃ p ∈ A i.val, p.accept x := (mem_filter.mp i.property).2
    choose f hf ha using ex
    let t := I.attach.image f
    refine ⟨t, mem_filter.mpr ⟨mem_powerset.mpr ?_, ?_, ?_⟩, ?_⟩
    · intro p hp
      obtain ⟨i, _, rfl⟩ := mem_image.mp hp
      exact mem_biUnion.mpr ⟨i.val, (mem_filter.mp i.property).1, List.mem_toFinset.mpr (hf i)⟩
    · exact card_image_le.trans (card_attach.le.trans (card_filter_le ..))
    · intro y hy
      by_contra hn
      refine (gap x y hx hn).not_ge (sum_le_sum fun i hi => ?_)
      by_cases he : (A i).accept x
      · let j : ↥I := ⟨i, mem_filter.mpr ⟨hi, he⟩⟩
        have h : (A i).accept y := ⟨f j, hf j, hy _ (mem_image.mpr ⟨j, mem_attach _ _, rfl⟩)⟩
        simp [he, h]
      · by_cases h : (A i).accept y <;> simp [he, h, hw i hi]
    · intro p hp
      obtain ⟨i, _, rfl⟩ := mem_image.mp hp
      exact ha i

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # Defined division and nonzero tests as product equations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open scoped Classical

namespace Instruction
variable {I : Type} [Fintype I] {n t : ℕ} {F : Type*} [Field F]

def needs : Instruction F n t → Prop
  | .ne .. | .div .. => True
  | _ => False

def denominator (x : Index n → F) (w : Fin t → F) : Instruction F n t → F
  | .ne a b => a.eval x w - b.eval x w
  | .div _ b _ => b.eval x w
  | _ => 1

variable (r : Operand F n t → Affine I F) (s : Affine I F)

def emit : Instruction F n t → List (Equation I F)
  | .eq a b => [⟨r a, Affine.const 1, r b⟩]
  | .ne a b => [⟨r a - r b, s, Affine.const 1⟩]
  | .op .add a b c => [⟨r a + r b, Affine.const 1, r c⟩]
  | .op .sub a b c => [⟨r a - r b, Affine.const 1, r c⟩]
  | .op .mul a b c => [⟨r a, r b, r c⟩]
  | .div a b c => [⟨r c, r b, r a⟩, ⟨r b, s, Affine.const 1⟩]

omit [Fintype I] in
theorem emit_length (i : Instruction F n t) : (i.emit r s).length ≤ 2 := by
  cases i <;> first | exact le_rfl | exact Nat.one_le_ofNat | rename_i f a b c; cases f <;> exact one_le_two

theorem nonzero {x : Index n → F} {w : Fin t → F} (i : Instruction F n t) (hi : i.holds x w) :
    i.denominator x w ≠ 0 := by
  cases i with
  | eq | op => exact one_ne_zero
  | ne => exact sub_ne_zero.mpr hi
  | div => exact hi.1

theorem emit_iff (i : Instruction F n t) (x : Index n → F) (w : Fin t → F) (y : I → F)
    (hr : ∀ a, (r a).eval y = a.eval x w) :
    (∀ a ∈ i.emit r s, a.holds y) ↔
      i.holds x w ∧ (i.needs → i.denominator x w * s.eval y = 1) := by
  have nz (a : F) (ha : a * s.eval y = 1) : a ≠ 0 := fun h => by simp [h] at ha
  cases i with
  | eq a b => simp [emit, holds, Equation.holds, needs, hr]
  | op f a b c => cases f <;> simp [emit, holds, Op.eval, Equation.holds, needs, hr]
  | ne a b =>
    simp only [emit, List.mem_singleton, forall_eq, Equation.holds, Affine.eval_sub, Affine.eval_const,
      map_one, hr, holds, needs, true_implies, denominator]
    exact ⟨fun he => ⟨sub_ne_zero.mp (nz _ he), he⟩, And.right⟩
  | div a b c =>
    simp only [emit, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff, implies_true, and_true,
      Equation.holds, Affine.eval_const, map_one, hr, holds, needs, true_implies, denominator]
    exact ⟨fun ⟨he, hq⟩ => ⟨⟨nz _ hq, (div_eq_iff (nz _ hq)).mpr he.symm⟩, hq⟩,
      fun ⟨⟨hn, he⟩, hq⟩ => ⟨((div_eq_iff hn).mp he).symm, hq⟩⟩

end Instruction
end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# A polynomial system for one accepting path

Only nonzero tests and quotients introduce extra inverse variables.
Projecting away those variables recovers the original path on every
assignment of the inputs and registers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open scoped Classical

namespace Path

variable {F K : Type*} {n : ℕ} (p : Path F n)

abbrev Inv := {j : Fin p.code.length // (p.code.get j).needs}
def extra := Fintype.card p.Inv
abbrev Witness := Fin p.vars ⊕ Fin p.extra
abbrev Var := Index n ⊕ p.Witness

theorem extra_le : p.extra ≤ p.code.length :=
  (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin _)

variable [Field F]

private def name : Operand F n p.vars → Affine p.Var F
  | .scalar c => Affine.const c
  | .input i => Affine.coord (.inl i)
  | .aux j => Affine.coord (.inr (.inl j))

private def invName (j : Fin p.code.length) : Affine p.Var F :=
  if h : (p.code.get j).needs then
    Affine.coord (.inr (.inr (Fintype.equivFin p.Inv ⟨j, h⟩))) else Affine.const 0

def equations : List (Equation p.Var F) :=
  (List.finRange p.code.length).flatMap fun j => (p.code.get j).emit p.name (p.invName j)

theorem equations_length : p.equations.length ≤ 2 * p.code.length := by
  let f := fun j => (p.code.get j).emit p.name (p.invName j)
  have size (l : List (Fin p.code.length)) : (l.flatMap f).length ≤ 2 * l.length := by
    induction l with
    | nil => simp
    | cons a l ih =>
      have ha : (f a).length ≤ 2 := Instruction.emit_length _ _ _
      simp only [List.flatMap_cons, List.length_append, List.length_cons]; omega
  simpa only [equations, List.length_finRange] using size (List.finRange p.code.length)

def Solves [Field K] [Algebra F K] (x : Index n → K) :=
  ∃ v : p.Witness → K, ∀ e ∈ p.equations, e.holds (Sum.elim x v)

private theorem name_eq (x : Index n → F) (w : Fin p.vars → F) (v : Fin p.extra → F)
    (a : Operand F n p.vars) : (p.name a).eval (Sum.elim x (Sum.elim w v)) = a.eval x w := by
  cases a <;> simp [name, Operand.eval]

theorem project (x : Index n → F) (w : Fin p.vars → F) :
    (∃ v : Fin p.extra → F, ∀ e ∈ p.equations, e.holds (Sum.elim x (Sum.elim w v))) ↔
      ∀ i ∈ p.code, i.holds x w := by
  constructor
  · rintro ⟨v, hv⟩ i hi
    obtain ⟨j, rfl⟩ := List.mem_iff_get.mp hi
    exact ((Instruction.emit_iff p.name (p.invName j) (p.code.get j) x w _ (p.name_eq x w v)).mp
      (fun e he => hv e (List.mem_flatMap.mpr ⟨j, List.mem_finRange _, he⟩))).1
  · intro hx
    let v (t : Fin p.extra) :=
      ((p.code.get ((Fintype.equivFin p.Inv).symm t).val).denominator x w)⁻¹
    refine ⟨v, ?_⟩
    intro e he
    obtain ⟨j, _, he⟩ := List.mem_flatMap.mp he
    have hj := hx (p.code.get j) (List.get_mem _ _)
    refine (Instruction.emit_iff p.name (p.invName j) (p.code.get j) x w _ (p.name_eq x w v)).mpr
      ⟨hj, ?_⟩ e he
    intro h
    simp only [invName, dite_eq_left h, Affine.eval_coord, Sum.elim_inr]
    change _ * v ((Fintype.equivFin p.Inv) ⟨j, h⟩) = 1
    simp only [v, Equiv.symm_apply_apply]
    exact mul_inv_cancel₀ ((p.code.get j).nonzero hj)

theorem solves_iff (x : Index n → F) : p.Solves x ↔ p.accept x := by
  constructor
  · rintro ⟨v, hv⟩
    have h : Sum.elim (v ∘ Sum.inl) (v ∘ Sum.inr) = v := by funext i; cases i <;> rfl
    exact ⟨_, (p.project x _).mp ⟨v ∘ Sum.inr, h.symm ▸ hv⟩⟩
  · rintro ⟨w, hw⟩
    obtain ⟨v, hv⟩ := (p.project x w).mpr hw
    exact ⟨_, hv⟩

end Path
end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # Separating the matrix pair from the proposed product -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open scoped Classical

abbrev PairIndex (n : ℕ) := Fin 2 × Pos n n

variable {F : Type*} {n : ℕ}

def join (x : PairIndex n → F) (y : Pos n n → F) (i : Index n) : F :=
  ![x (0, i.2), x (1, i.2), y i.2] i.1

def beta [CommRing F] (x : PairIndex n → F) (i : Pos n n) : F :=
  ∑ j, x (0, i.1, j) * x (1, j, i.2)

theorem correct_join [Field F] (x : PairIndex n → F) (y : Pos n n → F) :
    Correct (join x y) ↔ y = beta x :=
  ⟨fun h => funext fun z => (h z.1 z.2).symm, fun h i j => (congrFun h (i, j)).symm⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # A system of affine equations with shared products and offsets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial

structure Jet (F : Type*) (τ σ : Type) (q d : ℕ) where
  affine : σ → Affine (τ ⊕ σ) F
  left : Fin q → Affine (τ ⊕ σ) F
  right : Fin q → Affine (τ ⊕ σ) F
  c : Matrix σ (Fin q) F
  f : Matrix σ (Fin d) F

variable {F K E : Type*} [Field F] [Field K] [Algebra F K]
  {τ σ : Type} [Fintype τ] [Fintype σ] {q d : ℕ}

def Affine.specialize (a : Affine (τ ⊕ σ) F) (x : τ → K) : MvPolynomial σ K :=
  aeval (Sum.elim (C ∘ x) X) a.poly

def Jet.system (J : Jet F τ σ q d) (x : τ → K) (m : Fin d → K) (i : σ) : MvPolynomial σ K :=
  (J.affine i).specialize x + ∑ j, C (algebraMap F K (J.c i j)) *
    ((J.left j).specialize x * (J.right j).specialize x) - C (∑ j, algebraMap F K (J.f i j) * m j)

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # Changing the coefficient field of the equations and their Jacobian -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial

section
variable {F K L : Type*} [Field F] [Field K] [Field L] [Algebra F K] [Algebra K L]
  [Algebra F L] [IsScalarTower F K L] {τ σ : Type} [Fintype τ] [Fintype σ] {q d : ℕ}

private theorem Affine.map_specialize (a : Affine (τ ⊕ σ) F) (x : τ → K) :
    MvPolynomial.map (algebraMap K L) (a.specialize x) = a.specialize (algebraMap K L ∘ x) := by
  have hc : (MvPolynomial.map (σ := σ) (algebraMap K L)).comp (algebraMap F (MvPolynomial σ K)) =
      algebraMap F (MvPolynomial σ L) := by
    apply RingHom.ext
    intro c
    change MvPolynomial.map (algebraMap K L) (C (algebraMap F K c)) = C (algebraMap F L c)
    rw [map_C, ← IsScalarTower.algebraMap_apply F K L]
  rw [Affine.specialize, map_aeval, hc]
  have hv : (fun i : τ ⊕ σ => MvPolynomial.map (algebraMap K L) (Sum.elim (C ∘ x) X i)) =
      Sum.elim (C ∘ (algebraMap K L ∘ x)) X := by
    funext i
    cases i <;> simp
  rw [hv]
  rfl

theorem Jet.map_system (J : Jet F τ σ q d) (x : τ → K) (m : Fin d → K) (i : σ) :
    MvPolynomial.map (algebraMap K L) (J.system x m i) =
      J.system (algebraMap K L ∘ x) (algebraMap K L ∘ m) i := by
  simp only [system, map_sub, map_add, map_sum, map_mul, map_C, Affine.map_specialize,
    ← IsScalarTower.algebraMap_apply F K L, Function.comp_apply]

end

theorem map_jacobian {K L E : Type u} [Field K] [Field L] [Field E]
    [Algebra K L] [Algebra L E] [Algebra K E] [IsScalarTower K L E]
    {σ : Type} (G : σ → MvPolynomial σ K) (a : σ → E) :
    jacobian (fun i => MvPolynomial.map (algebraMap K L) (G i)) a = jacobian G a := by
  ext i j
  rw [jacobian, pderiv_map, jacobian, aeval_def, aeval_def, eval₂_map, ← IsScalarTower.algebraMap_eq K L E]

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# A simple solution specializing to an isolated one

Move the polynomial values along a ray whose direction is algebraically
independent over the original coefficients. Isolation supplies a component
on which the ray parameter varies. The values on this component are
algebraically independent over the original field, so the Jacobian is
invertible. Normalizing the curve gives a local ring for specialization.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial
variable {K L : Type u} [Field K] [Field L] [Algebra K L] {σ : Type}

private theorem map_isolated {G : σ → MvPolynomial σ K} {x : σ → K}
    (h : Isolated x (Ideal.span (Set.range G))) :
    Isolated (algebraMap K L ∘ x) (Ideal.span (Set.range (MvPolynomial.map (algebraMap K L) ∘ G))) := by
  rw [Set.range_comp, ← Ideal.map_span]
  exact h.map (algebraMap K L)

theorem simple_lift [Fintype σ] [DecidableEq σ] [CharZero L] [IsAlgClosed L]
    (G : σ → MvPolynomial σ K) (x : σ → K) (h : Isolated x (Ideal.span (Set.range G)))
    (c : σ → L) (hc : AlgebraicIndependent K c) :
    let g := MvPolynomial.map (algebraMap K L) ∘ G
    ∃ (E : Type u) (_ : Field E) (_ : Algebra L E) (t : E) (b : Branch L E t) (y : σ → b.ring),
      Transcendental L t ∧ (∀ i, b.res (y i) = algebraMap K L (x i)) ∧
      (∀ i, aeval (fun j => (y j : E)) (g i) = t * algebraMap L E (c i)) ∧
      IsUnit (jacobian g (fun j => (y j : E))) := by
  intro g
  obtain ⟨d⟩ := exists_deformation g c (algebraMap K L ∘ x) (map_isolated h)
  let E := d.E
  let _ : Algebra K E := ((algebraMap L E).comp (algebraMap K L)).toAlgebra
  have : IsScalarTower K L E := IsScalarTower.of_algebraMap_eq' rfl
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap L E).injective
  let a (j : σ) : E := d.y j
  have ht := transcendental_of_residue d.ring d.res d.t d.nonzero d.zero
  have eqn (i : σ) : aeval a (G i) = (d.t : E) * algebraMap L E (c i) := by
    have eq := d.ray i
    simp only [g, Function.comp_apply, aeval_def, eval₂_map] at eq
    exact eq
  have hi := isUnit_jacobian G a (independent_ray hc ht eqn)
  have alg := algebraic_ray hc ht eqn d.generates
  obtain ⟨b, hb, hs⟩ := exists_branch d.ring d.fg d.res d.t d.nonzero d.zero alg
  let y i : b.ring := ⟨a i, hb (d.y i).property⟩
  refine ⟨E, inferInstance, inferInstance, d.t, b, y, ht, fun i => (hs _).trans (d.point i), d.ray, ?_⟩
  change IsUnit (jacobian (fun i => MvPolynomial.map (algebraMap K L) (G i)) a)
  rw [map_jacobian]
  exact hi

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # The path equations with both input matrices fixed -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset MvPolynomial
open scoped Classical

variable {I J : Type} [Fintype I] [Fintype J] {F K : Type*} [Field F] [Field K] [Algebra F K]

namespace Affine

def evalₗ (x : I → K) : Affine I F →ₗ[F] K where
  toFun a := a.eval x
  map_add' _ _ := eval_add _ _ _
  map_smul' c a := by
    simp [eval, Algebra.smul_def, mul_assoc, mul_add, mul_sum]

theorem eval_specialize (a : Affine (I ⊕ J) F) (x : I → K) (y : J → K) :
    MvPolynomial.eval y (a.specialize x) = a.eval (Sum.elim x y) := by
  simp [specialize, poly, eval]

def relabel (f : I → J) (a : Affine I F) : Affine J F :=
  const a.1 + ∑ i, a.2 i • coord (f i)

theorem eval_relabel (f : I → J) (a : Affine I F) (x : J → K) :
    (a.relabel f).eval x = a.eval (x ∘ f) := by
  change evalₗ x (_ + _) = _
  rw [map_add, map_sum]
  simp_rw [map_smul]
  simp only [evalₗ, LinearMap.coe_mk, AddHom.coe_mk, eval_const, eval_coord, Algebra.smul_def]
  rfl

end Affine

namespace Path
variable {n : ℕ} (p : Path F n)

abbrev Unk := Pos n n ⊕ p.Witness

def split : p.Var → PairIndex n ⊕ p.Unk :=
  Sum.elim (join Sum.inl (Sum.inr ∘ Sum.inl)) (Sum.inr ∘ Sum.inr)

omit [Field F] [Field K] [Algebra F K] in
theorem eval_split (x : PairIndex n → K) (β : Pos n n → K) (y : p.Witness → K) :
    Sum.elim x (Sum.elim β y) ∘ p.split = Sum.elim (join x β) y := by
  funext t
  rcases t with ⟨i, u⟩ | j
  · fin_cases i <;> rfl
  · rfl

def fixedEq (fixed : p.Witness → Option F) (i : p.Witness) : Affine (PairIndex n ⊕ p.Unk) F :=
  match fixed i with
  | none => Affine.const 0
  | some a => Affine.coord (.inr (.inr i)) - Affine.const a

def generators (x : PairIndex n → K) (fixed : p.Witness → Option F) :
    Fin p.equations.length ⊕ p.Witness → MvPolynomial p.Unk K :=
  Sum.elim (fun i =>
    let e := p.equations.get i
    (e.left.relabel p.split).specialize x * (e.right.relabel p.split).specialize x -
      (e.value.relabel p.split).specialize x) (fun i => (p.fixedEq fixed i).specialize x)

def ideal (x : PairIndex n → K) (fixed : p.Witness → Option F) :=
  Ideal.span (Set.range (p.generators x fixed))

theorem ideal_iff (x : PairIndex n → K) (fixed : p.Witness → Option F) (β : Pos n n → K)
    (y : p.Witness → K) : p.ideal x fixed ≤ maxPoint (Sum.elim β y) ↔
    (∀ e ∈ p.equations, e.holds (Sum.elim (join x β) y)) ∧
      (∀ i a, fixed i = some a → y i = algebraMap F K a) := by
  have he (i : Fin p.equations.length) :
      p.generators x fixed (.inl i) ∈ maxPoint (Sum.elim β y) ↔
        (p.equations.get i).holds (Sum.elim (join x β) y) := by
    simp only [maxPoint, RingHom.mem_ker, generators, Sum.elim_inl, map_sub, map_mul, Affine.eval_specialize,
      Affine.eval_relabel, eval_split, sub_eq_zero, Equation.holds]
  have hf (i : p.Witness) :
      p.generators x fixed (.inr i) ∈ maxPoint (Sum.elim β y) ↔
        (∀ a, fixed i = some a → y i = algebraMap F K a) := by
    simp only [maxPoint, RingHom.mem_ker, generators, Sum.elim_inr, Affine.eval_specialize, fixedEq]
    cases fixed i <;> simp [sub_eq_zero]
  rw [ideal, Ideal.span_le, Set.range_subset_iff]
  constructor
  · intro h
    refine ⟨fun e he' => ?_, fun i => (hf i).mp (h _)⟩
    obtain ⟨i, rfl⟩ := List.mem_iff_get.mp he'
    exact (he i).mp (h _)
  · rintro ⟨h, h'⟩ (i|i)
    · exact (he i).mpr (h _ (List.get_mem _ _))
    · exact (hf i).mpr (h' i)

end Path
end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Mixed derivatives of the verification equations

Subtract the Jacobian applied to the mixed derivatives of the unknowns.
The remainder is additive and vanishes on affine forms when the inputs
have vanishing mixed derivatives. Each shared product contributes two
products of first derivatives.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open MvPolynomial

variable {F K E : Type u} [Field F] [Field K] [Field E] [Algebra K E] [Algebra F E]
  {τ σ : Type} [Fintype τ] [Fintype σ]
  {q d : ℕ}

variable (Y : σ → E) (D D' : Derivation F E E)

private def remMixed : MvPolynomial σ K →+ E where
  toFun p := D' (D (aeval Y p)) - ∑ j, aeval Y (pderiv j p) * D' (D (Y j))
  map_zero' := by simp
  map_add' p p' := by
    simp only [map_add, add_mul, Finset.sum_add_distrib]
    abel

private theorem rem_C (k : K) :
    remMixed Y D D' (C k) = D' (D (algebraMap K E k)) := by
  simp [remMixed]

private theorem rem_X (j : σ) :
    remMixed Y D D' (X j : MvPolynomial σ K) = 0 := by
  classical
  simp [remMixed, Pi.single_apply, apply_ite]

private theorem rem_mul (p r : MvPolynomial σ K) :
    remMixed Y D D' (p * r) =
      aeval Y p * remMixed Y D D' r + aeval Y r * remMixed Y D D' p +
      (D (aeval Y p) * D' (aeval Y r) + D (aeval Y r) * D' (aeval Y p)) := by
  simp only [remMixed, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_mul, Derivation.leibniz,
    smul_eq_mul, map_add, add_mul, mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

variable [Algebra F K] [IsScalarTower F K E]

private theorem rem_const_mul (z : F) (p : MvPolynomial σ K) :
    remMixed Y D D' (C (algebraMap F K z) * p) = algebraMap F E z * remMixed Y D D' p := by
  simp [rem_mul, rem_C, ← IsScalarTower.algebraMap_apply F K E]

private theorem rem_affine (a : Affine (τ ⊕ σ) F) (x : τ → K)
    (hx : ∀ k, D' (D (algebraMap K E (x k))) = 0) :
    remMixed Y D D' (a.specialize x) = 0 := by
  simp [Affine.specialize, Affine.poly, rem_const_mul, rem_C, rem_X, hx,
    ← IsScalarTower.algebraMap_apply F K E]

theorem Jet.mixed (J : Jet F τ σ q d) (x : τ → K) (m : Fin d → K)
    (Y : σ → E) (D D' : Derivation F E E) (i : σ)
    (hi : D' (D (aeval Y (J.system x m i))) = 0)
    (hx : ∀ k, D' (D (algebraMap K E (x k))) = 0) :
    (∑ j, jacobian (J.system x m) Y i j * D' (D (Y j))) +
      (∑ j, algebraMap F E (J.c i j) *
        (D (aeval Y ((J.left j).specialize x)) * D' (aeval Y ((J.right j).specialize x)) +
         D (aeval Y ((J.right j).specialize x)) * D' (aeval Y ((J.left j).specialize x)))) =
      ∑ j, algebraMap F E (J.f i j) * D' (D (algebraMap K E (m j))) := by
  have h := show remMixed Y D D' (J.system x m i) =
    D' (D (aeval Y (J.system x m i))) - ∑ j, jacobian (J.system x m) Y i j * D' (D (Y j)) from rfl
  conv at h =>
    lhs
    simp only [Jet.system, map_sub, map_add, map_sum, map_mul, rem_const_mul]
    simp only [rem_mul, rem_affine Y D D' _ x hx, rem_C, mul_zero, zero_add]
  linear_combination hi + h

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Combining paths while sharing the same product claim

All path witnesses have disjoint names. One reserved variable permits
a test that a specified output coordinate differs from the true one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open scoped Classical

namespace Packet
open MvPolynomial
variable {F K : Type*} [Field F] [Field K] [Algebra F K] {n : ℕ}
    (T : Finset (Path F n))

abbrev Extra := Pos n n ⊕ (Σ i : ↥T, i.val.Witness) ⊕ Unit
abbrev Name := PairIndex n ⊕ Extra T

def locate (i : ↥T) : i.val.Var → Name T :=
  Sum.elim (join Sum.inl (fun j => .inr (.inl j))) (fun j => .inr (.inr (.inl ⟨i, j⟩)))

def equations : Set (MvPolynomial (Name T) F) :=
  {f | ∃ i : ↥T, ∃ e ∈ i.val.equations, f = rename (locate T i) e.poly}

def output (w : Extra T → K) : Pos n n → K := w ∘ Sum.inl

private def registers (w : Extra T → K) (i : ↥T) (j : i.val.Witness) : K :=
  w (.inr (.inl ⟨i, j⟩))

def inverse : Extra T := .inr (.inr ())

omit [Field F] [Field K] [Algebra F K] in
private theorem locate_eq (x : PairIndex n → K) (w : Extra T → K) (i : ↥T) :
    Sum.elim x w ∘ locate T i = Sum.elim (join x (output T w)) (registers T w i) := by
  funext j
  rcases j with ⟨a, b⟩ | j
  · fin_cases a <;> rfl
  · rfl

variable (x : PairIndex n → K) (w : Extra T → K)

theorem solves (hz : ∀ f ∈ equations T, aeval (Sum.elim x w) f = 0) :
    ∀ p ∈ T, p.Solves (join x (output T w)) := by
  intro p hp
  let i : ↥T := ⟨p, hp⟩
  refine ⟨registers T w i, fun e he => ?_⟩
  have h := hz _ ⟨i, e, he, rfl⟩
  rw [aeval_rename, locate_eq, Equation.zero] at h
  exact h

theorem pack (z : Pos n n → K) (a : K) (hs : ∀ p ∈ T, p.Solves (join x z)) :
    ∃ w : Extra T → K, output T w = z ∧ w (inverse T) = a ∧
      ∀ f ∈ equations T, aeval (Sum.elim x w) f = 0 := by
  choose v hv using fun i : ↥T => hs i.val i.property
  let w : Extra T → K := Sum.elim z (Sum.elim (fun j => v j.1 j.2) (fun _ => a))
  refine ⟨w, rfl, rfl, ?_⟩
  rintro _ ⟨i, e, he, rfl⟩
  rw [aeval_rename, locate_eq, Equation.zero]
  exact hv i e he

def discrepancy (i : Pos n n) : MvPolynomial (Name T) F :=
  (X (.inr (.inl i)) - beta (fun v => X (.inl v)) i) * X (.inr (inverse T)) - 1

theorem discrepancy_zero (i : Pos n n) :
    aeval (Sum.elim x w) (discrepancy T i) = 0 ↔ (output T w i - beta x i) * w (inverse T) = 1 := by
  simp only [discrepancy, beta, output, Function.comp_apply, map_sub, map_mul, map_sum, map_one,
    aeval_X, Sum.elim_inl, Sum.elim_inr, sub_eq_zero]

end Packet
end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-!
# Isolating the correct product at algebraically independent inputs

A strict probability gap supplies a finite cover by conjunctions of
paths. Each conjunction excludes every false product even after
extending scalars. At least one conjunction is feasible generically.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open scoped Classical
variable {F K : Type*} [Field F] [Field K] [Algebra F K] [IsAlgClosed F] {n : ℕ}

private theorem Packet.sound (T : Finset (Path F n))
    (h : ∀ y, (∀ p ∈ T, p.accept y) → Correct y) {x : PairIndex n → K} {z : Pos n n → K}
    (hz : ∀ p ∈ T, p.Solves (join x z)) : z = beta x := by
  funext i
  by_contra hi
  obtain ⟨w, ho, ha, he⟩ := Packet.pack T x z (z i - beta x i)⁻¹ hz
  let B := insert (Packet.discrepancy T i) (Packet.equations T)
  have bad : ∀ e ∈ B, MvPolynomial.aeval (Sum.elim x w) e = 0 := by
    rintro e (rfl|he')
    · rw [Packet.discrepancy_zero, ho, ha]
      exact mul_inv_cancel₀ (sub_ne_zero.mpr hi)
    · exact he _ he'
  obtain ⟨y, hy⟩ := descend_point B _ bad
  let x' := y ∘ Sum.inl
  let w' := y ∘ Sum.inr
  have eq : Sum.elim x' w' = y := by funext v; cases v <;> rfl
  rw [← eq] at hy
  have hs := Packet.solves T x' w' (fun e he => hy e (Set.mem_insert_of_mem _ he))
  have ok := h _ (fun p hp => (p.solves_iff _).mp (hs p hp))
  have he := (Packet.discrepancy_zero T x' w' i).mp (hy _ (Set.mem_insert _ _))
  rw [(correct_join ..).mp ok, sub_self, zero_mul] at he
  exact zero_ne_one he

theorem specialization [IsAlgClosed K] (hn : 0 < n)
    {ι : Type*} {w : ι → ℝ} {S : Finset ι} {A : ι → Verifier F n} {c : ℝ}
    (hw : ∀ i ∈ S, 0 ≤ w i) (hc : ∀ i ∈ S, (A i).cost c)
    (gap : Gap w (fun i => (A i).accept) Correct S)
    {X : PairIndex n → K} (hx : AlgebraicIndependent F X) :
    ∃ l : ℕ, 0 < l ∧ l ≤ S.card ∧ ∃ p : Fin l → Path F n,
      (∀ i, ((p i).code.length : ℝ) ≤ c) ∧ ∀ Z, (∀ i, (p i).Solves (join X Z)) ↔ Z = beta X := by
  obtain ⟨B, sound, live⟩ := packet_cover hn hw hc gap
  have lift (x : PairIndex n → F) : ∃ i : ↥B, ∃ w : Packet.Extra i.val → F,
      ∀ e ∈ Packet.equations i.val, MvPolynomial.eval (Sum.elim x w) e = 0 := by
    obtain ⟨t, ht, hp⟩ := live _ ((correct_join x (beta x)).mpr rfl)
    obtain ⟨v, _, _, hv⟩ := Packet.pack t x (beta x) 0 (fun p h => (p.solves_iff _).mpr (hp p h))
    exact ⟨⟨t, ht⟩, v, hv⟩
  obtain ⟨⟨t, ht⟩, v, hv⟩ := generic_point hx (fun i : ↥B => Packet.Extra i.val)
    (fun i => Packet.equations i.val) lift
  obtain ⟨hl, hcard, hcost, hs⟩ := sound t ht
  have good := Packet.solves t X v hv
  have correct := Packet.sound t hs good
  let E : Fin t.card ≃ ↥t := (Fintype.equivOfCardEq (by simp))
  refine ⟨t.card, hl, hcard, fun i => (E i).val, fun i => hcost _ (E i).property, fun Z => ?_⟩
  constructor
  · intro h
    apply Packet.sound t hs
    intro p hp
    simpa only [Equiv.apply_symm_apply] using h (E.symm ⟨p, hp⟩)
  · intro he i
    rw [he, ← correct]
    exact good _ (E i).property

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # Isolating a solution of one path by rational output measurements -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open scoped Classical
variable {F K : Type*} [Field F] [Field K] [Algebra F K] {n : ℕ}

namespace Path
variable (p : Path F n) (x : PairIndex n → K) (z : Pos n n → K)

private def atOutput (e : Equation p.Var F) : MvPolynomial p.Witness K :=
  e.left.specialize (join x z) * e.right.specialize (join x z) - e.value.specialize (join x z)

private theorem eval_output (e : Equation p.Var F) (y : p.Witness → K) :
    MvPolynomial.eval y (p.atOutput x z e) = 0 ↔ e.holds (Sum.elim (join x z) y) := by
  simp only [atOutput, map_sub, map_mul, Affine.eval_specialize, sub_eq_zero, Equation.holds]

theorem finite_fiber [Infinite F] [IsAlgClosed K] (h : p.Solves (join x z)) :
    ∃ b : p.Witness → Option F, ∃ y : p.Witness → K,
      p.ideal x b ≤ maxPoint (Sum.elim z y) ∧
      Set.Finite {v : p.Witness → K | p.ideal x b ≤ maxPoint (Sum.elim z v)} := by
  let B := p.atOutput x z '' {e | e ∈ p.equations}
  have he (y : p.Witness → K) : (∀ q ∈ B, MvPolynomial.eval y q = 0) ↔
      ∀ e ∈ p.equations, e.holds (Sum.elim (join x z) y) := by
    simp only [B, Set.forall_mem_image, Set.mem_ofPred_eq, eval_output]
  obtain ⟨y, hy⟩ := h
  obtain ⟨b, ⟨w, hw⟩, hb⟩ := finite_slice F B ⟨y, (he y).mpr hy⟩
  have eq (v : p.Witness → K) : v ∈ slice B b ↔ p.ideal x b ≤ maxPoint (Sum.elim z v) := by
    simp only [slice, Set.mem_ofPred_eq, he, ideal_iff]
  exact ⟨b, w, (eq w).mp hw, hb.subset (fun v hv => (eq v).mpr hv)⟩

end Path

theorem path_cut [Infinite F] [CharZero K] [IsAlgClosed K] {l : ℕ} (hl : 0 < l)
    (p : Fin l → Path F n) (x : PairIndex n → K) (z : Pos n n → K)
    (h : ∀ y, (∀ i, (p i).Solves (join x y)) ↔ y = z) :
    ∃ (i : Fin l) (d : ℕ), d ≤ n * n ∧ n * n ≤ l * (n * n - d) ∧
      ∃ (b : (p i).Witness → Option F) (y : (p i).Witness → K) (H : Fin d → Pos n n → ℚ),
        Isolated (Sum.elim z y) ((p i).ideal x b ⊔ Ideal.span (Set.range (fun t => comb (offset z) (H t)))) := by
  let _ : Nonempty (Fin l) := ⟨⟨0, hl⟩⟩
  choose b w hw hf using fun i => (p i).finite_fiber x z ((h z).mpr rfl i)
  let I i := (p i).ideal x (b i)
  have hu (y : Pos n n → K) (hy : ∀ i, ∃ v, I i ≤ maxPoint (Sum.elim y v)) : y = z := by
    apply (h y).mp
    intro i
    obtain ⟨v, hv⟩ := hy i
    exact ⟨v, ((p i).ideal_iff x (b i) y v).mp hv |>.1⟩
  obtain ⟨joint, fiber⟩ := isolate_family I z w hw hf hu
  obtain ⟨i, d, hd, hl, H, hH⟩ := local_cut I z w joint fiber
  simp only [Pos, Fintype.card_prod, Fintype.card_fin] at hd hl
  exact ⟨i, d, hd, hl, b i, w i, H, hH⟩

end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end

/-! # A square system using only the products from the original path -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
open Finset MvPolynomial
open scoped Classical

variable {F K : Type*} [Field F] [Field K] [Algebra F K]

namespace Affine
variable {I L : Type} [Fintype I] [Fintype L]

private def blend (b : L → ℚ) (a : L → Affine I F) : Affine I F := ∑ i, (b i : F) • a i

private theorem eval_blend (b : L → ℚ) (a : L → Affine I F) (x : I → K) :
    (blend b a).eval x = ∑ i, (b i : K) * (a i).eval x := by
  change evalₗ x (∑ i, (b i : F) • a i) = _
  rw [map_sum]
  simp_rw [map_smul, Algebra.smul_def, map_ratCast]
  rfl

end Affine

namespace Path

variable {n : ℕ} (p : Path F n)

/-- Fixing witnesses and measuring outputs adds only affine terms.
The rational combinations isolating the solution reuse every original
quadratic term, even when several equations need the same product. -/
theorem jet [CharZero K] (x : PairIndex n → K) (fixed : p.Witness → Option F)
    (β : Pos n n → K) (y : p.Witness → K) {d : ℕ} (H : Fin d → Pos n n → ℚ)
    (h : Isolated (Sum.elim β y) (p.ideal x fixed ⊔ Ideal.span (Set.range fun t => comb (offset β) (H t)))) :
    ∃ J : Jet F (PairIndex n) p.Unk p.equations.length d, ∃ m : Fin d → K,
      Isolated (Sum.elim β y) (Ideal.span (Set.range (J.system x m))) := by
  let G := Sum.elim (p.generators x fixed) (fun t => comb (offset β) (H t))
  have hg : Isolated (Sum.elim β y) (Ideal.span (Set.range G)) := by
    rw [show Set.range G = _ from Set.Sum.elim_range _ _, Ideal.span_union]
    exact h
  obtain ⟨A, hA⟩ := square_system (Sum.elim β y) G hg
  let a i j := A i (.inl (.inl j))
  let b i j := A i (.inl (.inr j))
  let c i j := A i (.inr j)
  let M (j : Fin d) : Affine (PairIndex n ⊕ p.Unk) F :=
    Affine.blend (H j) (fun z => Affine.coord (.inr (.inl z)))
  let m (j : Fin d) := ∑ z, (H j z : K) * β z
  let e := p.equations.get
  let J : Jet F (PairIndex n) p.Unk p.equations.length d :=
    { affine := fun i => Affine.blend (b i) (p.fixedEq fixed) + Affine.blend (c i) M -
        Affine.blend (a i) (fun j => (e j).value.relabel p.split)
      left := fun j => (e j).left.relabel p.split
      right := fun j => (e j).right.relabel p.split
      c := fun i j => a i j
      f := fun i j => c i j }
  refine ⟨J, m, ?_⟩
  suffices he : J.system x m = (fun i => comb G (A i)) by rwa [he]
  funext i
  have : Infinite K := Infinite.of_injective (fun n : ℕ => (n : K)) Nat.cast_injective
  apply MvPolynomial.funext
  intro z
  have hm (j) : MvPolynomial.eval z (comb (offset β) (H j)) = (M j).eval (Sum.elim x z) - m j := by
    simp only [comb, offset, map_sum, map_mul, eval_C, map_sub, eval_X, M, Affine.eval_blend,
      Affine.eval_coord, Sum.elim_inr, m, mul_sub, sum_sub_distrib]
  rw [Jet.system, comb]
  simp only [map_sub, map_add, map_mul, map_sum, eval_C, Affine.eval_specialize]
  rw [Fintype.sum_sum_type (α₁ := Fin p.equations.length ⊕ p.Witness),
    Fintype.sum_sum_type (α₁ := Fin p.equations.length)]
  simp only [G, generators, Sum.elim_inl, Sum.elim_inr, map_mul, map_sub, Affine.eval_specialize, hm,
    J, Affine.eval_sub, Affine.eval_add, Affine.eval_blend, map_ratCast, a, b, c, e, mul_sub, sum_sub_distrib]
  abel

end Path
end OAI.LinearAlgebra.MatrixExponent.Rectangle.Verification
end
