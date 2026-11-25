import OAI.LinearAlgebra.MatrixExponent.Valued.Extension
import OAI.LinearAlgebra.TensorSpectrum.TagGrowth
import Mathlib.LinearAlgebra.Lagrange
import OAI.LinearAlgebra.MatrixExponent.Spectral.Placements
import Mathlib.Algebra.Algebra.Tower
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.LinearAlgebra.Dual.Lemmas
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.TreePrice

/-! # Evaluating tensor prices on coordinate arrays -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Spectral

variable {K S : Type} [Field K] [Fintype S] (O : Subring K)

/-- Forgetting integrality makes every permitted restriction an ordinary one. -/
def forget : ITensor O S →+* Tensor K S where
  toFun := Quotient.map id fun _ _ h => ⟨h.1.forget, h.2.forget⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' A B := Quotient.inductionOn₂ A B fun _ _ => rfl
  map_mul' A B := Quotient.inductionOn₂ A B fun _ _ => rfl

theorem forget_mono : Monotone (forget (S := S) O) :=
  fun x y => Quotient.inductionOn₂ x y fun _ _ h => h.forget

variable [Nonempty S] (X Y : S → Type) [∀ s, Fintype (X s)] [∀ s, Fintype (Y s)]

theorem table_mul (A : (∀ s, X s) → K) (B : (∀ s, Y s) → K) :
    table O (fun s => X s × Y s) (fun x => A (fun s => (x s).1) * B (fun s => (x s).2)) =
      table O X A * table O Y B := by
  apply ofRaw_eq
  refine equiv_coeff (fun _ => Equiv.refl _) fun x => ?_
  erw [Raw.coeff_mul, Raw.coeff_ofTable, Raw.coeff_ofTable, Raw.coeff_ofTable]
  rfl

theorem scalar_table (c : K) (A : (∀ s, X s) → K) :
    table O X (c • A) = scalar O S c * table O X A := by
  apply ofRaw_eq
  refine equiv_coeff (fun s => (Equiv.punitProd (X s)).symm) fun x => ?_
  erw [Raw.coeff_mul, Raw.coeff_ofTable, Raw.coeff_ofTable, Raw.coeff_ofTable]
  rfl

theorem scalar_le_one (c : K) (hc : c ∈ O) : scalar O S c ≤ 1 := by
  classical
  refine ⟨fun s _ _ => Raw.weight c s, ?_, fun x => ?_⟩
  · intro s _ _
    dsimp only [Raw.weight]
    split_ifs <;> simp [hc]
  · erw [Raw.coeff_ofTable]
    change c = ∑ _ : Unit, ∏ s : S, ∑ _ : Unit, Raw.weight c s * 1
    simp [Raw.weight]

variable {O}

theorem table_nonneg (f : ITensor O S →+* ℝ) (hf : Monotone f)
    (A : (∀ s, X s) → K) : 0 ≤ f (table O X A) := by
  rw [← map_zero f]
  exact hf (zero_le _)

theorem table_sum {I : Type*} (f : ITensor O S →+* ℝ) (hf : Monotone f)
    (s : Finset I) (A : I → (∀ s, X s) → K) :
    f (table O X (∑ i ∈ s, A i)) ≤ ∑ i ∈ s, f (table O X (A i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [table_zero]
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine (hf (table_add _ _ _ _)).trans ?_
    rw [map_add]
    exact add_le_add le_rfl ih

theorem table_span {I : Type*} (f : ITensor O S →+* ℝ) (hf : Monotone f)
    (s : Finset I) (A : I → (∀ s, X s) → K) (r : I → K) (hr : ∀ i ∈ s, f (scalar O S (r i)) ≤ 1) :
    f (table O X (∑ i ∈ s, r i • A i)) ≤ ∑ i ∈ s, f (table O X (A i)) := by
  refine (table_sum X f hf _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [scalar_table, map_mul]
  exact mul_le_of_le_one_left (table_nonneg X f hf _) (hr i hi)

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-!
# Interpolation at integral nodes

Pairwise unit differences keep the interpolation weights integral.
The linear overhead in degree disappears on taking tensor powers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Spectral

variable {K S : Type} [Field K] [Fintype S] [Nonempty S] {O : Subring K}

def Family (A : K → ITensor O S) (d : ℕ) : Prop :=
  ∃ (X : S → Type) (_ : ∀ s, Fintype (X s)) (P : (∀ s, X s) → Polynomial K),
    (∀ b, (P b).natDegree ≤ d) ∧ ∀ x, A x = table O X (fun b => (P b).eval x)

variable {A B : K → ITensor O S} {d e : ℕ}

theorem Family.mul (ha : Family A d) (hb : Family B e) :
    Family (fun x => A x * B x) (d + e) := by
  obtain ⟨X, _, P, hp, he⟩ := ha
  obtain ⟨Y, _, Q, hq, hf⟩ := hb
  refine ⟨fun s => X s × Y s, inferInstance, fun b => P (fun s => (b s).1) * Q (fun s => (b s).2),
    fun b => Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hp _) (hq _)), fun x => ?_⟩
  simp only [Polynomial.eval_mul, he, hf, ← table_mul]

theorem Family.pow (h : Family A d) (n : ℕ) :
    Family (fun x => A x ^ n) (n * d) := by
  induction n with
  | zero =>
    refine ⟨fun _ => Unit, inferInstance, fun _ => 1, by simp, fun x => ?_⟩
    simp only [pow_zero, Polynomial.eval_one]
    exact scalar_one.symm
  | succ n ih => simpa only [pow_succ, Nat.succ_mul] using ih.mul h

theorem table_sum_le {I : Type*} (X : S → Type) [∀ s, Fintype (X s)]
    (t : Finset I) (A : I → (∀ s, X s) → K) :
    table O X (∑ i ∈ t, A i) ≤ ∑ i ∈ t, table O X (A i) := by
  classical
  induction t using Finset.induction_on with
  | empty => simp [table_zero]
  | insert i t hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    refine (table_add O X _ _).trans ?_
    rw [add_comm (table O X (A i)), add_comm (table O X (A i))]
    exact add_le_add_right _ _ _ ih

theorem Family.weighted {I : Type*} [Fintype I] [DecidableEq I]
    (h : Family A d) (hn : d < Fintype.card I) (v : I → K) (hv : Function.Injective v)
    (x : K) : A x ≤ ∑ i, scalar O S ((Lagrange.basis Finset.univ v i).eval x) * A (v i) := by
  obtain ⟨X, _, P, hp, he⟩ := h
  let L (i : I) := (Lagrange.basis Finset.univ v i).eval x
  have E : (fun b => (P b).eval x) = ∑ i, L i • (fun b => (P b).eval (v i)) := by
    funext b
    have hd : (P b).degree < (Finset.univ : Finset I).card := by
      rw [Finset.card_univ]
      exact Polynomial.degree_le_natDegree.trans_lt (WithBot.coe_lt_coe.mpr ((hp b).trans_lt hn))
    have hz := congrArg (Polynomial.eval x) (Lagrange.eq_interpolate hv.injOn hd)
    simpa only [Lagrange.interpolate_apply, Polynomial.eval_finsetSum, Polynomial.eval_mul,
      Polynomial.eval_C, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, L, mul_comm] using hz
  rw [he, E]
  simp only [he]
  simpa only [scalar_table] using
    table_sum_le (O := O) X Finset.univ (fun i => L i • (fun b => (P b).eval (v i)))

theorem Family.interpolate (h : Family A d) (f : ITensor O S →+* ℝ) (hf : Monotone f)
    {V : Subring K} (hV : ∀ c ∈ V, f (scalar O S c) ≤ 1)
    {n : ℕ} (hn : d < n) (v : Fin n → K) (hv : Function.Injective v)
    (hi : ∀ i, v i ∈ V) (hu : ∀ i j, (v i - v j)⁻¹ ∈ V) (x : K) (hx : x ∈ V) :
    f (A x) ≤ ∑ i, f (A (v i)) := by
  let L (i : Fin n) := (Lagrange.basis Finset.univ v i).eval x
  have hL (i : Fin n) : L i ∈ V := by
    simp only [L, Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
    exact V.prod_mem fun j _ => V.mul_mem (hu i j) (V.sub_mem hx (hi j))
  have e := hf (h.weighted (by simpa using hn) v hv x)
  rw [map_sum] at e
  refine e.trans (Finset.sum_le_sum fun i _ => ?_)
  rw [f.map_mul]
  have hp : 0 ≤ f (A (v i)) := by simpa using hf (zero_le (A (v i)))
  exact mul_le_of_le_one_left hp (hV _ (hL i))

/-- The price at an integral parameter cannot exceed a uniform bound
on an infinite set of nodes having pairwise unit differences. -/
theorem Family.bound_scalar (h : Family A d) (f : ITensor O S →+* ℝ) (hf : Monotone f)
    {V : Subring K} (hV : ∀ c ∈ V, f (scalar O S c) ≤ 1)
    {J : Type*} [Infinite J] (v : J → K) (hv : Function.Injective v)
    (hi : ∀ i, v i ∈ V) (hu : ∀ i j, (v i - v j)⁻¹ ∈ V)
    {r : ℝ} (hr : ∀ j, f (A (v j)) ≤ r) (x : K) (hx : x ∈ V) : f (A x) ≤ r := by
  have hz (B : ITensor O S) : 0 ≤ f B := by simpa using hf (zero_le B)
  have hr0 := (hz _).trans (hr (Classical.arbitrary J))
  refine TensorSpectrum.le_of_pow_le_polynomial_mul_pow r (f (A x)) (d + 1) 1 hr0 (hz _)
    (by positivity) zero_le_one fun n _ => ?_
  let w : Fin (n * d + 1) ↪ J := Fin.valEmbedding.trans (Infinite.natEmbedding J)
  have he := (h.pow n).interpolate f hf hV (Nat.lt_succ_self (n * d)) (v ∘ w)
    (hv.comp w.injective) (fun i => hi (w i)) (fun i j => hu (w i) (w j)) x hx
  rw [Real.rpow_one]
  calc
    _ ≤ ∑ i, f (A (v (w i))) ^ n := by simpa only [map_pow, Function.comp_apply] using he
    _ ≤ ∑ _i : Fin (n * d + 1), r ^ n :=
      Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (hz _) (hr _) _
    _ ≤ _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hr0 n)
      push_cast
      linarith

theorem Family.bound (h : Family A d) (f : ITensor O S →+* ℝ) (hf : Monotone f)
    {J : Type*} [Infinite J] (v : J → K) (hv : Function.Injective v)
    (hi : ∀ i, v i ∈ O) (hu : ∀ i j, (v i - v j)⁻¹ ∈ O)
    {r : ℝ} (hr : ∀ j, f (A (v j)) ≤ r) (x : K) (hx : x ∈ O) : f (A x) ≤ r :=
  h.bound_scalar f hf (fun c hc => by simpa using hf (scalar_le_one O c hc)) v hv hi hu hr x hx

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-!
# Extracting base-field coefficients

Linear functionals on the ambient field commute with restrictions over
the base. They give additive evaluations, prior to imposing valuation
cutoffs on the functionals.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral

variable (E K : Type) [Field E] [Field K] [Algebra E K]

def constants : Subring K := (algebraMap E K).range

variable {E K} {S : Type} [Fintype S] [Nonempty S] (l : K →ₗ[E] E)

def sampleRaw (A : Raw K S) : Raw E S := Raw.ofTable A.leg (fun x => l (A.coeff x))

theorem sample_coeff (A : Raw K S) (x : ∀ s, A.leg s) :
    (sampleRaw l A).coeff x = l (A.coeff x) := Raw.coeff_ofTable _ _ _

theorem Restricts.sample {A B : Raw K S} (h : Restricts (constants E K) A B) :
    (sampleRaw l A).Restricts (sampleRaw l B) := by
  classical
  obtain ⟨L, hl, h⟩ := h
  choose M he using hl
  refine (Raw.restricts_iff _ _).mpr ⟨M, fun x => ?_⟩
  change (∀ s, B.leg s) at x
  erw [sample_coeff, h, A.expand, map_sum]
  refine Finset.sum_congr rfl fun y _ => ?_
  change (∀ s, A.leg s) at y
  erw [sample_coeff]
  rw [show (∏ s, L s (x s) (y s)) = algebraMap E K (∏ s, M s (x s) (y s)) by
    rw [map_prod]
    exact Finset.prod_congr rfl fun s _ => (he s _ _).symm]
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

omit [Nonempty S] in
private theorem side {X Y : S → Type}
    {I J : Type} [Fintype I] [Fintype J]
    (a : I → (s : S) → X s → K) (b : J → (s : S) → X s → E)
    (h : ∀ x : ∀ s, X s, l (∑ i, ∏ s, a i s (x s)) = ∑ j, ∏ s, b j s (x s))
    (x : ∀ s, X s ⊕ Y s) :
    l (∑ i, ∏ s, Sum.elim (a i s) (fun _ => 0) (x s)) =
      ∑ j, ∏ s, Sum.elim (b j s) (fun _ => 0) (x s) := by
  classical
  by_cases hx : ∀ s, ∃ u, x s = .inl u
  · choose u hu using hx
    simpa only [hu, Sum.elim_inl] using h u
  push Not at hx
  obtain ⟨s, hs⟩ := hx
  cases he : x s with
  | inl v => exact (hs _ he).elim
  | inr v =>
    rw [Finset.sum_eq_zero, map_zero, Finset.sum_eq_zero]
    all_goals exact fun _ _ => Finset.prod_eq_zero (Finset.mem_univ s) (by rw [he]; rfl)

private theorem sample_add (A B : Raw K S) :
    sampleRaw l (A + B) ≈ sampleRaw l A + sampleRaw l B := by
  let X := sampleRaw l A
  let Y := sampleRaw l B
  refine Raw.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_
  change (∀ s, A.leg s ⊕ B.leg s) at x
  erw [sample_coeff]
  change l (∑ i : A.term ⊕ B.term, ∏ s, (A + B).factor i s (x s)) =
    ∑ j : X.term ⊕ Y.term, ∏ s, (X + Y).factor j s (x s)
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, map_add]
  refine congrArg₂ (· + ·) (side l A.factor X.factor (fun u => (sample_coeff l A u).symm) x) ?_
  have he := side l B.factor Y.factor (fun u => (sample_coeff l B u).symm) (fun s => (x s).swap)
  convert he using 1
  · refine congrArg l (Finset.sum_congr rfl fun i _ => Finset.prod_congr rfl fun s _ => ?_)
    cases x s <;> rfl
  · refine Finset.sum_congr rfl fun i _ => Finset.prod_congr rfl fun s _ => ?_
    cases x s <;> rfl

def sample : ITensor (constants E K) S →+ Tensor E S where
  toFun := Quotient.map (sampleRaw l) fun _ _ h => ⟨h.1.sample l, h.2.sample l⟩
  map_zero' := Tensor.ofRaw_eq (Raw.equiv_coeff (fun _ => Equiv.refl _) fun x =>
    (x (Classical.arbitrary S)).elim)
  map_add' x y := Quotient.inductionOn₂ x y fun a b => Tensor.ofRaw_eq (sample_add l a b)

theorem sample_mono : Monotone (sample (S := S) l) :=
  fun x y => Quotient.inductionOn₂ x y fun _ _ h => Restricts.sample l h

theorem sample_table (X : S → Type) [∀ s, Fintype (X s)] (f : (∀ s, X s) → K) :
    sample l (ITensor.table (constants E K) X f) =
      Tensor.ofRaw (Raw.ofTable X fun x => l (f x)) := by
  apply Tensor.ofRaw_eq
  refine Raw.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_
  erw [sample_coeff, Raw.coeff_ofTable, Raw.coeff_ofTable]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-! # Changing coefficients and extending base-field tensors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued

open Spectral
variable {E K S : Type} [Field E] [Field K] [Fintype S]
variable {R : Subring E} {O : Subring K}

theorem Restricts.map {A B : Raw E S} (h : Restricts R A B) (f : E →+* K)
    (hf : ∀ x ∈ R, f x ∈ O) : Restricts O (A.map f) (B.map f) := by
  obtain ⟨P, hp, he⟩ := h
  refine ⟨fun s x y => f (P s x y), fun s x y => hf _ (hp s x y), fun x => ?_⟩
  change ∀ s, B.leg s at x
  change (B.map f).coeff x = ∑ i : A.term, ∏ s, ∑ y, f (P s (x s) y) * f (A.factor i s y)
  rw [Raw.coeff_map, he]
  simp only [map_sum, map_prod, map_mul]

namespace ITensor

def map (f : E →+* K) (hf : ∀ x ∈ R, f x ∈ O) : ITensor R S →+* ITensor O S where
  toFun := Quotient.map (fun A => A.map f) fun _ _ h => ⟨h.1.map f hf, h.2.map f hf⟩
  map_zero' := ofRaw_eq (relabel (Equiv.refl _) (fun _ => Equiv.refl _) fun i => Empty.elim i)
  map_one' := ofRaw_eq (relabel (Equiv.refl _) (fun _ => Equiv.refl _) fun _ _ _ => map_one f)
  map_mul' X Y := by
    refine Quotient.inductionOn₂ X Y fun A B => ?_
    exact ofRaw_eq (relabel (Equiv.refl _) (fun _ => Equiv.refl _) fun _ _ _ => map_mul f _ _)
  map_add' X Y := by
    refine Quotient.inductionOn₂ X Y fun A B => ?_
    refine ofRaw_eq (relabel (Equiv.refl _) (fun _ => Equiv.refl _) ?_)
    rintro (i | i) s (x | x)
    · rfl
    · exact map_zero f
    · exact map_zero f
    · rfl

theorem map_mono (f : E →+* K) (hf : ∀ x ∈ R, f x ∈ O) : Monotone (map (S := S) f hf) :=
  fun X Y => Quotient.inductionOn₂ X Y fun _ _ h => Restricts.map h f hf

def top : Tensor K S →+* ITensor (⊤ : Subring K) S where
  toFun := Quotient.map id fun _ _ h => ⟨top_restricts h.1, top_restricts h.2⟩
  map_zero' := rfl
  map_one' := rfl
  map_add' x y := Quotient.inductionOn₂ x y fun _ _ => rfl
  map_mul' x y := Quotient.inductionOn₂ x y fun _ _ => rfl

theorem top_mono : Monotone (top (K := K) (S := S)) :=
  fun X Y => Quotient.inductionOn₂ X Y fun _ _ h => top_restricts h

variable [Algebra E K]

def fromBase (hO : constants E K ≤ O) : Tensor E S →+* ITensor O S :=
  (map (algebraMap E K) (fun x _ => hO ⟨x, rfl⟩)).comp top

theorem fromBase_mono (hO : constants E K ≤ O) : Monotone (fromBase (S := S) hO) :=
  (map_mono (algebraMap E K) (fun x _ => hO ⟨x, rfl⟩)).comp top_mono

variable [Nonempty S] (l : K →ₗ[E] E)

theorem sample_mul (a : Tensor E S) (b : ITensor (constants E K) S) :
    sample l (fromBase le_rfl a * b) = a * sample l b := by
  refine Quotient.inductionOn₂ a b fun A B => ?_
  apply Tensor.ofRaw_eq
  refine Raw.equiv_coeff (fun _ => Equiv.refl _) fun x => ?_
  erw [sample_coeff, Raw.coeff_mul, Raw.coeff_mul, sample_coeff, Raw.coeff_map,
    ← Algebra.smul_def, map_smul, smul_eq_mul]
  rfl

theorem sample_scalar (c : K) (m : K →ₗ[E] E) (h : ∀ x, l (c * x) = m x)
    (a : ITensor (constants E K) S) : sample l (scalar _ _ c * a) = sample m a := by
  refine Quotient.inductionOn a fun A => ?_
  change sample l (scalar _ _ c * ofRaw A) = sample m (ofRaw A)
  rw [← table_coeff (constants E K) A, ← scalar_table, sample_table, sample_table]
  simp only [Pi.smul_apply, smul_eq_mul, h]

end ITensor
end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-!
# Filtered linear measurements

Take a supremum over any subspace of the base-field dual. The
resulting functional remains additive on block sums. Indeed along
a line through two witnesses, power interpolation shows that all
but finitely many parameters nearly achieve both bounds.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral Filter

variable {E K S : Type} [Field E] [Field K] [Algebra E K] [Fintype S] [Nonempty S]
  (f : Tensor E S →+* ℝ) (hf : Monotone f)
local notation "T" => ITensor (constants E K) S
local notation "D" => (K →ₗ[E] E)

private theorem generic_line (hf : Monotone f) (X : T) (l m : D) {r : ℝ} {c : E}
    (h : r < f (sample (l + c • m) X)) :
    ∀ᶠ a : E in cofinite, r < f (sample (l + a • m) X) := by
  classical
  revert h
  refine Quotient.inductionOn X fun A h => ?_
  let L (a : E) := ITensor.table ⊤ A.leg (fun x => (l + a • m) (A.coeff x))
  have hL : ITensor.Family L 1 := by
    refine ⟨A.leg, inferInstance, fun x => Polynomial.C (l (A.coeff x)) +
      Polynomial.X * Polynomial.C (m (A.coeff x)), ?_, ?_⟩
    · intro x
      refine (Polynomial.natDegree_add_le _ _).trans (max_le (by simp) ?_)
      exact Polynomial.natDegree_mul_le.trans (by simp)
    · intro t
      simp only [L, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, Polynomial.eval_add,
        Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
  let g := f.comp (ITensor.forget ⊤)
  have hg : Monotone g := hf.comp (ITensor.forget_mono _)
  change r < g (L c) at h
  change ∀ᶠ a : E in cofinite, r < g (L a)
  rw [eventually_cofinite]
  by_contra hn
  let _ : Infinite {a : E // ¬ r < g (L a)} := Set.Infinite.to_subtype hn
  exact h.not_ge (hL.bound g hg (fun a : {a : E // ¬ r < g (L a)} => a.val)
    Subtype.val_injective (fun _ => trivial) (fun _ _ => trivial)
    (fun a => le_of_not_gt a.property) c trivial)

theorem sample_bounded (hf : Monotone f) (A : T) : ∃ C : ℝ, ∀ l : D, f (sample l A) ≤ C := by
  refine Quotient.inductionOn A fun A => ?_
  refine ⟨(∏ s, Fintype.card (A.leg s) : ℕ), fun l => ?_⟩
  have h := hf (Tensor.le_dimension (sampleRaw l A))
  rw [map_natCast] at h
  exact h

variable (U : Submodule E (K →ₗ[E] E))

def best (A : T) : ℝ := sSup {r : ℝ | ∃ l : K →ₗ[E] E, l ∈ U ∧ f (sample l A) = r}

theorem best_le (A : T) {r : ℝ} (h : ∀ l ∈ U, f (sample l A) ≤ r) : best f U A ≤ r := by
  refine csSup_le ⟨_, 0, U.zero_mem, rfl⟩ ?_
  rintro _ ⟨l, hl, rfl⟩
  exact h l hl

include hf

theorem le_best (A : T) (l : D) (hl : l ∈ U) : f (sample l A) ≤ best f U A := by
  obtain ⟨C, hC⟩ := sample_bounded f hf A
  refine le_csSup ⟨C, ?_⟩ ⟨l, hl, rfl⟩
  rintro _ ⟨m, _, rfl⟩
  exact hC m

theorem best_nonneg (A : T) : 0 ≤ best f U A := by
  refine le_trans ?_ (le_best f hf U A _ U.zero_mem)
  rw [← map_zero f]
  exact hf (Tensor.zero_le _)

theorem best_mono : Monotone (best f U) := fun _ _ h =>
  best_le f U _ fun l hl => (hf (sample_mono l h)).trans (le_best f hf U _ l hl)

theorem best_zero : best f U 0 = 0 :=
  le_antisymm (best_le f U _ fun _ _ => by simp) (best_nonneg f hf U _)

theorem best_mul (A : Tensor E S) (B : T) :
    best f U (ITensor.fromBase le_rfl A * B) = f A * best f U B := by
  have h : 0 ≤ f A := by simpa using hf (Tensor.zero_le A)
  apply le_antisymm
  · refine best_le f U _ fun l hl => ?_
    rw [ITensor.sample_mul, map_mul]
    exact mul_le_mul_of_nonneg_left (le_best f hf U B l hl) h
  · rcases h.eq_or_lt with he | hp
    · rw [← he, zero_mul]
      exact best_nonneg f hf U _
    rw [mul_comm, ← le_div_iff₀ hp]
    refine best_le f U _ fun l hl => ?_
    rw [le_div_iff₀ hp, mul_comm, ← map_mul, ← ITensor.sample_mul]
    exact le_best f hf U _ l hl

theorem best_add [Infinite E] (A B : T) : best f U (A + B) = best f U A + best f U B := by
  apply le_antisymm
  · refine best_le f U _ fun l hl => ?_
    rw [map_add, map_add]
    exact add_le_add (le_best f hf U A l hl) (le_best f hf U B l hl)
  · apply le_sub_iff_add_le.mp
    refine best_le f U A fun l hl => ?_
    apply le_sub_comm.mp
    refine best_le f U B fun m hm => ?_
    rw [le_sub_iff_add_le']
    refine le_of_forall_pos_le_add fun ε he => ?_
    have ha := generic_line f hf A l (m - l) (c := 0) (r := f (sample l A) - ε / 2)
      (by simp only [zero_smul, add_zero]; linarith)
    have hb := generic_line f hf B l (m - l) (c := 1) (r := f (sample m B) - ε / 2)
      (by simp only [one_smul, add_sub_cancel]; linarith)
    obtain ⟨c, h₁, h₂⟩ := (ha.and hb).exists
    have h₃ := le_best f hf U (A + B) _ (U.add_mem hl (U.smul_mem c (U.sub_mem hm hl)))
    rw [map_add, map_add] at h₃
    linarith

end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-! # Linear forms killing entries above a valuation cutoff -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral

variable {E K S : Type} [Field E] [Field K] [Algebra E K] [Fintype S] [Nonempty S]
    (v : AddValuation K (WithTop ℚ))

def cutoff (E : Type) [Field E] [Algebra E K] (r : ℚ) : Submodule E (K →ₗ[E] E) where
  carrier := {l | ∀ x, (r : WithTop ℚ) < v x → l x = 0}
  zero_mem' := fun _ _ => rfl
  add_mem' hl hm x h := by rw [LinearMap.add_apply, hl x h, hm x h, add_zero]
  smul_mem' a _ hl x h := by rw [LinearMap.smul_apply, hl x h, smul_zero]

def integralRing : Subring K where
  carrier := {x | 0 ≤ v x}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := v.map_le_add
  neg_mem' h := by simpa only [Set.mem_ofPred_eq, v.map_neg] using h
  mul_mem' h g := by simpa only [Set.mem_ofPred_eq, v.map_mul] using add_nonneg h g

private theorem separates (hb : constants E K ≤ integralRing v) :
    ∃ l ∈ cutoff v E 0, l 1 ≠ 0 := by
  let V : Submodule E K :=
    { carrier := {x | 0 < v x}
      zero_mem' := by simp
      add_mem' := v.map_lt_add
      smul_mem' := by
        intro c x hx
        change 0 < v (c • x)
        rw [Algebra.smul_def, v.map_mul]
        exact lt_of_lt_of_le hx (le_add_of_nonneg_left (hb ⟨c, rfl⟩)) }
  have h : (1 : K) ∉ V := by simp [V]
  obtain ⟨l, hl, he⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  refine ⟨l, fun x hx => ?_, hl⟩
  have hv : l x ∈ V.map l := ⟨x, hx, rfl⟩
  simpa only [he, Submodule.mem_bot] using hv

variable (f : Tensor E S →+* ℝ) (hf : Monotone f)
local notation "T" => ITensor (constants E K) S

include hf

theorem best_unit (hb : constants E K ≤ integralRing v) : 0 < best f (cutoff v E 0) 1 := by
  obtain ⟨l, hl, he⟩ := separates v hb
  have h : sample (S := S) l 1 ≠ 0 := by
    intro h
    have ht := (Tensor.ofRaw_eq_zero (sampleRaw l (1 : Raw K S))).mp h (fun _ => ())
    erw [sample_coeff] at ht
    change l (∑ _ : Unit, ∏ _ : S, (1 : K)) = 0 at ht
    simp only [Finset.prod_const_one, Fintype.sum_unique] at ht
    exact he ht
  have hh := hf (Tensor.one_le _ h)
  rw [map_one] at hh
  exact zero_lt_one.trans_le (hh.trans (le_best f hf _ _ _ hl))

theorem best_shift {r s : ℚ} (c : K) (hc : (r : WithTop ℚ) ≤ v c) (A : T) :
    best f (cutoff v E s) (ITensor.scalar _ _ c * A) ≤ best f (cutoff v E (s - r)) A := by
  refine best_le f _ _ fun l hl => ?_
  let m := l.comp (LinearMap.mulLeft E c)
  have hm : m ∈ cutoff v E (s - r) := by
    intro x hx
    apply hl
    have hh := WithTop.add_lt_add_left (WithTop.coe_ne_top (a := r)) hx
    rw [← WithTop.coe_add, add_sub_cancel] at hh
    change (s : WithTop ℚ) < v (c * x)
    rw [v.map_mul]
    exact hh.trans_le (add_le_add_left hc _)
  rw [ITensor.sample_scalar l c m (fun _ => rfl)]
  exact le_best f hf _ _ _ hm

omit hf in
theorem exists_floor (c : K) : ∃ n : ℕ, (↑(-(n : ℚ)) : WithTop ℚ) ≤ v c := by
  rcases eq_or_ne (v c) ⊤ with h | h
  · exact ⟨0, by rw [h]; exact le_top⟩
  obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp h
  obtain ⟨n, hn⟩ := exists_nat_ge (-q)
  exact ⟨n, hq ▸ WithTop.coe_le_coe.mpr (neg_le.mp hn)⟩

theorem best_floor (A : T) : ∃ n : ℕ, ∀ r : ℚ, r < -(n : ℚ) → best f (cutoff v E r) A = 0 := by
  classical
  refine Quotient.inductionOn A fun a => ?_
  choose n hn using fun x => exists_floor v (a.coeff x)
  obtain ⟨N, hN⟩ := (Set.finite_range n).bddAbove
  refine ⟨N, fun r hr => le_antisymm (best_le _ _ _ fun l hl => ?_) (best_nonneg f hf _ _)⟩
  have ht : sample l (ITensor.ofRaw a) = 0 := by
    refine (Tensor.ofRaw_eq_zero _).mpr fun x => ?_
    change (∀ s, a.leg s) at x
    rw [sample_coeff]
    apply hl
    have he : (n x : ℚ) ≤ N := Nat.cast_le.mpr (hN ⟨x, rfl⟩)
    exact (WithTop.coe_lt_coe.mpr (hr.trans_le (neg_le_neg he))).trans_le (hn x)
  change f (sample l (ITensor.ofRaw a)) ≤ 0
  rw [ht, map_zero]

end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-!
# Interpolation of assisted costs

The one-copy envelope is additive. This permits bounding closures
of powers without asking a single extension to minimize at different
interpolation nodes.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Prices.ExtensionData

variable {S T : Type*} [CommSemiring S] [CommSemiring T] [PartialOrder S] [PartialOrder T]
  {pad : S → T} {f : S →+* ℝ} (H : ExtensionData pad f)

include H

theorem aided_nonneg (A : T) : 0 ≤ assisted pad f A := by
  obtain ⟨g, hg, _, he⟩ := (H.assisted_minimum A).1
  rw [← he, ← map_zero g]
  exact hg (H.zero _)

theorem test_iff (A : T) (r : ℝ) : assisted pad f A ≤ r ↔
    ∀ n : ℕ, ∀ s, pad s ≤ A ^ n → f s ≤ r ^ n := by
  obtain ⟨g, hg, he, e⟩ := (H.assisted_minimum A).1
  refine ⟨fun h n s hs => ?_, fun h => ?_⟩
  · rw [← he]
    refine (hg hs).trans ?_
    rw [map_pow, e]
    exact pow_le_pow_left₀ (H.aided_nonneg A) h _
  · obtain ⟨p, hp, ep, hr⟩ := (H.extension_iff (fun _ : Unit => A) (fun _ => r)).mpr
      (by intro w s hs; simpa [List.prod_replicate] using h w.length s (by simpa [List.prod_replicate] using hs))
    exact ((H.assisted_minimum _).2 ⟨p, hp, ep, rfl⟩).trans (hr ())

theorem test_with_loss (A : T) {r C : ℝ} (hr : 0 ≤ r) (hc : 0 < C)
    (h : ∀ n : ℕ, 1 ≤ n → ∀ s, pad s ≤ A ^ n → f s ≤ C * ((n : ℝ) + 1) * r ^ n) :
    assisted pad f A ≤ r := by
  refine (H.test_iff A r).mpr fun n s hs => ?_
  by_cases hn : n = 0
  · subst n
    rw [pow_zero, ← H.padLaw.one] at hs
    simpa using H.mono ((H.padLaw.le_iff _ _).mp hs)
  have hg : 0 ≤ f s := by
    rw [← map_zero f]
    exact H.mono ((H.padLaw.le_iff _ _).mp (H.padLaw.zero.symm ▸ H.zero _))
  have he (m : ℕ) : pad (s ^ m) ≤ (A ^ n) ^ m := by
    induction m with
    | zero => rw [pow_zero, pow_zero, H.padLaw.one]
    | succ m ih =>
      rw [pow_succ, H.padLaw.mul, pow_succ']
      exact (H.mul _ _ _ hs).trans (by rw [mul_comm]; exact H.mul _ _ _ ih)
  refine TensorSpectrum.le_of_pow_le_polynomial_mul_pow (r ^ n) (f s) (C * (n + 1)) 1 (pow_nonneg hr _)
    hg (by positivity) zero_le_one fun m hm => ?_
  have e := h (n * m) (Nat.mul_pos (by omega) hm) _ (by rw [pow_mul]; exact he m)
  rw [map_pow, pow_mul, Nat.cast_mul] at e
  rw [Real.rpow_one, mul_assoc C]
  refine e.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ hc.le) (by positivity))
  linarith

end OAI.LinearAlgebra.MatrixExponent.Prices.ExtensionData

namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Prices

variable {K S U : Type} [Field K] [Fintype S] [Nonempty S] [Fintype U] {O : Subring K}
  {A : K → ITensor O (S ⊕ U)} {d : ℕ} (h : Family A d)
  (f : ITensor O S →+* ℝ) (hf : Monotone f)

theorem Family.test_nodes (h : Family A d) (f : ITensor O S →+* ℝ) (hf : Monotone f)
    (n : ℕ) (x : K) {s : ITensor O S} (hs : pad U s ≤ A x ^ n)
    {I : Type*} [Fintype I] [DecidableEq I]
    (v : I → K) (hi : Function.Injective v) (hd : n * d < Fintype.card I) :
    f s ≤ ∑ i, f (scalar O S ((Lagrange.basis Finset.univ v i).eval x)) *
      assisted (pad U) f (A (v i)) ^ n := by
  let H := extensionData (U := U) f hf
  obtain ⟨M, h1, hm, he, hc⟩ := H.padLaw.envelope H.add H.mul H.zero H.upper f hf
  have ep (s : ITensor O S) : f s = M (pad U s) := by
    simpa only [mul_one, h1] using (he s 1).symm
  have ht := hm ((h.pow n).weighted hd v hi x)
  rw [map_sum] at ht
  refine ((ep s).trans_le ((hm hs).trans ht)).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [← pad_scalar, he]
  refine mul_le_mul_of_nonneg_left ((hc _ _).mpr ?_) (by rw [← map_zero f]; exact hf (zero_le _))
  exact (H.test_iff _ _).mp le_rfl n

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-! Interpolation nodes on the arms of a valuation star. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.Star

open Prices.Motion Prices.Motion.K0 Finset
open scoped Classical
variable {E : Type} [Field E] {n : ℕ}

abbrev Arm (n : ℕ) := Option (Fin n)

structure Data (E : Type) [Field E] (n : ℕ) where
  c : Fin n → K0 E
  hc : ∀ j, 0 ≤ val E (c j)
  hd : ∀ i j, i ≠ j → val E (c i - c j) = 0
  r : Arm n → ℚ
  hr : ∀ j, 0 < r j
  u : ℕ ↪ E
  hu : ∀ i, u i ≠ 0

variable (D : Data E n) {m : Arm n → ℕ}

abbrev Index (m : Arm n → ℕ) := Σ a, Fin (m a)

def node (i : Index m) := armEnd D.c D.r (C (D.u i.2.val)) i.1

def shift (d : Arm n) : ℚ := d.elim (-D.r none) (fun _ => 0)

def sep : Arm n → Arm n → ℚ
  | some i, some j => if i = j then D.r (some i) else 0
  | _, _ => -D.r none

private theorem scaled (s : ℚ) {a : E} (h : a ≠ 0) : val E (t s * C a) = ↑s := by
  rw [AddValuation.map_mul, val_C h, val_t, add_zero]

private theorem positive (j : Fin n) (k : ℕ) : 0 < val E (t (D.r (some j)) * C (D.u k)) := by
  rw [scaled _ (D.hu _)]
  exact WithTop.coe_pos.mpr (D.hr _)

private theorem integral (j : Fin n) (k : ℕ) :
    0 ≤ val E (D.c j + t (D.r (some j)) * C (D.u k)) :=
  (le_min (D.hc _) (positive D j k).le).trans ((val E).map_add _ _)

private theorem outer (k : ℕ) (x : K0 E) (hx : 0 ≤ val E x) :
    val E (t (-D.r none) * C (D.u k) - x) = ↑(-D.r none) := by
  have h : val E (t (-D.r none) * C (D.u k)) < val E (-x) := by
    rw [scaled _ (D.hu _), AddValuation.map_neg]
    exact (WithTop.coe_lt_coe.mpr (neg_neg_of_pos (D.hr none))).trans_le hx
  rw [sub_eq_add_neg, AddValuation.map_add_of_distinct_val _ h.ne, min_eq_left h.le, scaled _ (D.hu _)]

theorem distance (i j : Index m) (h : i ≠ j) :
    val E (node D i - node D j) = ↑(sep D i.1 j.1) := by
  have same (a : Arm n) (i j : Fin (m a)) (h : (⟨a, i⟩ : Index m) ≠ ⟨a, j⟩) (r : ℚ) :
      val E (t r * C (D.u i.val) - t r * C (D.u j.val)) = ↑r := by
    have hn : D.u i.val ≠ D.u j.val := fun e =>
      h (congrArg (Sigma.mk a) (Fin.ext (D.u.injective e)))
    rw [← mul_sub, ← map_sub, scaled r (sub_ne_zero.mpr hn)]
  obtain ⟨_ | a, i⟩ := i <;> obtain ⟨_ | b, j⟩ := j
  · exact same none i j h _
  · exact outer D _ _ (integral D _ _)
  · rw [AddValuation.map_sub_swap]
    exact outer D _ _ (integral D _ _)
  · simp only [node, armEnd, sep]
    by_cases he : a = b
    · subst b
      rw [ite_eq_left rfl, add_sub_add_left_eq_sub]
      exact same _ i j h _
    rw [ite_eq_right he]
    let x := t (D.r (some a)) * C (D.u i.val)
    let y := t (D.r (some b)) * C (D.u j.val)
    have hh : val E (D.c a - D.c b) < val E (x - y) := by
      rw [D.hd a b he]
      exact (lt_min (positive D _ _) (positive D _ _)).trans_le ((val E).map_sub _ _)
    change val E (D.c a + x - (D.c b + y)) = 0
    rw [show D.c a + x - (D.c b + y) = (D.c a - D.c b) + (x - y) by ring,
      AddValuation.map_add_of_distinct_val _ hh.ne, min_eq_left hh.le, D.hd a b he]

theorem injective : Function.Injective (node D (m := m)) := by
  intro i j e
  by_contra h
  have hb := distance D i j h
  simp [e] at hb

private theorem node_bound (i : Index m) {x : K0 E} (hx : 0 ≤ val E x) :
    ↑(shift D i.1) ≤ val E (x - node D i) := by
  obtain ⟨_ | a, i⟩ := i
  · rw [AddValuation.map_sub_swap]
    exact (outer D _ _ hx).ge
  · exact (le_min hx (integral D _ _)).trans ((val E).map_sub _ _)

theorem lagrange_bound (i : Index m) {x : K0 E} (hx : 0 ≤ val E x) :
    ↑(∑ j ∈ univ.erase i, (shift D j.1 - sep D i.1 j.1)) ≤
      val E ((Lagrange.basis univ (node D) i).eval x) := by
  let f (j : Index m) := (Lagrange.basisDivisor (node D i) (node D j)).eval x
  let g (j : Index m) := shift D j.1 - sep D i.1 j.1
  have h (j : Index m) (hj : j ≠ i) : ↑(g j) ≤ val E (f j) := by
    simp only [f, Lagrange.basisDivisor, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub,
      Polynomial.eval_X, AddValuation.map_mul, AddValuation.map_inv, distance D i j hj.symm]
    rw [show g j = -sep D i.1 j.1 + shift D j.1 by unfold g; ring, WithTop.coe_add]
    exact add_le_add le_rfl (node_bound D j hx)
  have H (s : Finset (Index m)) (hs : i ∉ s) : ↑(∑ j ∈ s, g j) ≤ val E (∏ j ∈ s, f j) := by
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s hj ih =>
      rw [sum_insert hj, prod_insert hj, AddValuation.map_mul, WithTop.coe_add]
      exact add_le_add (h j (fun he => hs (he ▸ mem_insert_self _ _)))
        (ih (fun he => hs (mem_insert_of_mem he)))
  rw [Lagrange.basis, Polynomial.eval_prod]
  exact H _ (notMem_erase _ _)

end OAI.LinearAlgebra.MatrixExponent.Valued.Star
end

/-!
# Choosing the numbers of interpolation nodes

An inner arm contributes only when its end rate is below the mean.
Its nodes absorb that difference. Their combined multiplicity supplies
the required vanishing order for the outer arm.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.Star

open Finset
open scoped Classical
variable {E : Type} [Field E] {n : ℕ} (D : Data E n)

def credit {m : Arm n → ℕ} (i : Index m) := ∑ j ∈ univ.erase i, (shift D j.1 - sep D i.1 j.1)

private theorem credit_none (m : Arm n → ℕ) (i : Fin (m none)) :
    credit D ⟨none, i⟩ = (∑ j, (m (some j) : ℚ)) * D.r none := by
  unfold credit
  rw [sum_erase_eq_sub (mem_univ _), Fintype.sum_sigma, Fintype.sum_option]
  simp [shift, sep, sum_mul]

private theorem credit_some (m : Arm n → ℕ) (j : Fin n) (i : Fin (m (some j))) :
    credit D ⟨some j, i⟩ = (1 - (m (some j) : ℚ)) * D.r (some j) := by
  unfold credit
  rw [sum_erase_eq_sub (mem_univ _), Fintype.sum_sigma, Fintype.sum_option]
  simp [shift, sep]
  ring

variable (R : Arm n → ℝ) (μ : ℝ) (d N : ℕ)

def weight (j : Arm n) := (μ - R j) / (D.r j : ℝ)

def size : Arm n → ℕ
  | none => N * d + 1
  | some j => ⌈(N : ℝ) * weight D R μ (some j)⌉₊

theorem sufficient : N * d < Fintype.card (Index (size D R μ d N)) := by
  simp only [Index, Fintype.card_sigma, Fintype.card_fin, Fintype.sum_option]
  rw [show size D R μ d N none = N * d + 1 from rfl]
  omega

theorem linear_size : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
    (Fintype.card (Index (size D R μ d N)) : ℝ) ≤ C * (N + 1) := by
  let c (j : Fin n) := ⌈weight D R μ (some j)⌉₊
  refine ⟨(d + 1 + ∑ j, c j : ℕ), by positivity, fun N => ?_⟩
  have hs (j : Fin n) : size D R μ d N (some j) ≤ N * c j := by
    apply Nat.ceil_le.mpr
    rw [Nat.cast_mul]
    exact mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _)
  have h := sum_le_sum (s := univ) (fun j _ => hs j)
  rw [← mul_sum] at h
  have hh : Fintype.card (Index (size D R μ d N)) ≤ (d + 1+∑ j, c j) * (N + 1) := by
    simp only [Index, Fintype.card_sigma, Fintype.card_fin, Fintype.sum_option]
    rw [show size D R μ d N none = N * d + 1 from rfl]
    nlinarith only [h, Nat.zero_le (∑ j, c j)]
  exact_mod_cast hh

theorem credit_bound (hμ : 0 ≤ ∑ j, weight D R μ j) (i : Index (size D R μ d N)) :
    (N : ℝ) * (R i.1 - μ) ≤ credit D i := by
  let m := size D R μ d N
  have hr (j) : (0 : ℝ) < D.r j := Rat.cast_pos.mpr (D.hr j)
  obtain ⟨_ | j, i⟩ := i
  · rw [credit_none]
    have hm (j : Fin n) : (N : ℝ) * weight D R μ (some j) ≤ m (some j) := Nat.le_ceil _
    have hsum := sum_le_sum (s := univ) (fun j _ => hm j)
    rw [← mul_sum] at hsum
    rw [Fintype.sum_option] at hμ
    have h : (N : ℝ) * (-weight D R μ none) ≤ ∑ j, (m (some j) : ℝ) :=
      (mul_le_mul_of_nonneg_left (by linarith only [hμ]) (Nat.cast_nonneg _)).trans hsum
    simp only [weight, ← neg_div, neg_sub, ← mul_div_assoc, div_le_iff₀ (hr _)] at h
    simpa only [Rat.cast_mul, Rat.cast_sum, Rat.cast_natCast] using h
  · rw [credit_some]
    have hm : 0 < m (some j) := Nat.zero_lt_of_lt i.isLt
    have hx := Nat.ceil_lt_add_one (Nat.ceil_pos.mp hm).le
    change (m (some j) : ℝ) < (N : ℝ) * ((μ - R (some j)) / (D.r (some j) : ℝ)) + 1 at hx
    rw [← mul_div_assoc, ← sub_lt_iff_lt_add, lt_div_iff₀ (hr _)] at hx
    simp only [Rat.cast_mul, Rat.cast_sub, Rat.cast_one, Rat.cast_natCast]
    linarith only [hx]

end OAI.LinearAlgebra.MatrixExponent.Valued.Star
end
