import OAI.LinearAlgebra.MatrixExponent.Spectral.Semiring
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rank
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Jacobson.Ring
import OAI.LinearAlgebra.MatrixExponent.Spectrum.Extension
import OAI.LinearAlgebra.MatrixExponent.Spectral.Place
import OAI.LinearAlgebra.MatrixExponent.Spectral.Transport

/-!
# Extending the coefficient field

A field homomorphism acts entrywise on both tensor factors and local
restriction matrices. It therefore induces a monotone semiring homomorphism.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral

variable {K L S : Type} [Field K] [Field L] [Fintype S]

namespace Raw

def map (A : Raw K S) (f : K →+* L) : Raw L S :=
  ⟨A.leg, A.term, fun i s x => f (A.factor i s x)⟩

@[simp] theorem coeff_map (A : Raw K S) (f : K →+* L) (x : ∀ s, A.leg s) :
    (A.map f).coeff x = f (A.coeff x) := by
  change (∑ i : A.term, ∏ s, f (A.factor i s (x s))) = _
  simp only [coeff, map_sum, map_prod]

theorem Restricts.map {A B : Raw K S} (h : A.Restricts B) (f : K →+* L) :
    (A.map f).Restricts (B.map f) := by
  obtain ⟨P, hP⟩ := h
  refine ⟨fun s x y => f (P s x y), fun x => ?_⟩
  change ∀ s, B.leg s at x
  change (B.map f).coeff x = ∑ i : A.term, ∏ s, ∑ y, f (P s (x s) y) * f (A.factor i s y)
  rw [coeff_map, hP]
  simp only [map_sum, map_prod, map_mul]

end Raw

namespace Tensor

def map (f : K →+* L) : Tensor K S →+* Tensor L S where
  toFun := Quotient.map (fun A => A.map f) fun _ _ h => ⟨h.1.map f, h.2.map f⟩
  map_zero' := by
    refine ofRaw_eq (Raw.relabel (Equiv.refl _) (fun _ => Equiv.refl _) ?_)
    exact fun i => Empty.elim i
  map_one' := by
    refine ofRaw_eq (Raw.relabel (Equiv.refl _) (fun _ => Equiv.refl _) ?_)
    exact fun _ _ _ => map_one f
  map_mul' X Y := by
    refine Quotient.inductionOn₂ X Y fun A B => ?_
    refine ofRaw_eq (Raw.relabel (Equiv.refl _) (fun _ => Equiv.refl _) ?_)
    exact fun _ _ _ => map_mul f _ _
  map_add' X Y := by
    refine Quotient.inductionOn₂ X Y fun A B => ?_
    refine ofRaw_eq (Raw.relabel (Equiv.refl _) (fun _ => Equiv.refl _) ?_)
    rintro (i | i) s (x | x)
    · rfl
    · exact map_zero f
    · exact map_zero f
    · rfl

@[simp] theorem map_ofRaw (f : K →+* L) (A : Raw K S) :
    map f (ofRaw A) = ofRaw (A.map f) := rfl

theorem map_mono (f : K →+* L) : Monotone (map (S := S) f) :=
  fun X Y => Quotient.inductionOn₂ X Y fun _ _ h => Raw.Restricts.map h f

end Tensor
end OAI.LinearAlgebra.MatrixExponent.Spectral
end

/-!
# Descent of restriction along a finite field extension

One extra diagonal label records one basis index at every site. Its
dimension depends on the field and the sites, and stays fixed even as
the local dimensions grow under tensor powers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K L S : Type} [Field K] [Field L] [Algebra K L] [Fintype S]

private theorem project_prod [DecidableEq S] {d : ℕ} (b : Module.Basis (Fin d) K L)
    (π : L →ₗ[K] K) (v : S → L) :
    π (∏ s, v s) = ∑ j : S → Fin d, (∏ s, b.repr (v s) (j s)) * π (∏ s, b (j s)) := by
  have e : (∏ s, v s) = ∏ s, ∑ i, b.repr (v s) i • b i :=
    Finset.prod_congr rfl fun s _ => (b.sum_repr _).symm
  rw [e, Fintype.prod_sum, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Algebra.smul_def, Finset.prod_mul_distrib, ← map_prod]
  rw [← Algebra.smul_def, map_smul, smul_eq_mul]

private theorem repr_sum {d : ℕ} (b : Module.Basis (Fin d) K L) (j : Fin d)
    {X : Type} [Fintype X] (u : X → L) (v : X → K) :
    b.repr (∑ y, u y * algebraMap K L (v y)) j = ∑ y, b.repr (u y) j * v y := by
  rw [map_sum, Finsupp.finsetSum_apply]
  refine Finset.sum_congr rfl fun y _ => ?_
  rw [mul_comm, ← Algebra.smul_def, map_smul, Finsupp.smul_apply, smul_eq_mul, mul_comm]

open Classical in
theorem descend [Nonempty S] [Module.Finite K L] {A B : Raw K S}
    (h : (A.map (algebraMap K L)).Restricts (B.map (algebraMap K L))) :
    (diag K S (S → Fin (Module.finrank K L)) * A).Restricts B := by
  classical
  obtain ⟨P, hP⟩ := h
  change (s : S) → B.leg s → A.leg s → L at P
  obtain ⟨π, hπ⟩ := Module.Projective.exists_dual_eq_one K (one_ne_zero : (1 : L) ≠ 0)
  have hbase (c : K) : π (algebraMap K L c) = c := by
    rw [Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one]
  let b := Module.finBasis K L
  let J := S → Fin (Module.finrank K L)
  let w (j : J) (s : S) := if s = Classical.arbitrary S then π (∏ a, b (j a)) else 1
  let Q (s : S) (x : B.leg s) (z : J × A.leg s) :=
    b.repr (P s x z.2) (z.1 s) * w z.1 s
  have localSum (i : A.term) (j : J) (s : S) (x : B.leg s) :
      (∑ z : J × A.leg s, Q s x z * ((if z.1 = j then 1 else 0) * A.factor i s z.2)) =
      b.repr (∑ y, P s x y * algebraMap K L (A.factor i s y)) (j s) * w j s := by
    rw [repr_sum, Finset.sum_mul, Fintype.sum_prod_type, Finset.sum_comm]
    simp [Q, J, mul_ite, ite_mul, mul_right_comm]
  refine ⟨Q, fun x => ?_⟩
  have hh : algebraMap K L (B.coeff x) =
      ∑ i : A.term, ∏ s, ∑ y : A.leg s, P s (x s) y * algebraMap K L (A.factor i s y) :=
    (B.coeff_map _ x).symm.trans (hP x)
  rw [← hbase (B.coeff x), hh, map_sum]
  change _ = ∑ t : J × A.term, ∏ s, ∑ z : J × A.leg s, Q s (x s) z *
    ((if z.1 = t.1 then 1 else 0) * A.factor t.2 s z.2)
  rw [Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [project_prod b π]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [localSum, Finset.prod_mul_distrib]
  simp [w]

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end

section
/-!
# Specializing a tensor restriction

The equations in the local matrix entries have coefficients in the base
field. A maximal ideal containing the kernel of evaluation preserves all
the equations simultaneously. Its residue field is a finite extension by
Zariski's lemma.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K L S : Type} [Field K] [Field L] [Algebra K L] [Fintype S]

theorem specialize {A B : Raw K S}
    (h : (A.map (algebraMap K L)).Restricts (B.map (algebraMap K L))) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra K E) (_ : Module.Finite K E),
      (A.map (algebraMap K E)).Restricts (B.map (algebraMap K E)) := by
  classical
  obtain ⟨M, hM⟩ := h
  change (s : S) → B.leg s → A.leg s → L at M
  let R := MvPolynomial (Σ s, B.leg s × A.leg s) K
  let X (s : S) (x : B.leg s) (y : A.leg s) : R := MvPolynomial.X ⟨s, x, y⟩
  let f : R →ₐ[K] L := MvPolynomial.aeval (fun t => M t.1 t.2.1 t.2.2)
  obtain ⟨m, hm, hker⟩ := Ideal.exists_le_maximal (RingHom.ker f.toRingHom)
    (RingHom.ker_ne_top f.toRingHom)
  let : Field (R ⧸ m) := Ideal.Quotient.field m
  let g := Ideal.Quotient.mkₐ K m
  refine ⟨R ⧸ m, inferInstance, inferInstance, finite_of_finite_type_of_isJacobsonRing K _,
    fun s x y => g (X s x y), fun x => ?_⟩
  let t : R := ∑ i : B.term, ∏ s, algebraMap K R (B.factor i s (x s))
  let d : R := ∑ i : A.term, ∏ s, ∑ y : A.leg s, X s (x s) y * algebraMap K R (A.factor i s y)
  have hf : f t = f d := by
    simp only [t, d, map_sum, map_prod, map_mul, AlgHom.commutes]
    simp only [f, X, R, MvPolynomial.aeval_X]
    exact hM x
  have hg : g t = g d := Ideal.Quotient.eq.mpr (hker (by
    change f (t - d) = 0
    rw [map_sub, hf, sub_self]))
  simp only [t, d, map_sum, map_prod, map_mul, AlgHom.commutes] at hg
  exact hg

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end

/-!
# Extension of spectral points under extension of scalars

One restriction specializes to a single finite extension. All powers
then descend with the same overhead, so every spectral point respects
the new comparison. Compact spectral extension yields agreement on
every tensor over the base field simultaneously.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
open scoped NNReal

variable {K S : Type} [Field K] [Fintype S]

theorem powers_le {A B : Tensor K S} (h : A ≤ B) (r : ℕ) : A ^ r ≤ B ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [pow_succ, pow_succ']
    exact (mul_le_mul_left A B _ h).trans (by
      rw [mul_comm]
      exact mul_le_mul_left _ _ B ih)

variable [Nonempty S] {L : Type} [Field L] [Algebra K L]

private theorem finite_descent [Module.Finite K L] (A B : Tensor K S)
    (h : map (algebraMap K L) A ≤ map (algebraMap K L) B) :
    A ≤ ((Module.finrank K L ^ Fintype.card S : ℕ) : Tensor K S) * B := by
  classical
  revert h
  refine Quotient.inductionOn₂ A B fun a b hab => ?_
  have hd : ofRaw a ≤ ofRaw (Raw.diag K S (S → Fin (Module.finrank K L)) * b) :=
    Raw.descend hab
  rw [ofRaw_mul, diag_eq_natCast, Fintype.card_fun, Fintype.card_fin] at hd
  exact hd

theorem descent_powers (A B : Tensor K S)
    (h : map (algebraMap K L) A ≤ map (algebraMap K L) B) :
    ∃ C : ℕ, ∀ r : ℕ, A ^ r ≤ (C : Tensor K S) * B ^ r := by
  revert h
  refine Quotient.inductionOn₂ A B fun a b hab => ?_
  obtain ⟨E, _, _, _, hE⟩ := Raw.specialize (L := L) (A := b) (B := a) hab
  have he : map (algebraMap K E) (ofRaw a) ≤ map (algebraMap K E) (ofRaw b) := hE
  refine ⟨Module.finrank K E ^ Fintype.card S, fun r => finite_descent (L := E) (ofRaw a ^ r) (ofRaw b ^ r) ?_⟩
  rw [map_pow, map_pow]
  exact powers_le he r

theorem extend_field (L : Type) [Field L] [Algebra K L]
    (f : Tensor K S →+* ℝ≥0) (hf : Monotone f) :
    ∃ g : Tensor L S →+* ℝ≥0, Monotone g ∧ ∀ A, g (map (algebraMap K L) A) = f A := by
  apply Spectrum.extension add_le_add_right mul_le_mul_left zero_le one_le exists_bound
  intro A B h
  obtain ⟨C, hc⟩ := descent_powers A B h
  apply Spectrum.le_of_powers_le (C := C)
  intro r
  rw [← map_pow, ← map_pow, ← map_natCast f, ← map_mul f]
  exact hf (hc r)

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-!
# Moving a single leg along a wire

The old and new sites both pin the wire label to the corresponding
leg coordinate. For each target assignment there is exactly one
source assignment satisfying these local conditions and the wire.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K S T : Type} [Field K] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

private theorem shared_on {U : Finset S} (hU : U.Nonempty) {n : ℕ} (i : Fin n) :
    (shared K U n).coeff (fun s => port U s i) = 1 := by
  change (∑ j : Fin n, ∏ s, if port U s i = port U s j then (1 : K) else 0) = 1
  rw [Fintype.sum_eq_single i]
  · simp
  · intro j hj
    obtain ⟨s, hs⟩ := hU
    exact Finset.prod_eq_zero (Finset.mem_univ s) (by simp [port, hs, hj.symm])

private theorem shared_support {U : Finset S} {n : ℕ} (x : S → Fin n)
    (h : (shared K U n).coeff x ≠ 0) : ∃ i, ∀ s, x s = port U s i := by
  change (∑ i : Fin n, ∏ s, if x s = port U s i then (1 : K) else 0) ≠ 0 at h
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  exact ⟨i, fun s => by
    by_contra he
    exact hi (Finset.prod_eq_zero (Finset.mem_univ s) (ite_eq_right he))⟩

theorem integral_move {O : Subring K} (A : Raw K T) (f g : T → S) (t : T) (h : ∀ u, u ≠ t → f u = g u) :
    Valued.Restricts O (A.group f * wire K (f t) (g t) (Fintype.card (A.leg t))) (A.group g) := by
  classical
  let e := Fintype.equivFin (A.leg t)
  let U : Finset S := {f t, g t}
  let W := shared K U (Fintype.card (A.leg t))
  let C := A.group f * W
  let ok (s : S) (x : (A.group g).leg s) (y : C.leg s) :=
    (∀ u (hf : f u = s) (hg : g u = s), y.1 ⟨u, hf⟩ = x ⟨u, hg⟩) ∧
    (∀ hf : f t = s, e (y.1 ⟨t, hf⟩) = y.2) ∧
    (∀ hg : g t = s, e (x ⟨t, hg⟩) = y.2)
  change Valued.Restricts O C (A.group g)
  refine (Valued.restricts_iff _ _).mpr ⟨fun s x y => if ok s x y then 1 else 0,
    fun s x y => by by_cases h : ok s x y <;> simp [h], fun x => ?_⟩
  let v (u : T) := x (g u) ⟨u, rfl⟩
  have hv u s (hg : g u = s) : x s ⟨u, hg⟩ = v u := by subst s; rfl
  let z := e (v t)
  let y₀ (s : S) : C.leg s := (fun u => v u, port U s z)
  have ho (s : S) : ok s (x s) (y₀ s) := by
    refine ⟨fun u hf hg => (hv u s hg).symm, ?_, ?_⟩
    · rintro rfl
      simp [y₀, port, U, z]
    · rintro rfl
      simp [y₀, port, U, z, v]
  rw [Fintype.sum_eq_single y₀]
  · simp only [ho, ↓reduceIte, Finset.prod_const_one, one_mul]
    change (A.group g).coeff x = (A.group f * W).coeff y₀
    rw [coeff_mul, coeff_group, coeff_group]
    change A.coeff v = A.coeff v * (shared K U _).coeff (fun s => port U s z)
    rw [shared_on (by simp [U]), mul_one]
  · intro y hy
    by_cases he : ∀ s, ok s (x s) (y s)
    swap
    · obtain ⟨s, hs⟩ := not_forall.mp he
      exact mul_eq_zero_of_left (Finset.prod_eq_zero (Finset.mem_univ s) (ite_eq_right hs)) _
    by_cases hw : W.coeff (fun s => (y s).2) = 0
    · simp only [C, coeff_mul, hw, mul_zero]
    obtain ⟨i, hi⟩ := shared_support (fun s => (y s).2) hw
    have hin (s : S) (hs : s ∈ U) : (y s).2 = i := (hi s).trans (ite_eq_left hs)
    have hiz : i = z := (hin (g t) (by simp [U])).symm.trans ((he (g t)).2.2 rfl).symm
    subst i
    exfalso
    apply hy
    funext s
    refine Prod.ext ?_ (hi s)
    funext u
    rcases u with ⟨u, hu⟩
    by_cases hut : u = t
    · subst u
      exact e.injective (((he s).2.1 hu).trans (hin s (by simp [U, hu])))
    · have hg : g u = s := (h u hut).symm.trans hu
      exact ((he s).1 u hu hg).trans (hv u s hg)

theorem move (A : Raw K T) (f g : T → S) (t : T) (h : ∀ u, u ≠ t → f u = g u) :
    (A.group f * wire K (f t) (g t) (Fintype.card (A.leg t))).Restricts (A.group g) :=
  (integral_move (O := ⊤) A f g t h).forget

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end

/-!
# Transporting a tensor between placements
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S T : Type} [Field K] [Fintype S] [Fintype T] [DecidableEq S] [DecidableEq T]

omit [Fintype S] [DecidableEq S] in
/-- Iterate a transport bound proved for one leg at a time. -/
theorem move_all {M : Type*} [CommMonoid M] [Preorder M]
    (V : (T → S) → M) (W : T → S → S → M)
    (hmul : ∀ a b c : M, a ≤ b → c * a ≤ c * b)
    (move : ∀ (f g : T → S) (t : T), (∀ u, u ≠ t → f u = g u) →
      V g ≤ V f * W t (f t) (g t)) (f g : T → S) :
    V g ≤ V f * ∏ t, W t (f t) (g t) := by
  let mix (U : Finset T) (t : T) := if t ∈ U then g t else f t
  have step (U : Finset T) : V (mix U) ≤ V f * ∏ t ∈ U, W t (f t) (g t) := by
    induction U using Finset.induction_on with
    | empty => simp [mix]
    | @insert t U ht ih =>
      have hm := move (mix U) (mix (insert t U)) t (by intro u hu; simp [mix, hu])
      have hfg : mix U t = f t := ite_eq_right ht
      have hgg : mix (insert t U) t = g t := ite_eq_left (Finset.mem_insert_self _ _)
      rw [hfg, hgg, mul_comm] at hm
      rw [Finset.prod_insert ht, mul_left_comm]
      exact hm.trans (hmul _ _ _ ih)
  simpa [mix] using step Finset.univ

theorem transport (A : Raw K T) (f g : T → S) :
    place g (ofRaw A) ≤ place f (ofRaw A) * ∏ t, wire K (f t) (g t) (Fintype.card (A.leg t)) :=
  move_all (fun f => place f (ofRaw A)) (fun t i j => wire K i j (Fintype.card (A.leg t)))
    mul_le_mul_left (Raw.move A) f g

variable [Nonempty T] (p : Tensor K S →+* ℝ) (hp : Monotone p)
include hp

theorem price_place_pos (f : T → S) {A : Tensor K T} (h : A ≠ 0) :
    0 < p (place f A) := by
  have e := hp (place_mono f (one_le A h))
  rw [place_one, map_one] at e
  exact zero_lt_one.trans_le e

omit [Nonempty T] [DecidableEq T] in
/-- Convert multiplicative wire bounds into an additive estimate on logs. -/
theorem log_transport (V : (T → S) → ℝ) (n : T → ℕ)
    (pos : ∀ f, 0 < V f) (dim : ∀ t, 0 < n t)
    (h : ∀ f g, V g ≤ V f * ∏ t, p (wire K (f t) (g t) (n t))) (f g : T → S) :
    |Real.log (V f) - Real.log (V g)| ≤ ∑ t, dist p (f t) (g t) * Real.log (n t) := by
  have bound (f g : T → S) :
      Real.log (V g) - Real.log (V f) ≤
        ∑ t, dist p (f t) (g t) * Real.log (n t) := by
    have hg := pos g
    have hf := pos f
    have hW (t : T) : 0 < p (wire K (f t) (g t) (n t)) := by
      rw [price_wire p hp _ _ (dim t)]
      exact Real.rpow_pos_of_pos (Nat.cast_pos.mpr (dim t)) _
    have he := Real.log_le_log hg (h f g)
    rw [Real.log_mul hf.ne' (Finset.prod_pos fun t _ => hW t).ne',
      Real.log_prod (fun t _ => (hW t).ne')] at he
    apply sub_le_iff_le_add'.mpr
    refine he.trans_eq (congrArg _ (Finset.sum_congr rfl fun t _ => ?_))
    rw [price_wire p hp _ _ (dim t), Real.log_rpow (Nat.cast_pos.mpr (dim t))]
  refine abs_sub_le_iff.mpr ⟨?_, bound f g⟩
  simpa only [dist_comm p (g _) (f _)] using bound g f

theorem price_transport (A : Raw K T) (h : ofRaw A ≠ 0) (f g : T → S) :
    |Real.log (p (place f (ofRaw A))) - Real.log (p (place g (ofRaw A)))| ≤
      ∑ t, dist p (f t) (g t) * Real.log (Fintype.card (A.leg t)) := by
  have dim (t : T) : 0 < Fintype.card (A.leg t) := by
    obtain ⟨x, _⟩ := not_forall.mp (fun he => h ((ofRaw_eq_zero A).mpr he))
    exact Fintype.card_pos_iff.mpr ⟨x t⟩
  refine log_transport p hp (fun v => p (place v (ofRaw A))) _ (fun v => price_place_pos p hp v h)
    dim ?_ f g
  intro v w
  have H := hp (transport A v w)
  rwa [p.map_mul, map_prod] at H

theorem price_place_eq (f g : T → S) (h : ∀ t, dist p (f t) (g t) = 0) (A : Tensor K T) :
    p (place f A) = p (place g A) := by
  refine Quotient.inductionOn A fun a => ?_
  change p (place f (ofRaw a)) = p (place g (ofRaw a))
  by_cases hz : ofRaw a = 0
  · simp only [hz, place_zero]
  have he := price_transport p hp a hz f g
  simp only [h, zero_mul, Finset.sum_const_zero, abs_nonpos_iff, sub_eq_zero] at he
  exact Real.log_injOn_pos (price_place_pos p hp f hz) (price_place_pos p hp g hz) he

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end
