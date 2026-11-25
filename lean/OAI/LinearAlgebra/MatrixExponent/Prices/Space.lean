import OAI.LinearAlgebra.MatrixExponent.Spectral.Transport
import OAI.LinearAlgebra.MatrixExponent.Spectrum.Comparison
import OAI.LinearAlgebra.MatrixExponent.Spectral.Place
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryTerms
import OAI.LinearAlgebra.MatrixExponent.Prices.Tensor

/-!
# Compactness of ordinary prices of bounded scale

We use base-two logarithms. A zero input is assigned a dummy value
of zero, common to every price. It therefore gives no information
in equality or continuity tests.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
open Set
open scoped NNReal

variable {K S : Type} [Field K] [Fintype S]

def values (d : ℝ) (f : Tensor K S →+* ℝ) (A : Tensor K S) : ℝ :=
  d * (Real.log (f A) / Real.log 2)

variable (K S) in
def ordinary (D : ℝ) : Set (Tensor K S → ℝ) :=
  {P | ∃ d ∈ Icc 0 D, ∃ f : Tensor K S →+* ℝ, Monotone f ∧ P = values d f}

variable [Nonempty S]

theorem value_one_le {f : Tensor K S →+* ℝ} (hf : Monotone f) {A : Tensor K S}
    (h : A ≠ 0) : 1 ≤ f A := by
  simpa using hf (one_le A h)

theorem values_nonneg {d : ℝ} (hd : 0 ≤ d) {f : Tensor K S →+* ℝ} (hf : Monotone f)
    (A : Tensor K S) : 0 ≤ values d f A := by
  by_cases h : A = 0
  · simp [values, h]
  exact mul_nonneg hd (div_nonneg (Real.log_nonneg (value_one_le hf h)) (Real.log_nonneg (by norm_num)))

theorem compact_ordinary (D : ℝ) : IsCompact (ordinary K S D) := by
  let T := Tensor K S
  let v (x : ℝ × (T → ℝ≥0)) (a : T) := x.1 * (Real.log (max 1 (x.2 a : ℝ)) / Real.log 2)
  have hv : Continuous v := by
    apply continuous_pi
    intro a
    have h : Continuous (fun x : ℝ × (T → ℝ≥0) => max 1 (x.2 a : ℝ)) := by fun_prop
    exact continuous_fst.mul ((h.log (fun x => (zero_lt_one.trans_le (le_max_left _ _)).ne')).div_const _)
  have ev (d : ℝ) (g : T → ℝ≥0) (f : T →+* ℝ) (hf : Monotone f) (he : ∀ A, ↑(g A) = f A) :
      v (d, g) = values d f := by
    funext A
    unfold v values
    rw [he]
    by_cases h : A = 0
    · simp [h]
    · rw [max_eq_right (value_one_le hf h)]
  have h : ordinary K S D = v '' (Icc 0 D ×ˢ Spectrum.points T) := by
    ext P
    constructor
    · rintro ⟨d, hd, f, hf, rfl⟩
      have hn (A : T) : 0 ≤ f A := by simpa using hf (zero_le A)
      let g : T →+* ℝ≥0 :=
        { toFun := fun A => ⟨f A, hn A⟩
          map_zero' := Subtype.ext (map_zero f)
          map_one' := Subtype.ext (map_one f)
          map_add' := fun a b => Subtype.ext (f.map_add a b)
          map_mul' := fun a b => Subtype.ext (f.map_mul a b) }
      exact ⟨(d, g), ⟨hd, g, hf, rfl⟩, ev d g f hf (fun _ => rfl)⟩
    · rintro ⟨⟨d, g⟩, ⟨hd, f, hf, he⟩, rfl⟩
      let f' := NNReal.toRealHom.comp f
      have hf' : Monotone f' := hf
      refine ⟨d, hd, f', hf', ev d g f' hf' ?_⟩
      intro A
      exact congrArg NNReal.toReal (congrFun he A).symm
  rw [h]
  exact (isCompact_Icc.prod (Spectrum.compact_points exists_bound)).image hv

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

section
/-!
# Compatible realizations of a finite price placement

A witness on the enlarged marking can have a different scale. Its
scale bound comes from the diameter and the number of names.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing
open Spectral

variable {K S T : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
variable {Y : Type*} [MetricSpace Y]

def Realized (x : S → Y) (P : Tensor K S → ℝ) (D : ℝ) : Prop :=
  (∀ a b, dist (x a) (x b) ≤ D) ∧
  ∀ (U : Type) [Fintype U] [DecidableEq U] [Nonempty U] (z : U → Y),
    (∀ i j, dist (Sum.elim x z i) (Sum.elim x z j) ≤ 2 * D) →
    ∃ Q ∈ Tensor.ordinary K (S ⊕ U) (2 * D * Fintype.card (S ⊕ U)),
      (∀ A, Q (Tensor.pad U A) = P A) ∧
      ∀ i j, Q (Tensor.wire K i j 2) = dist (Sum.elim x z i) (Sum.elim x z j)

theorem Realized.zero {x : S → Y} {P : Tensor K S → ℝ} {D : ℝ} (h : Realized x P D) :
    P 0 = 0 := by
  let i := Classical.arbitrary S
  have hD : 0 ≤ D := dist_nonneg.trans (h.1 i i)
  have hd (a b : S) : dist (x a) (x b) ≤ 2 * D := (h.1 a b).trans (by linarith)
  obtain ⟨_, ⟨d, _, f, _, rfl⟩, he, _⟩ := h.2 S x (fun j k => by cases j <;> cases k <;> exact hd _ _)
  rw [← he, (Tensor.padding S).zero]
  simp [Tensor.values]

variable (K Y) in
def SpectralSpace : Prop :=
  ∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S] (x : S → Y),
    ∃ P : Tensor K S → ℝ, (∀ a b, P (Tensor.wire K a b 2) = dist (x a) (x b)) ∧
      ∀ D : ℝ, 0 < D → (∀ a b, dist (x a) (x b) ≤ D) → Realized x P D

variable (K) in
def Represents [Fintype T] [DecidableEq T] (P : Tensor K T → ℝ) (x : T → Y) : Prop :=
  (∀ a b, P (Tensor.wire K a b 2) = dist (x a) (x b)) ∧
    ∀ (S : Type) [Fintype S] [DecidableEq S] [Nonempty S] (z : S → T) (D : ℝ),
      0 < D → (∀ a b, dist (x (z a)) (x (z b)) ≤ D) →
        Realized (x ∘ z) (P ∘ Tensor.place z) D

end OAI.LinearAlgebra.MatrixExponent.Routing
end

/-! # Preservation of shared labels and wire distances under extension -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  (U : Type) [Fintype U] [DecidableEq U]

theorem pad_shared (V : Finset S) (n : ℕ) :
    pad U (shared K V n) = shared K (V.image Sum.inl) n := by
  rw [← place_inl, place_shared]

theorem pad_wire (a b : S) (n : ℕ) :
    pad U (wire K a b n) = wire K (.inl a) (.inl b) n := by
  simp [wire, pad_shared]

variable {U}

theorem dist_pad {f : Tensor K S →+* ℝ} {g : Tensor K (S ⊕ U) →+* ℝ}
    (h : ∀ B, g (pad U B) = f B) (a b : S) :
    dist g (.inl a) (.inl b) = dist f a b := by
  unfold dist
  rw [← pad_wire, h]

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-!
# Simultaneous geodesic placement

Fold all new sites onto the first and then the second endpoints.
One extension interpolates these evaluations from above. The triangle
inequality forces equality on each of the prescribed endpoint distances.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S U : Type} [Field K] [Fintype S] [DecidableEq S]
    [Fintype U] [DecidableEq U]

def foldSites (a : U → S) : Tensor K (S ⊕ U) →+* Tensor K S :=
  group (Sum.elim id a) (fun s => ⟨.inl s, rfl⟩)

theorem foldSites_mono (a : U → S) : Monotone (foldSites (K := K) a) := group_mono _ _

theorem foldSites_wire (a : U → S) (x y : S ⊕ U) (n : ℕ) :
    foldSites a (wire K x y n) = wire K (Sum.elim id a x) (Sum.elim id a y) n :=
  group_wire _ _ x y n

theorem foldSites_pad [Nonempty S] (a : U → S) (B : Tensor K S) :
    foldSites a (pad U B) = B := group_pad _ _ (fun _ => rfl) B

/-- Two sharp distance bounds for a geodesic position at parameter t. -/
def Between (f : Tensor K S →+* ℝ) (a x b : S) (t : ℝ) : Prop :=
  dist f a x = t * dist f a b ∧ dist f x b = (1 - t) * dist f a b

theorem between_of_le (f : Tensor K S →+* ℝ) (hf : Monotone f) {a x b : S} {t : ℝ}
    (ha : dist f a x ≤ t * dist f a b) (hb : dist f x b ≤ (1 - t) * dist f a b) :
    Between f a x b t := by
  have h := dist_triangle f hf a x b
  constructor <;> linarith

theorem geodesic [Nonempty S] (f : Tensor K S →+* ℝ) (hf : Monotone f)
    (a b : U → S) {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) :
    ∃ g : Tensor K (S ⊕ U) →+* ℝ, Monotone g ∧ (∀ B, g (pad U B) = f B) ∧
      (∀ i, Between g (.inl (a i)) (.inr i) (.inl (b i)) t) ∧
      (∀ X, g X ≤ f (foldSites a X) ^ (1 - t) * f (foldSites b X) ^ t) := by
  let v (c : U → S) := f.comp (foldSites c)
  have hv (c : U → S) : Monotone (v c) := hf.comp (foldSites_mono c)
  have he (c : U → S) (B : Tensor K S) : v c (pad U B) = f B :=
    congrArg f (foldSites_pad c B)
  obtain ⟨g, hg, eg, h⟩ := interpolate f hf (v b) (v a) (hv b) (hv a) (he b) (he a) ht ht'
  have hu (X : Tensor K (S ⊕ U)) : g X ≤ f (foldSites a X) ^ (1 - t) * f (foldSites b X) ^ t :=
    (h X).trans_eq (mul_comm _ _)
  refine ⟨g, hg, eg, ?_, hu⟩
  have hd (x y : S ⊕ U) : dist g x y ≤
      (1 - t) * dist f (Sum.elim id a x) (Sum.elim id a y) +
      t * dist f (Sum.elim id b x) (Sum.elim id b y) := by
    have hxy := hu (wire K x y 2)
    rw [foldSites_wire, foldSites_wire, price_wire g hg _ _ (by decide),
      price_wire f hf _ _ (by decide), price_wire f hf _ _ (by decide)] at hxy
    have hpos : 0 < (2 : ℝ) := by norm_num
    simp only [Nat.cast_ofNat, ← Real.rpow_mul hpos.le, ← Real.rpow_add hpos] at hxy
    have hd := (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp hxy
    simpa only [mul_comm] using hd
  intro i
  apply between_of_le g hg
  · simpa [dist_pad eg, dist_self] using hd (.inl (a i)) (.inr i)
  · simpa [dist_pad eg, dist_self] using hd (.inr i) (.inl (b i))

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end
