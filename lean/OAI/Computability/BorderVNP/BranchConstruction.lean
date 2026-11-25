import OAI.Computability.BorderVNP.BranchArithmetic
import OAI.Computability.BorderVNP.BranchCurveGeometric
import OAI.Computability.BorderVNP.BranchFiniteCuts
import OAI.Computability.BorderVNP.BranchNumberedReader

/-!
# From image closure to the finite advice-field branch

This is the curve construction of Proposition 9.2. The coefficient map and prescribed
point are defined over a finite field. The hypothesis is membership in the actual
image closure over its algebraic closure. The resulting system is in the original
affine parameters and one deformation variable, has bounded degree and uses the
weighted rows specified by finite scalar advice. Its generic point specializes all
prescribed output coordinates simultaneously.
-/

namespace OAI
namespace Computability
namespace BorderVNP

universe u v

namespace Branch

open MvPolynomial

variable {E₀ : Type v} {K : Type u} [Field E₀] [Fintype E₀] [Field K] [IsAlgClosed K]
  [Algebra E₀ K] {I : Type*} [Fintype I] {h : ℕ}

private theorem map_graphSliceRow {E L : Type*} [Field E] [Field L] (f : E →+* L)
    (c : I → E) (s : Finset (Fin (h+1))) (p : Fin (h+1) → E) (e : I → ℕ) (B : ℕ) (a : E) :
    map f (graphSliceRow c s p e B a) = graphSliceRow (f ∘ c) s (f ∘ p) e B (f a) := by
  simp only [graphSliceRow, map_sum, map_mul, map_C, map_pow]
  apply Finset.sum_congr rfl
  intro j _
  cases j <;> simp [fiberResiduals]

/-- Advice data for the weighted slices and the affine deformation. -/
structure CurveAdvice (E : Type*) (h : ℕ) where
  /-- Index of the chosen standard projective chart. -/
  chart : Option (Fin h)
  /-- Parameter coordinates fixed during the first finite cut. -/
  pins : Finset (Fin (h+1))
  /-- Constants used in these coordinate hyperplanes. -/
  pinValue : Fin (h+1) → E
  /-- Scalars selecting the weighted slices. -/
  scalar : Fin h → E
  /-- Constant displacement yielding a generically nonsingular curve. -/
  target : Fin h → E

/-- The square branch system computed from the advice, before any specialization of t. -/
noncomputable def CurveAdvice.equations {E : Type*} [Field E] (advice : CurveAdvice E h)
    (Y : I → MvPolynomial (Fin h) E) (c : I → E) (e : I → ℕ) (B : ℕ) :
    Fin h → MvPolynomial (Option (Fin h)) E :=
  affineEquation Y advice.chart
    (fun i => graphSliceRow c advice.pins advice.pinValue e B (advice.scalar i)) advice.target

/-- Each full row has total degree at most the table degree plus two. -/
theorem CurveAdvice.equations_degree {E : Type*} [Field E] (advice : CurveAdvice E h)
    (Y : I → MvPolynomial (Fin h) E) (c : I → E) (e : I → ℕ) (d B : ℕ)
    (hd : ∀ i, (Y i).totalDegree ≤ d) (j : Fin h) :
    (advice.equations Y c e B j).totalDegree ≤ d+2 :=
  affineEquation_degree Y advice.chart hd _ (fun _ => graphSliceRow_degree ..) advice.target j

set_option maxHeartbeats 2000000 in
/-- The finite field, bounded equations, geometric branch, arithmetic branch and finite
residue field arise from the full closure hypothesis. Both extension factors are explicit;
the number of field constants stored for the weighted rows is polynomial in the parameter
count. -/
theorem branches_of_imageClosure (Y : I → MvPolynomial (Fin h) E₀) (c : I → E₀)
    (e : I → ℕ) (d B : ℕ) (hh : 0 < h) (hY : ∀ i, (Y i).totalDegree ≤ d)
    (he : Function.Injective e) (hB : ∀ i, e i < B)
    (hc : algebraMap E₀ K ∘ c ∈ imageClosure (Set.range
      (fun x : Fin h → K => fun i => eval x (map (algebraMap E₀ K) (Y i))))) :
    ∃ (E : IntermediateField E₀ K), Finite E ∧
      Nat.card E ≤ Fintype.card E₀ * max (sliceGridBound h d B (Fintype.card I)) 1 *
        max (displacementDegree h d (d+1)) 1 ∧
      ∃ (advice : CurveAdvice E h),
        let YE := fun i => map (algebraMap E₀ E) (Y i)
        let cE := algebraMap E₀ E ∘ c
        let G := advice.equations YE cE e B
        (∀ i, (G i).totalDegree ≤ d+2) ∧
          Nonempty (GeometricBranch (fun i => map E.subtype (YE i)) (E.subtype ∘ cE)
            (fun i => genericRow (map E.subtype (G i)))) ∧
          ∃ branch : GeometricBranch YE cE (fun i => genericRow (G i)),
            Finite (IsLocalRing.ResidueField branch.place) := by
  classical
  let T := DeformationField K
  have : Infinite T := Infinite.of_injective (algebraMap K T) (algebraMap K T).injective
  let t := algebraMap (Polynomial K) T Polynomial.X
  let yK := fun i => map (algebraMap E₀ K) (Y i)
  let cK := algebraMap E₀ K ∘ c
  have hyK (i) : (yK i).totalDegree ≤ d := (Finset.sup_mono (support_map_subset _ _)).trans (hY i)
  obtain ⟨k,E₁,hE₁,hcard₁,hk,s,p,a,hcut,z,hz⟩ := exists_finite_slices yK c e d B hh hyK he hB hc
  let := Fintype.ofFinite E₁
  let D₁ := fun i => graphSliceRow ((algebraMap E₀ E₁) ∘ c) s p e B (a i)
  let D := fun i => map E₁.subtype (D₁ i)
  have hD (i) : (D i).totalDegree ≤ 1 :=
    (Finset.sup_mono (support_map_subset E₁.subtype (D₁ i))).trans
      (graphSliceRow_degree (E := E₁) _ s p e B (a i))
  obtain ⟨E₂,hE₂,hcard₂,v,f,hv,q,heq⟩ := choose_affine_slice_target (T := T) E₁ yK k hyK D hD
  let E := E₂.restrictScalars E₀
  have : Finite E := hE₂
  let vv := E₂.subtype ∘ v
  obtain ⟨M⟩ := geometric_branch_of_finite_slice yK k hk D hD hyK hcut z cK hz.1 hz.2 vv f hv q heq
  let inc : E →+* K := E.subtype
  let inc₁ : E₁ →+* K := E₁.subtype
  let lift : E₁ →+* E := algebraMap E₁ E₂
  let vE : Fin h → E := v
  let advice : CurveAdvice E h := ⟨k,s,lift ∘ p,lift ∘ a,vE⟩
  let yE := fun i => map (algebraMap E₀ E) (Y i)
  let cE := algebraMap E₀ E ∘ c
  let G := advice.equations yE cE e B
  have yi : (fun i => map inc (yE i)) = yK := by
    funext i; rw [show yE i = map (algebraMap E₀ E) (Y i) from rfl, map_map]; rfl
  have ci : inc ∘ cE = cK := rfl
  have di (i) : map inc (graphSliceRow cE s (lift ∘ p) e B (lift (a i))) = D i := by
    change map inc _ = map inc₁ (graphSliceRow ((algebraMap E₀ E₁) ∘ c) s p e B (a i))
    rw [map_graphSliceRow inc, map_graphSliceRow inc₁]
    rfl
  have gi (i) : map (deformationMap inc) (genericRow (G i)) =
      affineRow k t (fun j => map (algebraMap K T) (affineSlice yK k (D j))) (algebraMap K T ∘ vv) i := by
    rw [genericRow_map]
    let D₂ := fun j => graphSliceRow cE s (lift ∘ p) e B (lift (a j))
    change genericRow (map inc (affineEquation yE k D₂ vE i)) = _
    rw [map_affineEquation inc, yi, show (fun j => map inc (D₂ j)) = D from funext di]
    change genericRow (affineEquation yK k D vv i) = _
    exact specialize_affineEquation (algebraMap K T) yK k D vv i t
  have m : GeometricBranch (fun i => map inc (yE i)) (inc ∘ cE)
      (fun i => map (deformationMap inc) (genericRow (G i))) := by
    rw [yi, ci, funext gi]
    exact M
  have geom : GeometricBranch (fun i => map inc (yE i)) (inc ∘ cE)
      (fun i => genericRow (map inc (G i))) := by
    rw [← funext (fun i => genericRow_map inc (G i))]
    exact m
  have hcard : Nat.card E ≤ Fintype.card E₀ * max (sliceGridBound h d B (Fintype.card I)) 1 *
      max (displacementDegree h d (d+1)) 1 := by
    change Nat.card E₂ ≤ _
    rw [Nat.card_eq_fintype_card] at hcard₁
    exact hcard₂.trans (Nat.mul_le_mul_right _ hcard₁)
  exact ⟨E,hE₂,hcard,advice,advice.equations_degree yE cE e d B
    (fun i => (Finset.sup_mono (support_map_subset _ _)).trans (hY i)),
    ⟨geom⟩, advice_field_branch inc yE cE _ m⟩

/-- The finite field, bounded equations, generically nonsingular branch and arithmetic
residue field arise from the full closure hypothesis. Both extension factors are explicit;
the number of field constants stored for the weighted rows is polynomial in the parameter
count. -/
theorem branch_of_imageClosure (Y : I → MvPolynomial (Fin h) E₀) (c : I → E₀)
    (e : I → ℕ) (d B : ℕ) (hh : 0 < h) (hY : ∀ i, (Y i).totalDegree ≤ d)
    (he : Function.Injective e) (hB : ∀ i, e i < B)
    (hc : algebraMap E₀ K ∘ c ∈ imageClosure (Set.range
      (fun x : Fin h → K => fun i => eval x (map (algebraMap E₀ K) (Y i))))) :
    ∃ (E : IntermediateField E₀ K), Finite E ∧
      Nat.card E ≤ Fintype.card E₀ * max (sliceGridBound h d B (Fintype.card I)) 1 *
        max (displacementDegree h d (d+1)) 1 ∧
      ∃ (advice : CurveAdvice E h),
        let YE := fun i => map (algebraMap E₀ E) (Y i)
        let cE := algebraMap E₀ E ∘ c
        let G := advice.equations YE cE e B
        (∀ i, (G i).totalDegree ≤ d+2) ∧
          ∃ branch : GeometricBranch YE cE (fun i => genericRow (G i)),
            Finite (IsLocalRing.ResidueField branch.place) := by
  obtain ⟨E, hE, hcard, advice, hdeg, _, branch⟩ :=
    branches_of_imageClosure Y c e d B hh hY he hB hc
  exact ⟨E, hE, hcard, advice, hdeg, branch⟩

end Branch

end BorderVNP
end Computability
end OAI
