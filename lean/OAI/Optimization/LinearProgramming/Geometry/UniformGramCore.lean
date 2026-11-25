import OAI.Optimization.LinearProgramming.Geometry.UniformInverse
import OAI.Optimization.LinearProgramming.Geometry.UniformGramTranspose
import OAI.Optimization.LinearProgramming.Geometry.GramAlgorithm

/-! A single fixed RAM block computing the rational projector of independent
rows. The same code and rational constants serve all dimensions. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Compression
open scoped Matrix BigOperators

/-- Scalar values needed by the fixed program, expressed only in terms of the
input row matrix. -/
structure UniformGramValues {K : Type} [Field K] {r n : ℕ} (P : K → Prop)
    (D : Matrix (Fin r) (Fin n) K) : Prop where
  zero : P 0
  one : P 1
  neg : ∀ x, P x → P (-x)
  gram : ∀ i j : Fin r, ∀ u : Finset (Fin n), P (∑ k ∈ u, D i k * D j k)
  reciprocal : P (D * Dᵀ).det⁻¹
  bird : ∀ a k, k<r → ∀ z : BirdRegister r, let A := requestedGramMatrix (D * Dᵀ) a
    P (z.read A (birdLayer A k))
  inverse : ∀ i j : Fin r, let G := D*Dᵀ
    P (G.det⁻¹ * (G.updateRow j (Pi.single i 1)).det)
  left : ∀ i : Fin n, ∀ j : Fin r, ∀ u : Finset (Fin r),
    P (∑ k ∈ u, D k i * (D * Dᵀ)⁻¹ k j)
  result : ∀ i j : Fin n, ∀ u : Finset (Fin r),
    P (∑ k ∈ u, (Dᵀ * (D * Dᵀ)⁻¹) i k * D k j)

/-- The single ordered-field program for the complete Gram projector. -/
def uniformGramBlock : Block :=
  .seq gramTransposePhase (.seq (gramProductPhase .gram)
    (.seq uniformGramInversePhase (.seq (gramProductPhase .left) (gramProductPhase .result))))

def rowPhaseTime (m p k : ℕ) := 6 + uniformTableTime m p (uniformRowDotCost m p k)

def uniformGramTime (r n : ℕ) :=
  gramTransposeTime r n + rowPhaseTime r r n + gramInverseTime r +
    rowPhaseTime n r r + rowPhaseTime n n r

theorem uniformGramBlock_spec {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {r n : ℕ} (l : GramLayout r n) (P : K → Prop) (s : Memory K) (hh : GramHeader l s)
    (hs : s.AllData P) (hD : LinearIndependent K (uniformRect r n l.d s).row)
    (values : UniformGramValues P (uniformRect r n l.d s)) :
    ∃ t k, k≤uniformGramTime r n ∧ Block.Eval (Memory.AllData P) uniformGramBlock s k t ∧
      uniformRect n n l.out t = rowGramProjector (uniformRect r n l.d s) ∧
      (∀ q, 64≤q → (q<l.tr ∨ l.workB+r*r≤q) → t.data q=s.data q) ∧
      ∀ q, q=14 ∨ 50≤q → t.index q=s.index q := by
  let D := uniformRect r n l.d s
  let G := D * Dᵀ
  have hmin := l.minimum
  have hdt := l.d_tr; have htg := l.tr_g; have hgi := l.g_inv; have hil := l.inv_left
  have hlo := l.left_out; have hos := l.out_sub; have hsa := l.sub_workA; have hab := l.workA_workB
  obtain ⟨u,k₁,b₁,e₁,ut,fu⟩ := gramTransposePhase_spec l P s hh hs
  have ud : uniformRect r n l.d u = D := fu.read hmin (Or.inl hdt) (by omega)
  obtain ⟨v,k₂,b₂,e₂,vg,fv⟩ := gramProductPhase_spec l .gram P u (fu.header hh) e₁.safe_end
    (by dsimp only [GramLayout.productCall]; rw [ud]; exact values.gram)
  change uniformRect r r l.g v = uniformRect r n l.d u * (uniformRect r n l.d u)ᵀ at vg
  rw [ud] at vg
  have vt : uniformRect n r l.tr v=Dᵀ := (fv.read (by omega) (Or.inl htg) (by omega)).trans ut
  have hvh := fv.header (fu.header hh)
  have det : G.det ≠ 0 := isUnit_iff_ne_zero.mp (gram_det_isUnit_of_independent_rows D hD)
  obtain ⟨w,k₃,b₃,e₃,wi,fw⟩ := uniformGramInversePhase_spec l P v hvh e₂.safe_end
    values.zero values.one values.neg (vg ▸ det) (vg ▸ values.reciprocal)
    (vg ▸ values.bird) (vg ▸ values.inverse)
  rw [vg] at wi
  have wt : uniformRect n r l.tr w=Dᵀ := (fw.read (by omega) (Or.inl (by omega)) (by omega)).trans vt
  have hGt : G⁻¹ᵀ = G⁻¹ := by simp [G,Matrix.transpose_nonsing_inv]
  have sym (k j : Fin r) : G⁻¹ j k = G⁻¹ k j := congrFun (congrFun hGt k) j
  have hwh := fw.header hvh
  obtain ⟨z,k₄,b₄,e₄,zl,fz⟩ := gramProductPhase_spec l .left P w hwh e₃.safe_end (by
    dsimp only [GramLayout.productCall]
    rw [wt,wi]
    intro i j U
    change P (∑ k ∈ U, D k i * G⁻¹ j k)
    have he : (∑ k ∈ U, D k i * G⁻¹ j k) = ∑ k ∈ U, D k i * G⁻¹ k j := by
      apply Finset.sum_congr rfl
      intro k _
      rw [sym k j]
    rw [he]
    exact values.left i j U)
  change uniformRect n r l.left z = uniformRect n r l.tr w * (uniformRect r r l.inv w)ᵀ at zl
  rw [wt,wi,hGt] at zl
  have zt : uniformRect n r l.tr z=Dᵀ := (fz.read (by omega)
    (Or.inl (by dsimp [GramLayout.productCall]; omega)) (by omega)).trans wt
  obtain ⟨t,k₅,b₅,e₅,tp,ft⟩ := gramProductPhase_spec l .result P z (fz.header hwh) e₄.safe_end (by
    dsimp only [GramLayout.productCall]
    rw [zl,zt]
    exact values.result)
  change uniformRect n n l.out t = uniformRect n r l.left z * (uniformRect n r l.tr z)ᵀ at tp
  rw [zl,zt,Matrix.transpose_transpose] at tp
  refine ⟨t,_,?_,e₁.seq (e₂.seq (e₃.seq (e₄.seq e₅))),tp,?_,?_⟩
  · change k₂ ≤ rowPhaseTime r r n at b₂
    change k₄ ≤ rowPhaseTime n r r at b₄
    change k₅ ≤ rowPhaseTime n n r at b₅
    unfold uniformGramTime; omega
  · intro q hq hframe
    have hwork : q<l.sub ∨ l.workB+r*r≤q := by omega
    exact (ft.data q hq (by dsimp [GramLayout.productCall]; omega) hwork).trans
      ((fz.data q hq (by dsimp [GramLayout.productCall]; omega) hwork).trans
      ((fw.data q hq (by omega) hwork).trans
      ((fv.data q hq (by dsimp [GramLayout.productCall]; omega) hwork).trans
      (fu.data q hq (by omega) hwork))))
  · intro q hq
    exact (ft.index q hq).trans ((fz.index q hq).trans
      ((fw.index q hq).trans ((fv.index q hq).trans (fu.index q hq))))

/-- Every rational quantity used by the fixed program fits the same polynomial
proved for the division-free determinant and the rectangular arithmetic circuits. -/
theorem uniformGramValues_ratBits {r n B : ℕ} (D : Matrix (Fin r) (Fin n) ℚ)
    (h : ∀ i j, ratBits (D i j) ≤ B) :
    UniformGramValues (fun x => ratBits x ≤ gramWorkspaceBits r n B) D := by
  let G := D*Dᵀ
  let g := dotBitBound n B B
  have hg : ∀ i j, ratBits (G i j) ≤ g :=
    matrix_product_bits D Dᵀ h (fun i j => h j i)
  have hg0 : 3 ≤ g := by dsimp [g,dotBitBound]; omega
  have hbound := gramRegister_bits D h
  have heq (a : Option (Fin r × Fin r)) : requestedGramMatrix G a = gramDetInput G a := by
    cases a with
    | none => rfl
    | some pair => rcases pair with ⟨_,_⟩; rfl
  refine ⟨hbound .zero,hbound .one,fun x hx => by simpa [PrimalDual.ratBits_neg] using hx,
    fun i j u => hbound (.gramDot i j u),?_,?_,?_,?_,?_⟩
  · simpa only [GramRegister.read,Elimination.determinant_eq] using hbound .reciprocal
  · intro a k hk z
    change ratBits (z.read (requestedGramMatrix G a) (birdLayer (requestedGramMatrix G a) k)) ≤ _
    rw [heq]
    exact hbound (.detTemporary a ⟨k,by omega⟩ z)
  · intro i j
    have hd := (gram_determinants_bits G hg0 hg).1
    have hc := (gram_determinants_bits G hg0 hg).2 i j
    simp only [Elimination.determinant_eq] at hd hc
    apply (ratBits_mul_le_add _ _).trans
    rw [ratBits_inv_eq]
    dsimp only [gramWorkspaceBits]
    dsimp only [G,g] at hd hc
    omega
  · intro i j u
    simpa only [GramRegister.read,gramInverse_eq] using hbound (.leftDot i j u)
  · intro i j u
    simpa only [GramRegister.read,gramInverse_eq] using hbound (.outputDot i j u)

end Geometry
end LinearProgramming
end Optimization
end OAI
