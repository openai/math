import OAI.LinearAlgebra.FiniteFourier.LayerSynchronization

/-! # A shear layer is a disjoint sum of cube transforms

Each block carries an independent set of Boolean coordinates. Parallel composition
takes the disjoint union of block labels. Tensoring chooses one block from each
factor and concatenates the Boolean coordinates of those blocks. These operations
give a single simultaneous row and column permutation for the entire layer.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

noncomputable section
section

open Matrix
open scoped Kronecker

variable {K : Type*} [CommSemiring K] {I J : Type} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

private structure CubeDecomposition {I : Type} (A : Matrix I I K) where
  B : Type
  [fb : Fintype B]
  Z : B → Type
  [fz : ∀ b, Fintype (Z b)]
  tag : I → B
  point : ∀ b, (Z b → Fin 2) → I
  tag_point (b x) : tag (point b x) = b
  covers (i : I) : ∃ x, point (tag i) x = i
  injective (b) : Function.Injective (point b)
  inside (b x y) : A (point b x) (point b y) = ∏ k, unitShear K (x k) (y k)
  outside {b c} (h : b ≠ c) (x y) : A (point b x) (point c y) = 0

attribute [instance] CubeDecomposition.fb CubeDecomposition.fz

namespace CubeDecomposition

private def one : CubeDecomposition (1 : Matrix I I K) where
  B := I
  Z := fun _ => Empty
  tag := id
  point b _ := b
  tag_point _ _ := rfl
  covers i := ⟨Empty.elim, rfl⟩
  injective _ _ _ _ := Subsingleton.elim _ _
  inside _ _ _ := by simp
  outside h _ _ := Matrix.one_apply_ne h

private def elementary : CubeDecomposition (unitShear K) where
  B := Unit
  Z := fun _ => Unit
  tag _ := ()
  point _ x := x ()
  tag_point _ _ := rfl
  covers i := ⟨fun _ => i, rfl⟩
  injective _ _ _ h := funext fun () => h
  inside _ _ _ := by simp
  outside h := (h (Subsingleton.elim _ _)).elim

private def relabel {A : Matrix I I K} (D : CubeDecomposition A) (e : I ≃ J) :
    CubeDecomposition (A.submatrix e.symm e.symm) where
  B := D.B
  Z := D.Z
  tag i := D.tag (e.symm i)
  point b x := e (D.point b x)
  tag_point b x := by simp [D.tag_point]
  covers i := by
    obtain ⟨x, hx⟩ := D.covers (e.symm i)
    exact ⟨x, (congrArg e hx).trans (e.apply_symm_apply _)⟩
  injective b := e.injective.comp (D.injective b)
  inside b x y := by simpa [submatrix] using D.inside b x y
  outside h x y := by simpa [submatrix] using D.outside h x y

private def tensor {A : Matrix I I K} {B : Matrix J J K}
    (D : CubeDecomposition A) (E : CubeDecomposition B) : CubeDecomposition (A ⊗ₖ B) where
  B := D.B × E.B
  Z b := D.Z b.1 ⊕ E.Z b.2
  tag i := (D.tag i.1, E.tag i.2)
  point b x := (D.point b.1 (fun z => x (.inl z)), E.point b.2 (fun z => x (.inr z)))
  tag_point b x := Prod.ext (D.tag_point ..) (E.tag_point ..)
  covers i := by
    obtain ⟨x, hx⟩ := D.covers i.1
    obtain ⟨y, hy⟩ := E.covers i.2
    exact ⟨Sum.elim x y, Prod.ext hx hy⟩
  injective b x y h := by
    have h₁ := D.injective _ (Prod.mk.inj h).1
    have h₂ := E.injective _ (Prod.mk.inj h).2
    funext z
    cases z with
    | inl z => exact congrFun h₁ z
    | inr z => exact congrFun h₂ z
  inside b x y := by rw [kronecker_apply, D.inside, E.inside, Fintype.prod_sum_type]
  outside {b c} h x y := by
    rw [kronecker_apply]
    by_cases h₁ : b.1 = c.1
    · rw [E.outside (fun h₂ => h (Prod.ext h₁ h₂)), mul_zero]
    · rw [D.outside h₁, zero_mul]

private def parallel {A : Matrix I I K} {B : Matrix J J K}
    (D : CubeDecomposition A) (E : CubeDecomposition B) : CubeDecomposition (fromBlocks A 0 0 B) where
  B := D.B ⊕ E.B
  Z := Sum.elim D.Z E.Z
  fz := fun b => match b with | .inl b => D.fz b | .inr c => E.fz c
  tag := Sum.map D.tag E.tag
  point := fun b => match b with
    | .inl b => fun x => Sum.inl (D.point b x)
    | .inr b => fun x => Sum.inr (E.point b x)
  tag_point b x := by
    cases b with
    | inl b => exact congrArg Sum.inl (D.tag_point b x)
    | inr b => exact congrArg Sum.inr (E.tag_point b x)
  covers i := by
    cases i with
    | inl i =>
      obtain ⟨x, hx⟩ := D.covers i
      exact ⟨x, congrArg Sum.inl hx⟩
    | inr i =>
      obtain ⟨x, hx⟩ := E.covers i
      exact ⟨x, congrArg Sum.inr hx⟩
  injective b := by
    cases b with
    | inl b => exact Sum.inl_injective.comp (D.injective b)
    | inr b => exact Sum.inr_injective.comp (E.injective b)
  inside b x y := by cases b with
    | inl b => exact D.inside b x y
    | inr b => exact E.inside b x y
  outside {b c} h x y := by
    cases b <;> cases c
    · exact D.outside (fun e => h (congrArg Sum.inl e)) _ _
    · rfl
    · rfl
    · exact E.outside (fun e => h (congrArg Sum.inr e)) _ _

variable {ι : Type} [Fintype ι] {T : ι → Type} {A : ∀ i, Matrix (T i) (T i) K}

private def grid [DecidableEq ι] (D : ∀ i, CubeDecomposition (A i)) : CubeDecomposition (gridTensor A) where
  B := ∀ i, (D i).B
  Z b := Σ i, (D i).Z (b i)
  tag x i := (D i).tag (x i)
  point b x i := (D i).point (b i) (fun z => x ⟨i, z⟩)
  tag_point b x := funext fun i => (D i).tag_point ..
  covers x := by
    choose y hy using fun i => (D i).covers (x i)
    exact ⟨Sigma.uncurry y, funext hy⟩
  injective b x y h := by
    apply funext
    rintro ⟨i, z⟩
    exact congrFun ((D i).injective _ (congrFun h i)) z
  inside b x y := by simp_rw [gridTensor, (D _).inside, Fintype.prod_sigma]
  outside {b c} h x y := by
    obtain ⟨i, hi⟩ : ∃ i, b i ≠ c i := by exact not_forall.mp (fun he => h (funext he))
    exact Finset.prod_eq_zero (Finset.mem_univ i) ((D i).outside hi _ _)

private def blocks [DecidableEq ι] (D : ∀ i, CubeDecomposition (A i)) :
    CubeDecomposition (blockDiagonal' A) where
  B := Σ i, (D i).B
  Z b := (D b.1).Z b.2
  tag x := ⟨x.1, (D x.1).tag x.2⟩
  point b x := ⟨b.1, (D b.1).point b.2 x⟩
  tag_point b x := congrArg (Sigma.mk b.1) ((D b.1).tag_point ..)
  covers x := by
    obtain ⟨y, hy⟩ := (D x.1).covers x.2
    exact ⟨y, congrArg (Sigma.mk x.1) hy⟩
  injective b x y h := (D b.1).injective _ (sigma_mk_injective h)
  inside b x y := (blockDiagonal'_apply_eq ..).trans ((D b.1).inside ..)
  outside {b c} h x y := by
    obtain ⟨i,b⟩ := b
    obtain ⟨j,c⟩ := c
    by_cases hij : i = j
    · subst j
      rw [blockDiagonal'_apply_eq]
      exact (D i).outside (fun he => h (congrArg (Sigma.mk i) he)) _ _
    · exact blockDiagonal'_apply_ne A _ _ hij

end CubeDecomposition

private theorem shearLayer_decomposition {k : LayerKind} {A : Matrix I I K} (h : LayerMatrix k A) :
    k = .shear → Nonempty (CubeDecomposition A) := by
  induction h with
  | id k => exact fun _ => ⟨CubeDecomposition.one⟩
  | monomial e d => intro h; cases h
  | unitShear => exact fun _ => ⟨CubeDecomposition.elementary⟩
  | relabel e h ih => exact fun hk => ⟨(ih hk).some.relabel e⟩
  | tensor h₁ h₂ ih₁ ih₂ => exact fun hk => ⟨(ih₁ hk).some.tensor (ih₂ hk).some⟩
  | parallel h₁ h₂ ih₁ ih₂ => exact fun hk => ⟨(ih₁ hk).some.parallel (ih₂ hk).some⟩
  | grid h ih => exact fun hk => ⟨CubeDecomposition.grid fun i => (ih i hk).some⟩
  | blocks h ih => exact fun hk => ⟨CubeDecomposition.blocks fun i => (ih i hk).some⟩

/-- A shear layer is simultaneously row- and column-equivalent to a disjoint sum
of powers of the two-coordinate shear. The exponent may vary between blocks. -/
theorem shearLayer_normalForm {A : Matrix I I K} (hA : LayerMatrix .shear A) :
    ∃ (B : Type) (_ : Fintype B) (_ : DecidableEq B) (j : B → ℕ)
      (e : (Σ b, Fin (j b) → Fin 2) ≃ I),
      A.submatrix e e = Matrix.blockDiagonal' (fun b => gridTensor (fun _ : Fin (j b) => unitShear K)) := by
  classical
  let D := (shearLayer_decomposition hA rfl).some
  let j (b : D.B) := Fintype.card (D.Z b)
  let f (b : D.B) : D.Z b ≃ Fin (j b) := Fintype.equivFin _
  let g (p : Σ b, Fin (j b) → Fin 2) := D.point p.1 (p.2 ∘ f p.1)
  have hg : Function.Bijective g := by
    constructor
    · rintro ⟨b,x⟩ ⟨c,y⟩ h
      have he : b = c :=
        (D.tag_point b _).symm.trans ((congrArg D.tag h).trans (D.tag_point c _))
      subst c
      apply congrArg (Sigma.mk b)
      funext k
      obtain ⟨z, rfl⟩ := (f b).surjective k
      exact congrFun (D.injective b h) z
    · intro i
      obtain ⟨x, hx⟩ := D.covers i
      refine ⟨⟨D.tag i, x ∘ (f _).symm⟩, ?_⟩
      simpa [g, Function.comp_def] using hx
  refine ⟨D.B, D.fb, inferInstance, j, Equiv.ofBijective g hg, ?_⟩
  ext ⟨b,x⟩ ⟨c,y⟩
  change A (D.point b (x ∘ f b)) (D.point c (y ∘ f c)) = _
  by_cases h : b = c
  · subst c
    rw [D.inside, Matrix.blockDiagonal'_apply_eq]
    exact (f b).prod_comp (fun k => unitShear K (x k) (y k))
  · exact (D.outside h _ _).trans (Matrix.blockDiagonal'_apply_ne _ _ _ h).symm

end

end

end FiniteFourier
end LinearAlgebra
end OAI
