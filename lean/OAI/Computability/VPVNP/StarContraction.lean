import OAI.Computability.VPVNP.StarTensor

/-!
# Transport of a center covector

For the extension in Theorem 2.4, a covector on the output of a restriction
pulls back through the matrix at the new party. The matrices at the old
parties act after this contraction. Direct sums split the pulled-back
covector into its two coordinate blocks. An embedded old tensor has a
singleton center basis, so it factors through an arbitrary contraction.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v w w'

namespace WireTensor

variable {k : Type u} {J : Type v} [CommSemiring k]

section Local

variable [Fintype J]

/-- The center covector pulled back through a local restriction matrix. -/
def pullCovector {A B : Type*} [Fintype B] (L : B → A → k) (ξ : B → k) (a : A) : k :=
  ∑ b, ξ b * L b a

open scoped Classical in
/-- Split the center index out of a sum over all local basis tuples. -/
private theorem sum_withCenter {A : Option J → Type*} [∀ j, Fintype (A j)]
    (f : ((j : Option J) → A j) → k) :
    ∑ a, f a = ∑ t, ∑ b : (j : J) → A (some j), f (withCenter t b) := by
  classical
  rw [← Fintype.sum_prod_type']
  refine ((Equiv.piOptionEquivProd (β := A)).symm.sum_comp f).symm.trans ?_
  apply Finset.sum_congr rfl
  intro z _
  apply congrArg f
  funext j
  cases j <;> rfl

/-- The matrix at the center acts on its covector, and all other matrices act
on the resulting old-party array. -/
theorem contractCenter_applyLocal {A : Option J → Type w} {B : Option J → Type w'}
    [a : ∀ j, Fintype (A j)] [b : ∀ j, Fintype (B j)]
    (L : ∀ j, B j → A j → k) (T : Array k A) (ξ : B none → k) :
    (contractCenter (.mk B b (applyLocal L T)) ξ).coeff =
      applyLocal (fun j ↦ L (some j))
        (contractCenter (.mk A a T) (pullCovector (L none) ξ)).coeff := by
  classical
  funext x
  change (j : J) → B (some j) at x
  simp only [contractCenter, applyLocal, pullCovector]
  have split (c : B none) := sum_withCenter (A := A)
    (fun z ↦ (∏ j, L j (withCenter c x j) (z j)) * T z)
  calc
    _ = ∑ c, ξ c * ∑ t, ∑ y : (j : J) → A (some j),
          (∏ j, L j (withCenter c x j) (withCenter t y j)) * T (withCenter t y) := by
      apply Finset.sum_congr rfl
      intro c _
      apply congrArg (ξ c * ·)
      convert! split c using 2
      ext z
      simp
    _ = _ := ?_
  simp_rw [Fintype.prod_option]
  simp only [withCenter, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm, Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun y t ↦
    ∑ c, (∏ j, L (some j) (x j) (y j)) * (ξ c * L none c t * T (withCenter t y)))]
  apply Finset.sum_congr rfl
  intro t _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro c _
  ac_rfl

/-- Every contraction of the demand tensor is obtained by restricting a
contraction of the supply tensor. The pulled-back covector can be entangled
across all factors at the center. -/
theorem contractCenter_restricts {Y : Tensor.{u,v,w} k (Option J)}
    {X : Tensor.{u,v,w'} k (Option J)} (h : Restricts Y X) (ξ : X.Basis none → k) :
    ∃ η, Restricts (contractCenter Y η) (contractCenter X ξ) := by
  obtain ⟨L, hL⟩ := h
  refine ⟨pullCovector (L none) ξ, fun j ↦ L (some j), ?_⟩
  have hcoeff := (contractCenter_applyLocal L Y.coeff ξ).symm
  rw [hL] at hcoeff
  exact hcoeff

/-- Each coordinate block of the center covector contracts its own summand.
The old-party bases still form a direct sum. -/
theorem contractCenter_directSum (T : Tensor.{u,v,w} k (Option J))
    (U : Tensor.{u,v,w'} k (Option J)) (ξ : (directSum T U).Basis none → k) :
    contractCenter (directSum T U) ξ =
      directSum (contractCenter T (fun x ↦ ξ (.inl x))) (contractCenter U (fun y ↦ ξ (.inr y))) := by
  classical
  let B (j : Option J) := T.Basis j ⊕ U.Basis j
  let l (j : Option J) (c : B j) (x : T.Basis j) : k := if c = Sum.inl x then 1 else 0
  let r (j : Option J) (c : B j) (x : U.Basis j) : k := if c = Sum.inr x then 1 else 0
  have hl : pullCovector (l none) ξ = fun x ↦ ξ (.inl x) := by
    funext x
    unfold pullCovector
    rw [Finset.sum_eq_single (Sum.inl x)]
    · simp [l]
    · intro z _ hz
      simp [l, hz]
    · simp
  have hr : pullCovector (r none) ξ = fun y ↦ ξ (.inr y) := by
    funext y
    unfold pullCovector
    rw [Finset.sum_eq_single (Sum.inr y)]
    · simp [r]
    · intro z _ hz
      simp [r, hz]
    · simp
  have hlt := contractCenter_applyLocal l T.coeff ξ
  have hrt := contractCenter_applyLocal r U.coeff ξ
  rw [hl] at hlt
  rw [hr] at hrt
  unfold contractCenter directSum
  congr 1
  funext x
  change (j : J) → B (some j) at x
  change (∑ c, ξ c * ((applyLocal l T.coeff) (withCenter c x) +
      (applyLocal r U.coeff) (withCenter c x))) = _
  simp only [mul_add, Finset.sum_add_distrib, Pi.add_apply]
  exact congrArg₂ (· + ·) (congrFun hlt x) (congrFun hrt x)

/-- The old-party maps after restricting an extended direct sum act on the
contracted branches separately, with ordinary addition of their output arrays. -/
theorem contractCenter_restricted_directSum (T : Tensor.{u,v,w} k (Option J))
    (U : Tensor.{u,v,w'} k (Option J)) {X : Tensor k (Option J)}
    (h : Restricts (directSum T U) X) (ξ : X.Basis none → k) :
    ∃ (η : T.Basis none → k) (θ : U.Basis none → k)
        (L : ∀ j : J, X.Basis (some j) → T.Basis (some j) → k)
        (M : ∀ j : J, X.Basis (some j) → U.Basis (some j) → k),
      (contractCenter X ξ).coeff =
        applyLocal L (contractCenter T η).coeff + applyLocal M (contractCenter U θ).coeff := by
  obtain ⟨γ, hγ⟩ := contractCenter_restricts h ξ
  rw [contractCenter_directSum] at hγ
  obtain ⟨K, hK⟩ := hγ
  refine ⟨_, _, _, _, hK.symm.trans (applyLocal_directSum _ _ K)⟩

/-- An extended tensor can supply any center contraction with the trivial leg
restored. This lets an extending spectral point bound the old spectral value
of every contraction. -/
theorem restricts_embedOld_contractCenter (T : Tensor.{u,v,w} k (Option J))
    (ξ : T.Basis none → k) : Restricts T (embedOld (contractCenter T ξ)) := by
  classical
  let L (j : Option J) : (embedOld (contractCenter T ξ)).Basis j → T.Basis j → k :=
    match j with
    | none => fun _ t ↦ ξ t
    | some i => fun c t ↦ if c = t then 1 else 0
  refine ⟨L, ?_⟩
  funext x
  unfold applyLocal
  calc
    _ = ∑ t, ∑ y : (j : J) → T.Basis (some j),
          (∏ j, L j (x j) (withCenter t y j)) * T.coeff (withCenter t y) := by
      convert! sum_withCenter (A := T.Basis) (fun z ↦ (∏ j, L j (x j) (z j)) * T.coeff z) using 2
      ext z
      simp
    _ = _ := by
      let y₀ : (j : J) → T.Basis (some j) := fun j ↦ x (some j)
      simp only [Fintype.prod_option, L, withCenter, embedOld, contractCenter]
      apply Finset.sum_congr rfl
      intro t _
      change (∑ y, (ξ t * ∏ j, if y₀ j = y j then 1 else 0) * T.coeff (withCenter t y)) =
        ξ t * T.coeff (withCenter t y₀)
      simp [Fintype.prod_boole, ← funext_iff, mul_ite, ite_mul]

/-- Adding a trivial party preserves local restriction. -/
theorem embedOld_restricts {T : Tensor.{u,v,w} k J} {U : Tensor.{u,v,w'} k J}
    (h : Restricts T U) : Restricts (embedOld T) (embedOld U) := by
  classical
  obtain ⟨L, hL⟩ := h
  let M (j : Option J) : (embedOld U).Basis j → (embedOld T).Basis j → k :=
    match j with
    | none => fun _ _ ↦ 1
    | some i => L i
  refine ⟨M, ?_⟩
  funext x
  unfold applyLocal
  calc
    _ = ∑ t, ∑ y : (j : J) → (embedOld T).Basis (some j),
          (∏ j, M j (x j) (withCenter t y j)) * (embedOld T).coeff (withCenter t y) := by
      convert! sum_withCenter (A := (embedOld T).Basis)
        (fun z ↦ (∏ j, M j (x j) (z j)) * (embedOld T).coeff z) using 2
      ext z
      simp
    _ = _ := by
      change (∑ t : PUnit, ∑ y : (j : J) → T.Basis j,
        (∏ j, M j (x j) (withCenter t y j)) * (embedOld T).coeff (withCenter t y)) = _
      simpa only [Fintype.sum_unique, Fintype.prod_option, M, withCenter, embedOld, one_mul, applyLocal] using
        congrFun hL (fun j ↦ x (some j))

/-- Parallel products of embedded old tensors differ from the embedded
product only by the canonical bijection of their singleton center bases. -/
theorem embedOld_product_mutual (T : Tensor.{u,v,w} k J) (U : Tensor.{u,v,w'} k J) :
    Restricts (embedOld (tensorProduct T U)) (tensorProduct (embedOld T) (embedOld U)) ∧
      Restricts (tensorProduct (embedOld T) (embedOld U)) (embedOld (tensorProduct T U)) := by
  let e (j : Option J) : (tensorProduct (embedOld T) (embedOld U)).Basis j ≃
      (embedOld (tensorProduct T U)).Basis j :=
    match j with
    | none => (⟨fun _ ↦ .unit, fun _ ↦ (.unit, .unit), fun p ↦ by cases p; rfl,
        fun _ ↦ rfl⟩ : (PUnit × PUnit) ≃ PUnit)
    | some _ => Equiv.refl _
  exact restricts_of_reindex e (fun _ ↦ rfl)

end Local

/-- Evaluating the embedded singleton leg at one returns the old tensor. -/
theorem contractCenter_embedOld_one (T : Tensor.{u,v,w} k J) :
    contractCenter (embedOld T) (fun _ ↦ 1) = T := by
  cases T with
  | mk A a T =>
    unfold contractCenter embedOld
    congr 1
    funext x
    change (∑ _ : PUnit.{w+1}, 1 * T x) = T x
    rw [Fintype.sum_unique, one_mul]

/-- A scalar multiple of an old tensor is a local restriction: one old
party absorbs the scalar into its identity matrix. -/
theorem restricts_contractCenter_embedOld [Fintype J] [Nonempty J]
    (T : Tensor.{u,v,w} k J) (ξ : (embedOld T).Basis none → k) :
    Restricts T (contractCenter (embedOld T) ξ) := by
  classical
  let p : J := Classical.choice inferInstance
  let L (j : J) (c b : T.Basis j) : k :=
    if c = b then (if j = p then ξ PUnit.unit else 1) else 0
  refine ⟨L, ?_⟩
  funext x
  change (j : J) → T.Basis j at x
  change (∑ b, (∏ j, L j (x j) (b j)) * T.coeff b) =
    ∑ t : PUnit.{w+1}, ξ t * T.coeff x
  rw [Finset.sum_eq_single x, Fintype.sum_unique]
  · simp [L, Finset.prod_ite_eq']
  · intro b _ hb
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ b j := Classical.not_forall.mp (fun he ↦ hb (funext he).symm)
    rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [L, hj]), zero_mul]
  · simp

/-- A general covector on the center leg of an old tensor times an extended
tensor leaves the old tensor intact. -/
theorem contractCenter_old_product (T : Tensor.{u,v,w} k J)
    (U : Tensor.{u,v,w'} k (Option J)) (ξ : (tensorProduct (embedOld T) U).Basis none → k) :
    contractCenter (tensorProduct (embedOld T) U) ξ =
      tensorProduct T (contractCenter U (fun y ↦ ξ (PUnit.unit, y))) := by
  classical
  unfold contractCenter tensorProduct embedOld
  congr 1
  funext x
  rw [Fintype.sum_prod_type]
  simp only [Fintype.sum_unique, Finset.mul_sum, withCenter, mul_left_comm]
  apply Finset.sum_congr rfl
  intro y _
  congr 2
  apply congrArg U.coeff
  funext j
  cases j <;> rfl

end WireTensor

end VPVNP
end Computability
end OAI
