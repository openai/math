import OAI.Computability.VPVNP.WireSpectrum
import OAI.Computability.VPVNP.StarTensor

/-!
# Moving local tensor factors to a common party set

Under the placement of roles at parties used in Lemma 2.3 of *VP and VNP differ
over every field*, independent linear maps on the original roles still act
locally. At a party that carries several roles their matrix entries multiply.
Regrouping tensor products, the unit tensor and zero arrays also commute with
placement.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace WireTensor

universe u v w
variable {k : Type u} {J : Type v} {R : Type} [Fintype R] [Fintype J]

/-- Place the tensor's original factors on the specified parties. -/
noncomputable def placeTensor (p : R → J) (T : Tensor.{u,0,w} k R) : Tensor.{u,v,w} k J :=
  placedTensor p T.Basis T.coeff

/-- A global assignment of the placed indices is the same as an assignment of
the original indices, including when several roles share a party. -/
def placedAssignmentEquiv (p : R → J) (B : R → Type w) :
    ((r : R) → B r) ≃ ((j : J) → (r : R) → j = p r → B r) where
  toFun x _ r _ := x r
  invFun y r := y (p r) r rfl
  left_inv _ := rfl
  right_inv y := by
    funext j r h
    subst j
    rfl

section LinearMaps
variable [CommSemiring k]

/-- Local restrictions on the original roles act on their placed factors by
taking the product of the matrix entries assigned to each party. -/
theorem Restricts.placeTensor {T U : Tensor.{u,0,w} k R} (h : Restricts T U) (p : R → J) :
    Restricts (placeTensor p T) (placeTensor p U) := by
  classical
  obtain ⟨L, hL⟩ := h
  let M (j : J) (c : (r : R) → j = p r → U.Basis r)
      (b : (r : R) → j = p r → T.Basis r) :=
    ∏ r, if h : j = p r then L r (c r h) (b r h) else 1
  refine ⟨M, ?_⟩
  funext c
  let e := placedAssignmentEquiv p T.Basis
  let c₀ := fun r ↦ c (p r) r rfl
  refine Eq.trans ?_ (congrFun hL c₀)
  change (∑ b : (j : J) → (r : R) → j = p r → T.Basis r, (∏ j, M j (c j) (b j)) * T.coeff (fun r ↦ b (p r) r rfl)) =
    ∑ b : (r : R) → T.Basis r, (∏ r, L r (c₀ r) (b r)) * T.coeff b
  apply Fintype.sum_equiv e.symm
  intro b
  change (∏ j, M j (c j) (b j)) * T.coeff (fun r ↦ b (p r) r rfl) =
    (∏ r, L r (c₀ r) (b (p r) r rfl)) * T.coeff (fun r ↦ b (p r) r rfl)
  congr 1
  unfold M
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro r _
  rw [Finset.prod_eq_single (p r)]
  · simp [c₀]
  · intro j _ hj
    simp [hj]
  · simp

/-- Placement respects parallel tensor products up to local basis bijections. -/
theorem placeTensor_tensorProduct (p : R → J) (T U : Tensor.{u,0,w} k R) :
    Restricts (placeTensor p (tensorProduct T U)) (tensorProduct (placeTensor p T) (placeTensor p U)) ∧
    Restricts (tensorProduct (placeTensor p T) (placeTensor p U)) (placeTensor p (tensorProduct T U)) := by
  let e (j : J) :
      ((r : R) → j = p r → T.Basis r) × ((r : R) → j = p r → U.Basis r) ≃
        ((r : R) → j = p r → T.Basis r × U.Basis r) :=
    { toFun := fun z r h ↦ (z.1 r h, z.2 r h)
      invFun := fun z ↦ (fun r h ↦ (z r h).1, fun r h ↦ (z r h).2)
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  exact restricts_of_reindex e (fun _ ↦ rfl)

/-- Placing a unit tensor gives a unit tensor, up to local basis bijections. -/
theorem placeTensor_unit (p : R → J) :
    Restricts (unit : Tensor.{u,v,w} k J) (placeTensor p (unit : Tensor.{u,0,w} k R)) ∧
    Restricts (placeTensor p (unit : Tensor.{u,0,w} k R)) (unit : Tensor.{u,v,w} k J) := by
  apply restricts_of_reindex (fun j ↦ Equiv.equivPUnit ((r : R) → j = p r → PUnit))
  intro _
  rfl

omit [Fintype J] in
/-- The placed array vanishes exactly when its original array vanishes. -/
theorem placeTensor_coeff_eq_zero_iff (p : R → J) (T : Tensor.{u,0,w} k R) :
    (placeTensor p T).coeff = 0 ↔ T.coeff = 0 := by
  constructor
  · intro h
    funext x
    exact congrFun h (fun _ r _ ↦ x r)
  · intro h
    funext x
    exact congrFun h (fun r ↦ x (p r) r rfl)

/-- Placing the endpoint factors of a wire gives the wire on their image parties,
including the case where the two endpoints coincide. -/
theorem placeTensor_wire (p : R → J) (a b : R) (I : Type w) [Fintype I] :
    Restricts (placeTensor p (wire (k := k) a b I)) (wire (p a) (p b) I) ∧
    Restricts (wire (k := k) (p a) (p b) I) (placeTensor p (wire a b I)) := by
  let e (j : J) : ((j = p a → I) × (j = p b → I)) ≃
      ((r : R) → j = p r → (r = a → I) × (r = b → I)) :=
    { toFun := fun x r h ↦ (fun h₁ ↦ x.1 (h.trans (congrArg p h₁)),
                              fun h₂ ↦ x.2 (h.trans (congrArg p h₂)))
      invFun := fun y ↦ (fun h ↦ (y a h).1 rfl, fun h ↦ (y b h).2 rfl)
      left_inv := fun _ ↦ rfl
      right_inv := by
        intro y
        funext r h
        apply Prod.ext
        · funext ha
          subst r
          rfl
        · funext hb
          subst r
          rfl }
  exact restricts_of_reindex e (fun _ ↦ rfl)

end LinearMaps

section Values

variable {𝕜 : Type u} [Field 𝕜] (F : SpectralPoint 𝕜 J)

namespace SpectralPoint

/-- The spectral value of a placed tensor product is multiplicative. -/
theorem value_placed_tensorProduct (p : R → J) (T U : Tensor.{u,0,0} 𝕜 R) :
    F.value (placeTensor p (tensorProduct T U)) = F.value (placeTensor p T) * F.value (placeTensor p U) :=
  (F.value_eq_of_mutual (placeTensor_tensorProduct p T U)).trans (F.value_tensorProduct _ _)

/-- Placing all factors of a tensor power gives the corresponding power of
the placed tensor's spectral value. -/
theorem value_placed_tensorPowerFin (p : R → J) (n : ℕ) (T : Tensor.{u,0,0} 𝕜 R) :
    F.value (placeTensor p (tensorPowerFin n T)) = F.value (placeTensor p T) ^ n := by
  let Ts (_ : Fin n) := placeTensor p T
  let e (j : J) : (Fin n → (r : R) → j = p r → T.Basis r) ≃
      ((r : R) → j = p r → Fin n → T.Basis r) :=
    { toFun := fun x r h i ↦ x i r h
      invFun := fun x i r h ↦ x r h i
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have h : Restricts (placeTensor p (tensorPowerFin n T)) (tensorFamilyProduct Ts) ∧
      Restricts (tensorFamilyProduct Ts) (placeTensor p (tensorPowerFin n T)) :=
    restricts_of_reindex e (fun _ ↦ rfl)
  rw [F.value_eq_of_mutual h, F.value_tensorFamilyProduct]
  simp [Ts]

end SpectralPoint
end Values
end WireTensor

end VPVNP
end Computability
end OAI
