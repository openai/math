import OAI.Computability.VPVNP.WireTensor

/-!
# Adding a center to a tensor

In the star construction of Theorem 2.4, the added party holds one end of
every wire. Its product basis is indexed by the full tuple of leaf indices.
A covector at the center can therefore specify the entries of an arbitrary
old-party tensor independently.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v w

namespace WireTensor

variable {k : Type u} {J : Type v}

/-- Extend an old tuple of indices by an index for the additional party. -/
def withCenter {B : Option J → Type w} (c : B none) (x : (j : J) → B (some j)) :
    (t : Option J) → B t
  | none => c
  | some j => x j

/-- Embed an old tensor by using a one-dimensional factor at the center. -/
def embedOld (T : Tensor.{u,v,w} k J) : Tensor.{u,v,w} k (Option J) where
  Basis
    | none => PUnit
    | some j => T.Basis j
  finiteBasis
    | none => inferInstance
    | some j => T.finiteBasis j
  coeff x := T.coeff (fun j ↦ x (some j))

/-- Evaluate a covector on the center leg while keeping all the old legs. -/
def contractCenter [CommSemiring k] (T : Tensor.{u,v,w} k (Option J))
    (ξ : T.Basis none → k) : Tensor.{u,v,w} k J where
  Basis j := T.Basis (some j)
  finiteBasis j := T.finiteBasis (some j)
  coeff x := ∑ c, ξ c * T.coeff (withCenter c x)

/-- The basis of a star of wires. The center stores a tuple and leaf `j`
stores only its component at `j`. -/
def starBasis (I : J → Type v) : Option J → Type v
  | none => (j : J) → I j
  | some j => I j

/-- Equality wires from the center to every old party, in their product basis. -/
noncomputable def starTensor [Fintype J] [Zero k] [One k]
    (I : J → Type v) [∀ j, Fintype (I j)] : Tensor k (Option J) where
  Basis := starBasis I
  finiteBasis
    | none => by classical exact Pi.instFintype
    | some j => inferInstanceAs (Fintype (I j))
  coeff x := by
    classical exact if x none = fun j ↦ x (some j) then 1 else 0

/-- A single unrestricted covector on the center of the star realizes any
coefficient array in the indicated local dimensions. -/
theorem contractCenter_starTensor [Fintype J] [CommSemiring k]
    (I : J → Type v) [b : ∀ j, Fintype (I j)] (T : Array k I) :
    contractCenter (starTensor I) T = Tensor.mk I b T := by
  classical
  unfold contractCenter
  dsimp only [starTensor, starBasis, withCenter]
  congr 1
  funext x
  rw [Finset.sum_eq_single x]
  · simp
  · intro c _ hc
    simp [hc]
  · intro h
    exact (h (Finset.mem_univ _)).elim

/-- A tensor power with its copies indexed by `Fin n` and their local legs
grouped at each party. -/
def tensorPowerFin [CommMonoid k] (n : ℕ) (T : Tensor.{u,v,w} k J) :
    Tensor.{u,v,w} k J where
  Basis j := Fin n → T.Basis j
  finiteBasis j := inferInstanceAs (Fintype (Fin n → T.Basis j))
  coeff x := ∏ a, T.coeff (fun j ↦ x j a)


private def starNetworkBasisEquiv (I : J → Type v) (t : Option J) :
    starBasis I t ≃ (((j : J) → t = none → I j) × ((j : J) → t = some j → I j)) :=
  match t with
  | none =>
    { toFun := fun c ↦ ⟨fun j _ ↦ c j, fun _ h ↦ nomatch h⟩
      invFun := fun x j ↦ x.1 j rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ by
        apply Prod.ext
        · rfl
        · funext j h; exact nomatch h }
  | some i =>
    { toFun := fun c ↦ ⟨(fun _ h ↦ nomatch h), fun j h ↦ cast (congrArg I (Option.some.inj h)) c⟩
      invFun := fun x ↦ x.2 i rfl
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ by
        apply Prod.ext
        · funext j h; exact nomatch h
        · funext j h
          obtain rfl := Option.some.inj h
          rfl }

/-- The tuple-indexed star is the wire network joining the center to each
leaf, up to invertible local changes of basis. -/
theorem starTensor_wireNetwork [Fintype J] [CommSemiring k]
    (I : J → Type v) [∀ j, Fintype (I j)] :
    Restricts (wireNetwork (k := k) (fun _ ↦ none) some I) (starTensor I) ∧
    Restricts (starTensor I) (wireNetwork (k := k) (fun _ ↦ none) some I) := by
  classical
  apply restricts_of_reindex (starNetworkBasisEquiv I)
  intro x
  simp only [starTensor, wireNetwork, Fintype.prod_boole]
  congr 1
  apply propext
  change (x none = fun j ↦ x (some j)) ↔ ∀ j : J, x none j = x (some j)
  exact funext_iff

private def starProductBasisEquiv (I K : J → Type v) (t : Option J) :
    starBasis (fun j ↦ I j × K j) t ≃ (starBasis I t × starBasis K t) :=
  match t with
  | none => Equiv.arrowProdEquivProdArrow J I K
  | some _ => Equiv.refl _

private theorem indicator_eq_product [MulZeroOneClass k] {P Q R : Prop}
    [Decidable P] [Decidable Q] [Decidable R] (h : P ↔ Q ∧ R) :
    (if P then (1 : k) else 0) = (if Q then 1 else 0) * (if R then 1 else 0) := by
  split_ifs <;> simp_all

/-- Multiplying two stars independently combines their two sets of wire
indices at each leaf and at the center. -/
theorem starTensor_tensorProduct [Fintype J] [CommSemiring k]
    (I K : J → Type v) [∀ j, Fintype (I j)] [∀ j, Fintype (K j)] :
    Restricts (tensorProduct (starTensor (k := k) I) (starTensor K))
      (starTensor (fun j ↦ I j × K j)) ∧
    Restricts (starTensor (k := k) (fun j ↦ I j × K j))
      (tensorProduct (starTensor I) (starTensor K)) := by
  classical
  apply restricts_of_reindex (starProductBasisEquiv I K)
  intro x
  let f : (j : J) → I j × K j := x none
  let g : (j : J) → I j × K j := fun j ↦ x (some j)
  let e := Equiv.arrowProdEquivProdArrow J I K
  have he : f = g ↔ (e f).1 = (e g).1 ∧ (e f).2 = (e g).2 :=
    e.injective.eq_iff.symm.trans Prod.ext_iff
  apply indicator_eq_product
  exact he

private def starPowerBasisEquiv (I : J → Type v) (n : ℕ) (t : Option J) :
    starBasis (fun j ↦ Fin n → I j) t ≃ (Fin n → starBasis I t) :=
  match t with
  | none => ⟨fun x a j ↦ x j a, fun x j a ↦ x a j, fun _ ↦ rfl, fun _ ↦ rfl⟩
  | some _ => Equiv.refl _

/-- The power of a star has one enlarged wire of dimension `|I j| ^ n` at
each leaf. This identifies its joint center, including the zeroth power. -/
theorem starTensor_powerFin [Fintype J] [CommSemiring k]
    (I : J → Type v) [∀ j, Fintype (I j)] (n : ℕ) :
    Restricts (tensorPowerFin n (starTensor (k := k) I))
      (starTensor (fun j ↦ Fin n → I j)) ∧
    Restricts (starTensor (k := k) (fun j ↦ Fin n → I j))
      (tensorPowerFin n (starTensor I)) := by
  classical
  apply restricts_of_reindex (starPowerBasisEquiv I n)
  intro x
  simp only [starTensor, tensorPowerFin, Fintype.prod_boole]
  congr 1
  apply propext
  change (x none = fun j ↦ x (some j)) ↔
    ∀ a : Fin n, (fun j ↦ x none j a) = fun j ↦ x (some j) a
  constructor
  · intro h a
    exact funext fun j ↦ congrFun (congrFun h j) a
  · intro h
    exact funext fun j ↦ funext fun a ↦ congrFun (h a) j

/-- Arbitrary leaf coefficients on a power of the star are realized by one
covector on its entire center leg. Its coordinates transpose the copy and
party indices. -/
theorem contractCenter_starPowerFin [Fintype J] [CommSemiring k]
    (I : J → Type v) [∀ j, Fintype (I j)] (n : ℕ) (T : Array k (fun j ↦ Fin n → I j)) :
    ∃ ξ : (tensorPowerFin n (starTensor (k := k) I)).Basis none → k,
      (contractCenter (tensorPowerFin n (starTensor I)) ξ).coeff = T := by
  classical
  refine ⟨fun c ↦ T (fun j a ↦ c a j), ?_⟩
  funext x
  change (j : J) → Fin n → I j at x
  simp only [contractCenter, tensorPowerFin, starTensor, withCenter, starBasis]
  let c : Fin n → (j : J) → I j := fun a j ↦ x j a
  rw [Finset.sum_eq_single c]
  · simp [c]
  · intro b _ hb
    have h : ¬ ∀ a : Fin n, b a = fun j ↦ x j a := fun H ↦ hb (funext H)
    obtain ⟨a, ha⟩ := Classical.not_forall.mp h
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ a) (by simp only [ha, ↓reduceIte]))
  · intro h
    exact (h (Finset.mem_univ _)).elim

end WireTensor

end VPVNP
end Computability
end OAI
