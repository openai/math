import Mathlib.Data.Matrix.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Multipartite tensors and local restrictions

Finite coefficient arrays implement the restriction preorder of Section 2 of
*VP and VNP differ over every field*. Each party has its own finite basis. A
local restriction independently applies one matrix at each party. The ordinary
sum of arrays in the same bases differs from the direct sum, which uses separate
local coordinate blocks at every party.
-/

namespace OAI
namespace Computability
namespace VPVNP

universe u v w w'

namespace WireTensor

/-- A scalar for every simultaneous choice of one basis index at each party. -/
abbrev Array (k : Type u) {J : Type v} (B : J → Type w) := ((j : J) → B j) → k

/-- A tensor given by its entries in a finite basis at each party. -/
structure Tensor (k : Type u) (J : Type v) where
  /-- The basis-index type for the tensor factor at each party. -/
  Basis : J → Type w
  finiteBasis : ∀ j, Fintype (Basis j)
  /-- The coefficients of the tensor in the specified product basis. -/
  coeff : Array k Basis

attribute [instance] Tensor.finiteBasis

variable {k : Type u} {J : Type v}

/-- Apply a linear map at each party, contracting its old index against the
corresponding column of the matrix. -/
noncomputable def applyLocal [Fintype J] [CommSemiring k] {B : J → Type*} {C : J → Type*}
    [∀ j, Fintype (B j)] (L : ∀ j, C j → B j → k) (T : Array k B) : Array k C := by
  classical exact fun c ↦ ∑ b, (∏ j, L j (c j) (b j)) * T b

/-- The tensor restriction preorder, oriented from supply to demand. -/
def Restricts [Fintype J] [CommSemiring k] (Y : Tensor.{u,v,w} k J) (X : Tensor.{u,v,w'} k J) : Prop :=
  ∃ L : ∀ j, X.Basis j → Y.Basis j → k, applyLocal L Y.coeff = X.coeff

/-- Product with parallel factors regrouped at each party. -/
def tensorProduct [Mul k] (T : Tensor.{u,v,w} k J) (U : Tensor.{u,v,w'} k J) : Tensor k J where
  Basis j := T.Basis j × U.Basis j
  finiteBasis _ := inferInstance
  coeff p := T.coeff (fun j ↦ (p j).1) * U.coeff (fun j ↦ (p j).2)

/-- The simple unit tensor with singleton bases. -/
def unit [One k] : Tensor.{u,v,w} k J where
  Basis _ := PUnit
  finiteBasis _ := inferInstance
  coeff _ := 1

/-- The all-parties equality tensor. -/
noncomputable def diagonal [Zero k] [One k] (I : Type w) [Fintype I] : Tensor k J where
  Basis _ := I
  finiteBasis _ := inferInstance
  coeff x := by classical exact if ∃ i, ∀ j, x j = i then 1 else 0

/-- The direct sum includes the first array in the left block and the second
array in the right block. The coefficient vanishes on every mixed block. -/
noncomputable def directSum [Fintype J] [CommSemiring k]
    (T : Tensor.{u,v,w} k J) (U : Tensor.{u,v,w'} k J) : Tensor k J where
  Basis j := T.Basis j ⊕ U.Basis j
  finiteBasis _ := inferInstance
  coeff := by
    classical
    exact applyLocal (fun _ i b ↦ if i = Sum.inl b then 1 else 0) T.coeff +
      applyLocal (fun _ i b ↦ if i = Sum.inr b then 1 else 0) U.coeff

/-- A wire has one endpoint index at `a`, one at `b`, and trivial factors at
other parties. The proof-indexed functions keep both local factors even when
the two endpoints coincide. -/
noncomputable def wire [Zero k] [One k] (a b : J) (I : Type w) [Fintype I] : Tensor k J where
  Basis j := (j = a → I) × (j = b → I)
  finiteBasis j := by classical exact inferInstance
  coeff x := by classical exact if (x a).1 rfl = (x b).2 rfl then 1 else 0

section Restrictions

variable [Fintype J] [CommSemiring k]

/-- Selecting one old coordinate at each party pulls back the coefficient array. -/
theorem applyLocal_pullback {B C : J → Type*} [∀ j, Fintype (B j)]
    [∀ j, DecidableEq (B j)] (f : ∀ j, C j → B j) (T : Array k B) :
    applyLocal (fun j c b ↦ if f j c = b then 1 else 0) T =
      fun c ↦ T (fun j ↦ f j (c j)) := by
  classical
  funext c
  simp [applyLocal, Fintype.prod_boole, ← funext_iff, ite_mul]

theorem applyLocal_id {B : J → Type*} [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]
    (T : Array k B) :
    applyLocal (fun _ c b ↦ if c = b then 1 else 0) T = T :=
  applyLocal_pullback (fun _ ↦ id) T

/-- Composing two local restrictions multiplies the matrices at each party. -/
theorem applyLocal_comp {A B C : J → Type*} [∀ j, Fintype (A j)] [∀ j, Fintype (B j)]
    (M : ∀ j, C j → B j → k) (L : ∀ j, B j → A j → k) (T : Array k A) :
    applyLocal M (applyLocal L T) =
      applyLocal (fun j c a ↦ ∑ b, M j c b * L j b a) T := by
  classical
  funext c
  simp only [applyLocal, Fintype.prod_sum, Finset.prod_mul_distrib, Finset.mul_sum,
    Finset.sum_mul, mul_assoc]
  rw [Finset.sum_comm]

theorem Restricts.refl (T : Tensor k J) : Restricts T T := by
  classical
  exact ⟨_, applyLocal_id T.coeff⟩

theorem Restricts.trans {T U V : Tensor k J} (hTU : Restricts T U) (hUV : Restricts U V) :
    Restricts T V := by
  obtain ⟨L, hL⟩ := hTU
  obtain ⟨M, hM⟩ := hUV
  exact ⟨_, (applyLocal_comp M L T.coeff).symm.trans (by rw [hL, hM])⟩

/-- Relabeling the finite bases at every party gives mutual local restrictions. -/
theorem restricts_of_reindex {T U : Tensor k J} (e : ∀ j, U.Basis j ≃ T.Basis j)
    (h : ∀ c, U.coeff c = T.coeff (fun j ↦ e j (c j))) :
    Restricts T U ∧ Restricts U T := by
  classical
  constructor
  · exact ⟨_, (applyLocal_pullback (fun j ↦ e j) T.coeff).trans (funext h).symm⟩
  · refine ⟨_, (applyLocal_pullback (fun j ↦ (e j).symm) U.coeff).trans ?_⟩
    funext b
    simp [h]

end Restrictions

section Products

variable [Fintype J] [CommSemiring k]

/-- Independent restrictions of two tensors combine after the parallel local
factors are regrouped, by taking their Kronecker products at each party. -/
theorem Restricts.tensorProduct {T T' U U' : Tensor k J} (hT : Restricts T T')
    (hU : Restricts U U') : Restricts (tensorProduct T U) (tensorProduct T' U') := by
  classical
  obtain ⟨L, hL⟩ := hT
  obtain ⟨M, hM⟩ := hU
  refine ⟨fun j p q ↦ L j p.1 q.1 * M j p.2 q.2, ?_⟩
  funext c
  let f (b : ∀ j, T.Basis j) := (∏ j, L j (c j).1 (b j)) * T.coeff b
  let g (b : ∀ j, U.Basis j) := (∏ j, M j (c j).2 (b j)) * U.coeff b
  change (∑ b : ∀ j, T.Basis j × U.Basis j,
    (∏ j, L j (c j).1 (b j).1 * M j (c j).2 (b j).2) *
      (T.coeff (fun j ↦ (b j).1) * U.coeff (fun j ↦ (b j).2))) =
    T'.coeff (fun j ↦ (c j).1) * U'.coeff (fun j ↦ (c j).2)
  rw [← hL, ← hM]
  change _ = (∑ b, f b) * ∑ b, g b
  calc
    _ = ∑ p : (∀ j, T.Basis j) × (∀ j, U.Basis j), f p.1 * g p.2 := by
      apply Fintype.sum_equiv (Equiv.arrowProdEquivProdArrow J T.Basis U.Basis)
      intro b
      rw [Finset.prod_mul_distrib, mul_mul_mul_comm]
      rfl
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul_sum]

end Products

section DirectSum
variable [Fintype J] [CommSemiring k]

/-- Coefficients on the first block of the direct sum. -/
theorem directSum_coeff_inl [Nonempty J] (T : Tensor.{u,v,w} k J) (U : Tensor.{u,v,w'} k J)
    (x : (j : J) → T.Basis j) :
    (directSum T U).coeff (fun j ↦ Sum.inl (x j)) = T.coeff x := by
  classical
  simp [directSum, applyLocal, Fintype.prod_boole, ← funext_iff, ite_mul]

/-- Coefficients on the second block of the direct sum. -/
theorem directSum_coeff_inr [Nonempty J] (T : Tensor.{u,v,w} k J) (U : Tensor.{u,v,w'} k J)
    (x : (j : J) → U.Basis j) :
    (directSum T U).coeff (fun j ↦ Sum.inr (x j)) = U.coeff x := by
  classical
  simp [directSum, applyLocal, Fintype.prod_boole, ← funext_iff, ite_mul]

/-- An entry using the left block at one party and the right block at another is zero. -/
theorem directSum_coeff_mixed (T : Tensor.{u,v,w} k J) (U : Tensor.{u,v,w'} k J)
    (x : (j : J) → T.Basis j ⊕ U.Basis j) {a b : J} {i : T.Basis a} {l : U.Basis b}
    (ha : x a = Sum.inl i) (hb : x b = Sum.inr l) :
    (directSum T U).coeff x = 0 := by
  classical
  have hleft (y : (j : J) → T.Basis j) : ¬ ∀ j, x j = Sum.inl (y j) := by
    intro h
    simpa [hb] using h b
  have hright (y : (j : J) → U.Basis j) : ¬ ∀ j, x j = Sum.inr (y j) := by
    intro h
    simpa [ha] using h a
  simp [directSum, applyLocal, Fintype.prod_boole, hleft, hright]

/-- A local map on a direct sum acts separately on the two blocks, after which
the resulting arrays are added in the ordinary sense. -/
theorem applyLocal_directSum {C : J → Type*} (T : Tensor.{u,v,w} k J)
    (U : Tensor.{u,v,w'} k J) (L : ∀ j, C j → (T.Basis j ⊕ U.Basis j) → k) :
    applyLocal L (directSum T U).coeff =
      applyLocal (fun j c b ↦ L j c (.inl b)) T.coeff +
      applyLocal (fun j c b ↦ L j c (.inr b)) U.coeff := by
  classical
  funext c
  simp only [directSum, applyLocal, Pi.add_apply, Fintype.prod_boole, ite_mul,
    one_mul, zero_mul, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_ite, mul_zero]
  congr 1 <;> rw [Finset.sum_comm] <;> apply Finset.sum_congr rfl <;> intro x hx <;>
    simp [← funext_iff]

/-- Merging corresponding coordinates of the two blocks realizes the
ordinary sum as a restriction of the direct sum. -/
theorem directSum_restricts_add {B : J → Type w} [b : ∀ j, Fintype (B j)] (T U : Array k B) :
    Restricts (directSum (Tensor.mk B b T) (Tensor.mk B b U)) (Tensor.mk B b (T + U)) := by
  classical
  let L (j : J) (c : B j) (p : B j ⊕ B j) : k := if c = p.elim id id then 1 else 0
  refine ⟨L, ?_⟩
  refine (applyLocal_directSum (C := B) (Tensor.mk B b T) (Tensor.mk B b U) L).trans ?_
  change applyLocal (fun j (c x : B j) ↦ if c = x then 1 else 0) T +
      applyLocal (fun j (c x : B j) ↦ if c = x then 1 else 0) U = T + U
  funext c
  simp [applyLocal, Fintype.prod_boole, ← funext_iff, ite_mul]

end DirectSum

/-- Local restrictions on the two summands act independently on the corresponding
blocks at each party. -/
theorem directSum_restricts [Fintype J] [CommSemiring k]
    {T : Tensor k J} {U : Tensor k J} {T' : Tensor k J} {U' : Tensor k J} (hT : Restricts T T') (hU : Restricts U U') :
    Restricts (directSum T U) (directSum T' U') := by
  classical
  obtain ⟨L, hL⟩ := hT
  obtain ⟨M, hM⟩ := hU
  let K (j : J) (c : T'.Basis j ⊕ U'.Basis j) (b : T.Basis j ⊕ U.Basis j) : k :=
    match c, b with
    | .inl x, .inl y => L j x y
    | .inr x, .inr y => M j x y
    | _, _ => 0
  refine ⟨K, (applyLocal_directSum (C := fun j ↦ T'.Basis j ⊕ U'.Basis j) T U K).trans ?_⟩
  simp only [directSum, ← hL, ← hM, applyLocal_comp]
  congr 1
  · apply congrArg (fun m ↦ applyLocal m T.coeff)
    funext j c b
    cases c <;> simp [K, ite_mul]
  · apply congrArg (fun m ↦ applyLocal m U.coeff)
    funext j c b
    cases c <;> simp [K, ite_mul]

section Summand
variable [Fintype J] [CommSemiring k] [Nonempty J]

/-- Projection onto the first coordinate block restricts a direct sum to its first summand. -/
theorem directSum_restricts_left (T : Tensor.{u,v,w} k J) (U : Tensor.{u,v,w'} k J) :
    Restricts (directSum T U) T := by
  classical
  let L (j : J) (c : T.Basis j) : T.Basis j ⊕ U.Basis j → k :=
    Sum.elim (fun b ↦ if c = b then 1 else 0) (fun _ ↦ 0)
  refine ⟨L, (applyLocal_directSum (C := T.Basis) T U L).trans ?_⟩
  change applyLocal (fun j (c x : T.Basis j) ↦ if c = x then 1 else 0) T.coeff +
      applyLocal (fun _ _ _ ↦ 0) U.coeff = T.coeff
  funext c
  simp [applyLocal, Fintype.prod_boole, ← funext_iff, ite_mul]

/-- Projection onto the second coordinate block restricts a direct sum to its second summand. -/
theorem directSum_restricts_right (T : Tensor.{u,v,w} k J) (U : Tensor.{u,v,w'} k J) :
    Restricts (directSum T U) U := by
  classical
  let L (j : J) (c : U.Basis j) : T.Basis j ⊕ U.Basis j → k :=
    Sum.elim (fun _ ↦ 0) (fun b ↦ if c = b then 1 else 0)
  refine ⟨L, (applyLocal_directSum (C := U.Basis) T U L).trans ?_⟩
  change applyLocal (fun _ _ _ ↦ 0) T.coeff +
      applyLocal (fun j (c x : U.Basis j) ↦ if c = x then 1 else 0) U.coeff = U.coeff
  funext c
  simp [applyLocal, Fintype.prod_boole, ← funext_iff, ite_mul]

end Summand

/-- Move the factors indexed by `R` to the prescribed parties, grouping all
factors at the same party into one local basis. -/
noncomputable def placedTensor {R : Type*} [Fintype R] (place : R → J) (B : R → Type w)
    [∀ r, Fintype (B r)] (T : Array k B) : Tensor k J where
  Basis j := (r : R) → j = place r → B r
  finiteBasis _ := by classical exact inferInstance
  coeff x := T (fun r ↦ x (place r) r rfl)

/-- The tensor enforcing equality of the indices at both ends of every edge.
The local basis lists its incoming and outgoing endpoint indices separately. -/
noncomputable def wireNetwork [CommSemiring k] {E : Type*} [Fintype E]
    (a b : E → J) (I : E → Type w) [∀ e, Fintype (I e)] : Tensor k J where
  Basis j := ((e : E) → j = a e → I e) × ((e : E) → j = b e → I e)
  finiteBasis _ := by classical exact inferInstance
  coeff x := by classical exact ∏ e, if (x (a e)).1 e rfl = (x (b e)).2 e rfl then 1 else 0

/-- Encode a global assignment of indices to edges as the local half-wire
assignments at a party. This is the point on the diagonal of the wire tensor. -/
def edgeAssignment {E : Type*} (a b : E → J) {I : E → Type w} (x : (e : E) → I e) (j : J) :
    ((e : E) → j = a e → I e) × ((e : E) → j = b e → I e) :=
  ⟨fun e _ ↦ x e, fun e _ ↦ x e⟩

private def endpointEquiv {E : Type*} (a b : E → J) (I : E → Type w) :
    (((e : E) → I e) × ((e : E) → I e)) ≃
      ((j : J) → ((e : E) → j = a e → I e) × ((e : E) → j = b e → I e)) where
  toFun xy _ := ⟨fun e _ ↦ xy.1 e, fun e _ ↦ xy.2 e⟩
  invFun x := ⟨fun e ↦ (x (a e)).1 e rfl, fun e ↦ (x (b e)).2 e rfl⟩
  left_inv _ := rfl
  right_inv x := by
    funext j
    apply Prod.ext
    · funext e h
      subst j
      rfl
    · funext e h
      subst j
      rfl

open scoped Classical in
/-- Contraction of the equality network leaves exactly one sum per edge,
including when there are parallel edges or repeated parties. -/
theorem applyLocal_wireNetwork [Fintype J] [CommSemiring k] {E : Type*} [Fintype E]
    (a b : E → J) (I : E → Type w) [∀ e, Fintype (I e)] {C : J → Type*}
    (L : ∀ j, C j → (wireNetwork (k := k) a b I).Basis j → k) (c : (j : J) → C j) :
    applyLocal L (wireNetwork a b I).coeff c =
      ∑ x : (e : E) → I e, ∏ j, L j (c j) (edgeAssignment a b x j) := by
  classical
  unfold applyLocal
  let f := fun z : (j : J) → (wireNetwork (k := k) a b I).Basis j ↦
    (∏ j, L j (c j) (z j)) * (wireNetwork (k := k) a b I).coeff z
  change (∑ z, f z) = _
  calc
    _ = ∑ xy, f (endpointEquiv a b I xy) := ((endpointEquiv a b I).sum_comp f).symm
    _ = _ := ?_
  dsimp only [f]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro x _
  simp [wireNetwork, endpointEquiv, Fintype.prod_boole, ← funext_iff, mul_ite, edgeAssignment]

end WireTensor

namespace WireTensor

variable {k : Type u} {J : Type v} [Fintype J] [Nonempty J]

/-- A nonzero coefficient gives a restriction to the unit tensor. Each party
selects its coordinate, and one party divides by the selected coefficient. -/
theorem restricts_unit_of_ne_zero [Field k] (T : Tensor.{u,v,w} k J) (hT : T.coeff ≠ 0) :
    Restricts T (unit.{u,v,0} (k := k) (J := J)) := by
  classical
  obtain ⟨p, hp⟩ : ∃ p, T.coeff p ≠ 0 :=
    Classical.not_forall.mp (fun h ↦ hT (funext h))
  let a : J := Classical.choice inferInstance
  let L (j : J) (_ : PUnit) (i : T.Basis j) : k :=
    if i = p j then (if j = a then (T.coeff p)⁻¹ else 1) else 0
  refine ⟨L, ?_⟩
  funext c
  change (∑ b : (j : J) → T.Basis j, (∏ j, L j (c j) (b j)) * T.coeff b) = 1
  rw [Finset.sum_eq_single p]
  · simpa [L, Finset.prod_ite_eq'] using inv_mul_cancel₀ hp
  · intro b _ hbp
    obtain ⟨j, hj⟩ : ∃ j, b j ≠ p j := Classical.not_forall.mp (fun h ↦ hbp (funext h))
    have hprod : (∏ j, L j (c j) (b j)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ j) (by simp [L, hj])
    rw [hprod, zero_mul]
  · simp

/-- The diagonal indexed by all tuples of basis coordinates restricts to
the tensor, giving the product of the local dimensions as a rank bound.
One party contributes the selected coefficient, and all parties check their
component of the tuple. -/
theorem diagonal_restricts_of_card [CommSemiring k] (T : Tensor.{u,v,w} k J) :
    Restricts (diagonal (Fin (∏ j, Fintype.card (T.Basis j)))) T := by
  classical
  let I := Fin (∏ j, Fintype.card (T.Basis j))
  let e : ((j : J) → T.Basis j) ≃ I := Fintype.equivFinOfCardEq Fintype.card_pi
  let a : J := Classical.choice inferInstance
  let L (j : J) (i : T.Basis j) (s : I) : k :=
    if i = e.symm s j then (if j = a then T.coeff (e.symm s) else 1) else 0
  refine ⟨L, ?_⟩
  funext p
  simp only [applyLocal, diagonal]
  rw [Finset.sum_eq_single (fun _ ↦ e p)]
  · simp [L, Finset.prod_ite_eq']
  · intro x _ hx
    split_ifs with hdiag
    · obtain ⟨s, hs⟩ := hdiag
      obtain ⟨j, hj⟩ : ∃ j, p j ≠ e.symm s j := by
        apply Classical.not_forall.mp
        intro he
        have hep : e p = s := by rw [funext he, e.apply_symm_apply]
        exact hx (funext (fun i ↦ (hs i).trans hep.symm))
      have hprod : (∏ j, L j (p j) (x j)) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ j) (by simp [L, hs j, hj])
      rw [hprod, zero_mul]
    · simp
  · intro h
    exact (h (Finset.mem_univ _)).elim

end WireTensor

namespace WireTensor

private theorem nonpos_of_nat_mul_bounded {x C : ℝ} (h : ∀ m : ℕ, (m : ℝ) * x ≤ C) :
    x ≤ 0 := by
  by_contra! hx
  obtain ⟨m, hm⟩ := exists_nat_gt (C / x)
  exact (not_lt_of_ge (h m)) ((div_lt_iff₀ hx).mp hm)

/-- In Section 2.1, the monotonicity and multiplicativity of the value on
integer-dimensional wires force the power law. For each power of `q`, compare
the adjacent powers of two and then apply the same comparison to their images. -/
theorem monotone_dimension_power_law (f : ℕ →* ℝ) (hf : Monotone f) {q : ℕ} (hq : 0 < q) :
    f q = (q : ℝ) ^ (Real.log (f 2) / Real.log 2) := by
  have hf_one (i : ℕ) (hi : 0 < i) : 1 ≤ f i := by
    simpa using hf (show 1 ≤ i from hi)
  have hf_pos (i : ℕ) (hi : 0 < i) : 0 < f i := zero_lt_one.trans_le (hf_one i hi)
  have hb : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hd : 0 ≤ Real.log (f 2) := Real.log_nonneg (hf_one _ (by decide))
  have hlog {i j : ℕ} (hi : 0 < i) (hij : i ≤ j) : Real.log i ≤ Real.log j :=
    Real.log_le_log (by exact_mod_cast hi) (by exact_mod_cast hij)
  have hbounds (m : ℕ) :
      (m : ℝ) * (Real.log (f q) * Real.log 2 - Real.log q * Real.log (f 2)) ≤
          Real.log (f 2) * Real.log 2 ∧
      (m : ℝ) * (Real.log q * Real.log (f 2) - Real.log (f q) * Real.log 2) ≤
          Real.log (f 2) * Real.log 2 := by
    let r := Nat.log 2 (q ^ m)
    have hlo : 2 ^ r ≤ q ^ m := Nat.pow_log_le_self 2 (pow_ne_zero _ hq.ne')
    have hhi : q ^ m ≤ 2 ^ r.succ := (Nat.lt_pow_succ_log_self (by decide) _).le
    have hlo_log := hlog (by positivity) hlo
    have hhi_log := hlog (pow_pos hq _) hhi
    have hlo_image := Real.log_le_log (hf_pos _ (by positivity)) (hf hlo)
    have hhi_image := Real.log_le_log (hf_pos _ (pow_pos hq _)) (hf hhi)
    simp only [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, Nat.cast_succ] at hlo_log hhi_log
    simp only [map_pow, Real.log_pow, Nat.cast_succ] at hlo_image hhi_image
    constructor
    · linarith only [mul_le_mul_of_nonneg_right hhi_image hb.le,
        mul_le_mul_of_nonneg_right hlo_log hd]
    · linarith only [mul_le_mul_of_nonneg_right hlo_image hb.le,
        mul_le_mul_of_nonneg_right hhi_log hd]
  have hcross : Real.log (f q) * Real.log 2 = Real.log q * Real.log (f 2) :=
    le_antisymm (sub_nonpos.mp (nonpos_of_nat_mul_bounded fun m ↦ (hbounds m).1))
      (sub_nonpos.mp (nonpos_of_nat_mul_bounded fun m ↦ (hbounds m).2))
  rw [Real.rpow_def_of_pos (by exact_mod_cast hq), ← Real.exp_log (hf_pos q hq)]
  congr 1
  calc
    Real.log (f q) = (Real.log q * Real.log (f 2)) / Real.log 2 :=
      (eq_div_iff hb.ne').mpr hcross
    _ = _ := by ring


section WireArithmetic

variable {k : Type u} {J : Type v}

section Wires

variable [Fintype J] [CommSemiring k]

/-- Swapping the endpoints of a wire permutes the local bases. -/
theorem wire_swap (a b : J) (I : Type*) [Fintype I] :
    Restricts (wire (k := k) a b I) (wire b a I) ∧
      Restricts (wire (k := k) b a I) (wire a b I) := by
  classical
  apply restricts_of_reindex (fun _ ↦ Equiv.prodComm _ _)
  intro z
  change (if (z b).1 rfl = (z a).2 rfl then (1 : k) else 0) =
    if (z a).2 rfl = (z b).1 rfl then 1 else 0
  rw [@eq_comm _ ((z b).1 rfl) ((z a).2 rfl)]

/-- A wire on a smaller index set is obtained by coordinate selection at its endpoints. -/
theorem wire_restricts_of_embedding (a b : J) {I K : Type*} [Fintype I] [Fintype K]
    (e : I ↪ K) : Restricts (wire (k := k) a b K) (wire a b I) := by
  classical
  let f (j : J) (z : (j = a → I) × (j = b → I)) :
      (j = a → K) × (j = b → K) := (e ∘ z.1, e ∘ z.2)
  refine ⟨_, (applyLocal_pullback f (wire (k := k) a b K).coeff).trans ?_⟩
  funext z
  simp [wire, f]

theorem wire_restricts_of_le (a b : J) {m n : ℕ} (h : m ≤ n) :
    Restricts (wire (k := k) a b (Fin n)) (wire a b (Fin m)) :=
  wire_restricts_of_embedding a b (Fin.castLEEmb h)

/-- The two coordinate components of an ordered pair give the two parallel wires. -/
theorem wire_tensorProduct (a b : J) (I K : Type*) [Fintype I] [Fintype K] :
    Restricts (wire (k := k) a b (I × K)) (tensorProduct (wire a b I) (wire a b K)) ∧
      Restricts (tensorProduct (wire (k := k) a b I) (wire a b K)) (wire a b (I × K)) := by
  classical
  let e (j : J) :
      ((j = a → I) × (j = b → I)) × ((j = a → K) × (j = b → K)) ≃
        ((j = a → I × K) × (j = b → I × K)) :=
    { toFun := fun z ↦ (fun h ↦ (z.1.1 h, z.2.1 h), fun h ↦ (z.1.2 h, z.2.2 h))
      invFun := fun z ↦ ((fun h ↦ (z.1 h).1, fun h ↦ (z.2 h).1),
                         (fun h ↦ (z.1 h).2, fun h ↦ (z.2 h).2))
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  apply restricts_of_reindex e
  intro z
  have he : (e a (z a)).1 rfl = (e b (z b)).2 rfl ↔
      (z a).1.1 rfl = (z b).1.2 rfl ∧ (z a).2.1 rfl = (z b).2.2 rfl :=
    Prod.mk.injEq _ _ _ _ |>.to_iff
  simp only [wire, tensorProduct]
  split_ifs <;> simp_all <;> contradiction

/-- Sending each copy of the unit to the matching pair of endpoint basis
vectors produces a wire of the same dimension. -/
theorem diagonal_restricts_wire (a b : J) (I : Type*) [Fintype I] :
    Restricts (diagonal (k := k) I) (wire a b I) := by
  classical
  let L (j : J) (z : (j = a → I) × (j = b → I)) (i : I) : k :=
    if (∀ h, z.1 h = i) ∧ (∀ h, z.2 h = i) then 1 else 0
  refine ⟨L, ?_⟩
  funext z
  simp only [applyLocal, diagonal, wire, L, Fintype.prod_boole]
  rw [Finset.sum_eq_single (fun _ ↦ (z a).1 rfl)]
  · have he : (∀ j, (∀ h : j = a, (z j).1 h = (z a).1 rfl) ∧
                (∀ h : j = b, (z j).2 h = (z a).1 rfl)) ↔ (z a).1 rfl = (z b).2 rfl := by
      constructor
      · exact fun h ↦ ((h b).2 rfl).symm
      · intro h j
        exact ⟨by rintro rfl; rfl, by rintro rfl; exact h.symm⟩
    have hc : ∃ i : I, ∀ _ : J, (z a).1 rfl = i := ⟨_, fun _ ↦ rfl⟩
    simp only [hc, ite_true, mul_one, he]
  · intro x _ hx
    split_ifs with hloc hdiag
    · obtain ⟨i, hi⟩ := hdiag
      exact False.elim (hx (funext (fun j ↦ (hi j).trans ((hi a).symm.trans ((hloc a).1 rfl).symm))))
    all_goals simp
  · intro h
    exact (h (Finset.mem_univ _)).elim

end Wires

section UnitWires

variable [Fintype J] [CommSemiring k]

/-- A one-dimensional wire is the simple unit, including when its endpoints coincide. -/
theorem wire_one (a b : J) :
    Restricts (unit.{u,v,0} (k := k) (J := J)) (wire a b (Fin 1)) ∧
      Restricts (wire (k := k) a b (Fin 1)) unit.{u,v,0} := by
  classical
  let (j : J) : Unique ((j = a → Fin 1) × (j = b → Fin 1)) :=
    uniqueOfSubsingleton (fun _ ↦ 0, fun _ ↦ 0)
  apply restricts_of_reindex (fun j ↦ Equiv.equivPUnit ((j = a → Fin 1) × (j = b → Fin 1)))
  intro z
  simp [wire, unit, Subsingleton.elim ((z a).1 rfl) ((z b).2 rfl)]

/-- A loop carries both endpoint indices at a single party, so its Kronecker
delta can be created by a linear map from that party's one-dimensional leg. -/
theorem unit_restricts_loop (a : J) (I : Type*) [Fintype I] :
    Restricts (unit.{u,v,0} (k := k) (J := J)) (wire a a I) := by
  classical
  let L (j : J) (z : (j = a → I) × (j = a → I)) (_ : PUnit) : k :=
    if ∀ h, z.1 h = z.2 h then 1 else 0
  refine ⟨L, ?_⟩
  funext z
  have he : (∀ j, ∀ h : j = a, (z j).1 h = (z j).2 h) ↔ (z a).1 rfl = (z a).2 rfl :=
    ⟨fun h ↦ h a rfl, fun h _ eq ↦ by subst eq; exact h⟩
  change (∑ x : J → PUnit, (∏ j, L j (z j) (x j)) * 1) = _
  rw [Fintype.sum_unique]
  simp [wire, L, Fintype.prod_boole, he]

end UnitWires

/-- Contracting the common endpoint of two wires produces the wire between
their outside endpoints. This works even when some of the three parties coincide. -/
theorem restricts_wire_triangle [Fintype J] [CommSemiring k] (a b c : J)
    (I : Type w) [Fintype I] :
    Restricts (tensorProduct (wire (k := k) a b I) (wire b c I)) (wire a c I) := by
  classical
  let ok (j : J) (z : (wire (k := k) a c I).Basis j)
      (y : (tensorProduct (wire (k := k) a b I) (wire b c I)).Basis j) : Prop :=
    (∀ h : j = a, z.1 h = y.1.1 h) ∧ (∀ h : j = b, y.1.2 h = y.2.1 h) ∧
      (∀ h : j = c, z.2 h = y.2.2 h)
  refine ⟨fun j z y ↦ if ok j z y then 1 else 0, ?_⟩
  funext z
  let y₀ (j : J) : (tensorProduct (wire (k := k) a b I) (wire b c I)).Basis j :=
    ((fun _ ↦ (z a).1 rfl, fun _ ↦ (z a).1 rfl),
     (fun _ ↦ (z c).2 rfl, fun _ ↦ (z c).2 rfl))
  have hok : (∀ j, ok j (z j) (y₀ j)) ↔ (z a).1 rfl = (z c).2 rfl := by
    refine ⟨fun h ↦ (h b).2.1 rfl, fun h j ↦ ⟨?_, ?_, ?_⟩⟩
    · rintro rfl
      rfl
    · rintro rfl
      exact h
    · rintro rfl
      rfl
  have uniqueY (y : ∀ j, (tensorProduct (wire (k := k) a b I) (wire b c I)).Basis j)
      (h : ∀ j, ok j (z j) (y j))
      (hl : (y a).1.1 rfl = (y b).1.2 rfl) (hr : (y b).2.1 rfl = (y c).2.2 rfl) :
      y = y₀ := by
    funext j
    apply Prod.ext
    · apply Prod.ext
      · funext hj
        subst j
        exact ((h a).1 rfl).symm
      · funext hj
        subst j
        exact hl.symm.trans ((h a).1 rfl).symm
    · apply Prod.ext
      · funext hj
        subst j
        exact hr.trans ((h c).2.2 rfl).symm
      · funext hj
        subst j
        exact ((h c).2.2 rfl).symm
  have product (y : ∀ j, (tensorProduct (wire (k := k) a b I) (wire b c I)).Basis j) :
      (∏ j, if ok j (z j) (y j) then (1 : k) else 0) =
        if ∀ j, ok j (z j) (y j) then 1 else 0 := Fintype.prod_boole (p := fun j ↦ ok j (z j) (y j))
  rw [applyLocal, Finset.sum_eq_single y₀]
  · rw [product, if_congr hok (rfl : (1 : k) = 1) (rfl : (0 : k) = 0)]
    simp [tensorProduct, wire, y₀]
  · intro y _ hy
    rw [product]
    simp only [tensorProduct, wire]
    split_ifs with h hl hr <;> simp only [zero_mul, mul_zero, one_mul]
    exact (hy (uniqueY y h hl hr)).elim
  · simp

end WireArithmetic

end WireTensor


universe z

namespace WireTensor

variable {k J R : Type*} [CommSemiring k] [Fintype J] [Fintype R]

/-- The extra edge in `Option R` carries the factorization index. -/
def cutBasis (B : R → Type z) (K : Type z) : Option R → Type z
  | none => K
  | some r => B r

instance cutBasisFintype (B : R → Type z) (K : Type z) [∀ r, Fintype (B r)] [Fintype K]
    (e : Option R) : Fintype (cutBasis B K e) := by
  cases e with
  | none => exact inferInstanceAs (Fintype K)
  | some r => exact inferInstanceAs (Fintype (B r))

/-- The terminals feed into the center on their own side. The remaining edge
carries the common matrix-factorization index from the first center to the second. -/
def cutSource (place : R → J) (center : Bool → J) : Option R → J
  | none => center false
  | some r => place r

/-- Send each routed wire to the center on its selected side of the cut, and the auxiliary wire
to the true-side center. -/
def cutTarget (side : R → Bool) (center : Bool → J) : Option R → J
  | none => center true
  | some r => center (side r)

private theorem prod_at [DecidableEq J] (a : J) (f : ∀ j, j = a → k) :
    ∏ j, (if h : j = a then f j h else 1) = f a rfl := by
  rw [Finset.prod_eq_single a]
  · simp
  · intro j _ hj
    simp [hj]
  · simp

private def cutBasisEquiv (B : R → Type z) (K : Type z) :
    K × ((r : R) → B r) ≃ ((e : Option R) → cutBasis B K e) where
  toFun p | none => p.1 | some r => p.2 r
  invFun x := (x none, fun r ↦ x (some r))
  left_inv _ := rfl
  right_inv x := by funext e; cases e <;> rfl

open scoped Classical in
/-- Any matrix factorization across a cut of the terminal roles can be realized
by terminal-to-center wires plus a rank wire between the two centers. Roles and
centers may coincide as parties. Used for both shifted cuts in Lemma 3.2. -/
theorem cutFactorization_restricts (place : R → J) (side : R → Bool) (center : Bool → J)
    (B : R → Type z) [∀ r, Fintype (B r)] (K : Type z) [Fintype K]
    (F : ((r : R) → side r = false → B r) → K → k)
    (G : ((r : R) → side r = true → B r) → K → k) :
    Restricts (wireNetwork (cutSource place center) (cutTarget side center) (cutBasis B K))
      (placedTensor place B (fun x ↦ ∑ z, F (fun r _ ↦ x r) z * G (fun r _ ↦ x r) z)) := by
  classical
  let _ : DecidableEq (Option R) := Classical.decEq _
  let a := cutSource place center
  let b := cutTarget side center
  let I := cutBasis B K
  let L (j : J) (u : (r : R) → j = place r → B r)
      (w : (wireNetwork (k := k) a b I).Basis j) : k :=
    (∏ r, if h : j = place r then (if u r h = w.1 (some r) h then (1 : k) else 0) else 1) *
    (if h : j = center false then
      F (fun r hr ↦ w.2 (some r) (h.trans (congrArg center hr).symm)) (w.1 none h) else 1) *
    (if h : j = center true then
      G (fun r hr ↦ w.2 (some r) (h.trans (congrArg center hr).symm)) (w.2 none h) else 1)
  refine ⟨L, ?_⟩
  funext u
  refine (applyLocal_wireNetwork a b I L u).trans ?_
  let f := fun x : (e : Option R) → I e ↦ ∏ j, L j (u j) (edgeAssignment a b x j)
  change (∑ x, f x) = _
  calc
    _ = ∑ p, f (cutBasisEquiv B K p) := ((cutBasisEquiv B K).sum_comp f).symm
    _ = _ := ?_
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  let out := fun r ↦ u (place r) r rfl
  have hp (x : (r : R) → B r) : f (cutBasisEquiv B K (z, x)) =
      (if out = x then 1 else 0) * F (fun r _ ↦ x r) z * G (fun r _ ↦ x r) z := by
    dsimp only [f, L, edgeAssignment, cutBasisEquiv, Equiv.coe_fn_mk]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_comm]
    simp_rw [prod_at]
    simp [Fintype.prod_boole, out, ← funext_iff]
  change (∑ x, f (cutBasisEquiv B K (z, x))) = _
  simp_rw [hp]
  simp [ite_mul, out]

end WireTensor

end VPVNP
end Computability
end OAI
