import OAI.Hierarchy.BinarySampling
import OAI.Hierarchy.GrassmannTransitivity
import OAI.ThreeFlat.ExpanderFiberKernel

namespace OAI
/-! # Joint observations on a Grassmann pair

A random linear map on the ambient binary space restricts to three independent
uniform maps on the common space and the two complementary summands. The fixed
labelling of each plane then gives a pair of equal-size conditional fibers.
-/

noncomputable section
namespace Hierarchy.NonlinearExpanders.GrassmannSampling

open Computability.VPVNP.Grassmann Hierarchy.GrassmannTransitivity
open ThreeFlat.Expander LinearMap Submodule

abbrev Data (n : ℕ) := Fin n → ZMod 2
abbrev Label (n r : ℕ) := Fin ((2^n)^r)
abbrev Read (n : ℕ) (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] := V →ₗ[ZMod 2] Data n

instance readFintype (n : ℕ) (V : Type*) [AddCommGroup V] [Module (ZMod 2) V]
    [FiniteDimensional (ZMod 2) V] : Fintype (Read n V) :=
  Fintype.ofEquiv _ (homLabels V (r := Module.finrank (ZMod 2) V) (n := n) rfl).symm

/-- The label is assigned with a single choice of basis at each plane. -/
def observe {m n : ℕ} (U : Plane m) (g : Read n (Space m)) : Label n m :=
  homLabels U.val U.property (g.comp U.val.subtype)

private def sumEquiv {m : ℕ} {C L U : Submodule (ZMod 2) (Space m)}
    (disj : Disjoint C L) (total : C ⊔ L = U) : (C × L) ≃ₗ[ZMod 2] U := by
  let f := C.subtype.coprod L.subtype
  have dj : Disjoint (range C.subtype) (range L.subtype) := by simpa using disj
  have hf : Function.Injective f := by
    rw [← ker_eq_bot, ker_coprod_of_disjoint_range _ _ dj]
    simp
  have he : range f = U := by simpa only [f, range_coprod, range_subtype] using total
  exact (LinearEquiv.ofInjective f hf).trans (LinearEquiv.ofEq _ _ he)

private theorem sumEquiv_coe {m : ℕ} {C L U : Submodule (ZMod 2) (Space m)}
    (disj : Disjoint C L) (total : C ⊔ L = U) (c : C) (l : L) :
    (sumEquiv disj total (c,l) : Space m) = (c : Space m) + l := rfl

private def readParts {m n : ℕ} {C L U : Submodule (ZMod 2) (Space m)}
    (disj : Disjoint C L) (total : C ⊔ L = U) : Read n U ≃ Read n C × Read n L :=
  (((sumEquiv disj total).symm.arrowCongr (LinearEquiv.refl (ZMod 2) (Data n))).toEquiv).trans
    (LinearMap.coprodEquiv (ZMod 2)).symm.toEquiv

private theorem readParts_observe {m n : ℕ} {C L U : Submodule (ZMod 2) (Space m)}
    (disj : Disjoint C L) (total : C ⊔ L = U) (g : Read n (Space m)) :
    readParts disj total (g.comp U.subtype) = (g.comp C.subtype, g.comp L.subtype) := by
  apply Prod.ext
  · ext c i
    change g (sumEquiv disj total (c,0) : Space m) i = g (c : Space m) i
    rw [sumEquiv_coe]
    simp
  · ext l i
    change g (sumEquiv disj total (0,l) : Space m) i = g (l : Space m) i
    rw [sumEquiv_coe]
    simp

private def layout {m n r : ℕ} (U : Plane m) {C L : Submodule (ZMod 2) (Space m)}
    (disj : Disjoint C L) (total : C ⊔ L = U.val)
    (hC : Module.finrank (ZMod 2) C = m-r) (hL : Module.finrank (ZMod 2) L = r) :
    Label n m ≃ Label n r × Label n (m-r) :=
  (homLabels U.val U.property).symm.trans <| (readParts disj total).trans <|
    (Equiv.prodComm _ _).trans (Equiv.prodCongr (homLabels L hL) (homLabels C hC))

private theorem layout_observe {m n r : ℕ} (U : Plane m) {C L : Submodule (ZMod 2) (Space m)}
    (disj : Disjoint C L) (total : C ⊔ L = U.val)
    (hC : Module.finrank (ZMod 2) C = m-r) (hL : Module.finrank (ZMod 2) L = r)
    (g : Read n (Space m)) :
    layout U disj total hC hL (observe U g) =
      (homLabels L hL (g.comp L.subtype), homLabels C hC (g.comp C.subtype)) := by
  simp only [layout, observe, Equiv.trans_apply, Equiv.symm_apply_apply, readParts_observe,
    Equiv.prodComm_apply, Equiv.prodCongr_apply]
  rfl

private def split {m r : ℕ} (p : Pair m r) := Classical.choice (split_exists p.val.1 p.val.2)

def layoutLeft {m r : ℕ} (n : ℕ) (p : Pair m r) : Label n m ≃ Label n r × Label n (m-r) :=
  let s := split p
  let dims := s.ranks p.property
  layout p.val.1 s.disjoint_left s.sum_left dims.1 dims.2.1

def layoutRight {m r : ℕ} (n : ℕ) (p : Pair m r) : Label n m ≃ Label n r × Label n (m-r) :=
  let s := split p
  let dims := s.ranks p.property
  layout p.val.2 (s.disjoint_right.mono_left (s.sum_left ▸ le_sup_left)) s.sum_right dims.1 dims.2.2

private def triple {m n r : ℕ} (p : Pair m r) :
    Read n (((split p).common × (split p).left) × (split p).right) ≃
    Label n (m-r) × (Label n r × Label n r) :=
  let s := split p
  let dims := s.ranks p.property
  let parts : Read n ((s.common × s.left) × s.right) ≃
      Read n (s.common × s.left) × Read n s.right := (LinearMap.coprodEquiv (ZMod 2)).symm.toEquiv
  let first : Read n (s.common × s.left) ≃ Read n s.common × Read n s.left :=
    (LinearMap.coprodEquiv (ZMod 2)).symm.toEquiv
  parts.trans <| (first.prodCongr (Equiv.refl _)).trans <| (Equiv.prodAssoc _ _ _).trans <|
    (homLabels s.common dims.1).prodCongr ((homLabels s.left dims.2.1).prodCongr (homLabels s.right dims.2.2))

private theorem triple_observe {m n r : ℕ} (p : Pair m r) (g : Read n (Space m)) :
    let s := split p
    let dims := s.ranks p.property
    triple p (g.comp s.embed) =
      (homLabels s.common dims.1 (g.comp s.common.subtype),
       homLabels s.left dims.2.1 (g.comp s.left.subtype),
       homLabels s.right dims.2.2 (g.comp s.right.subtype)) := by
  let s := split p
  have h0 :
      ((g.comp s.embed).comp (inl _ _ _)).comp (inl _ _ _) = g.comp s.common.subtype := by
    ext x i
    change g (((x : Space m) + 0) + 0) i = g x i
    simp
  have h1 :
      ((g.comp s.embed).comp (inl _ _ _)).comp (inr _ _ _) = g.comp s.left.subtype := by
    ext x i
    change g ((0 + (x : Space m)) + 0) i = g x i
    simp
  have h2 : (g.comp s.embed).comp (inr _ _ _) = g.comp s.right.subtype := by
    ext x i
    change g ((0 + 0) + (x : Space m)) i = g x i
    simp
  exact Prod.ext (congrArg (homLabels s.common (s.ranks p.property).1) h0)
    (Prod.ext (congrArg (homLabels s.left (s.ranks p.property).2.1) h1)
      (congrArg (homLabels s.right (s.ranks p.property).2.2) h2))

/-- Exact joint distribution for every pair type. -/
theorem pair_expectation {m n r : ℕ} (p : Pair m r) (D : Label n m → Label n m → ℝ) :
    (avg fun g : Read n (Space m) => D (observe p.val.1 g) (observe p.val.2 g)) =
    avg fun t => avg fun a => avg fun b =>
      D ((layoutLeft n p).symm (a,t)) ((layoutRight n p).symm (b,t)) := by
  let s := split p
  let H (z : Label n (m-r) × (Label n r × Label n r)) :=
    D ((layoutLeft n p).symm (z.2.1,z.1)) ((layoutRight n p).symm (z.2.2,z.1))
  let Z := triple (n := n) p
  have factor (g : Read n (Space m)) :
      D (observe p.val.1 g) (observe p.val.2 g) = H (Z (g.comp s.embed)) := by
    have left := layout_observe p.val.1 s.disjoint_left s.sum_left (s.ranks p.property).1
      (s.ranks p.property).2.1 g
    have right := layout_observe p.val.2 (s.disjoint_right.mono_left (s.sum_left ▸ le_sup_left))
      s.sum_right (s.ranks p.property).1 (s.ranks p.property).2.2 g
    change layoutLeft n p _ = _ at left
    change layoutRight n p _ = _ at right
    dsimp only [Z,s,H]
    rw [triple_observe]
    dsimp only
    rw [← left, ← right, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  calc
    _ = avg (fun g : Read n (Space m) => (H ∘ Z) (g.comp s.embed)) :=
      avg_congr _ _ factor
    _ = avg (H ∘ Z) := avg_restrict_linear s.embed s.injective (H ∘ Z)
    _ = avg H := avg_equiv Z _
    _ = _ := by
      rw [show avg H = avg (fun t => avg fun ab => H (t,ab)) from
        avg_prod (fun t ab => H (t,ab))]
      exact avg_congr _ _ fun t => avg_prod (fun a b => H (t,a,b))

end Hierarchy.NonlinearExpanders.GrassmannSampling

end
end OAI
