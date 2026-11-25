import OAI.Computability.BorderVNP.CubeIdentity
import OAI.Computability.BorderVNP.CrossingGadgetReduction

/-!
# Integral equations for a fixed cube identity

The local maps in Lemma 8.1 are a finite array of constants. Each input
coefficient of the identity gives one integral polynomial equation in
these constants. Their specialization preserves the chosen widths,
summand counts, and local table positions simultaneously.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube

open VPVNP.WireTensor VPVNP.MotifBase MvPolynomial
open scoped BigOperators Classical

/-- The copy and ordered sequence of cube edges selecting an ordinary summand. -/
abbrev Selector (n K h : ℕ) := Fin K × (Fin h → Edge (n+1))

/-- Endpoint words incident to one site of a binary wire topology. -/
abbrev PortWords {I V : Type} (a b : I → V) (w : I → ℕ) (v : V) :=
  ((i : I) → v = a i → Fin (2 ^ w i)) × ((i : I) → v = b i → Fin (2 ^ w i))

/-- The local input basis of the antipodal binary-wire tensor. -/
abbrev DemandBasis (n b h : ℕ) := PortWords (@start n) (@stop n) (fun _ => h*b)

/-- The local basis for the supply edges of one ordinary summand. -/
abbrev SupplyBasis {n K h : ℕ} (s : ℕ) (u : Selector n K h) :=
  PortWords (@Prod.fst (Vertex (n+1)) (Fin (n+1))) head (payload (onEdge s) u.2)

/-- An address in one of the actual local matrices chosen for Lemma 8.1. -/
abbrev TableEntry (n b h K s : ℕ) :=
  Σ u : Selector n K h, Σ v : Vertex (n+1), DemandBasis n b h v × SupplyBasis s u v

/-- All local matrix positions form a fixed finite alphabet of gadget labels. -/
noncomputable instance tableEntryFintype (n b h K s : ℕ) : Fintype (TableEntry n b h K s) := by
  let (v : Vertex (n+1)) : Fintype (DemandBasis n b h v) :=
    (binaryWires (k := ℤ) (@start n) (@stop n) (fun _ => h*b)).finiteBasis v
  let (u : Selector n K h) (v : Vertex (n+1)) : Fintype (SupplyBasis s u v) :=
    (binaryWires (k := ℤ) Prod.fst head (payload (onEdge s) u.2)).finiteBasis v
  unfold TableEntry
  infer_instance

variable {n b h K s : ℕ} {R : Type*} [CommRing R]

/-- The product of all old wire equalities is a zero-one integer tensor. -/
private noncomputable def targetCoeff (a : ∀ v, DemandBasis n b h v) : ℤ :=
  ∏ i, if (a (start i)).1 i rfl = (a (stop i)).2 i rfl then 1 else 0

private theorem targetCoeff_cast (a : ∀ v, DemandBasis n b h v) :
    (Int.castRingHom R) (targetCoeff a) =
      (binaryWires (k := R) (@start n) (@stop n) (fun _ => h*b)).coeff a := by
  rw [targetCoeff, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  split <;> simp_all

/-- Evaluation of one ordinary summand uses one shared index per supply edge. -/
private noncomputable def term (x : TableEntry n b h K s → R) (u : Selector n K h)
    (a : ∀ v, DemandBasis n b h v) : R := by
  letI : DecidableEq (Edge (n+1)) := Classical.decEq _
  exact ∑ z : ∀ e : Edge (n+1), Fin (2 ^ payload (onEdge s) u.2 e),
    ∏ v, x ⟨u,v,a v,edgeAssignment Prod.fst head z v⟩

private theorem local_eq_term (x : TableEntry n b h K s → R) (u : Selector n K h)
    (a : ∀ v, DemandBasis n b h v) :
    @applyLocal R (Vertex (n+1)) _ _ (SupplyBasis s u) (DemandBasis n b h)
      (binaryWires (k := R) Prod.fst head (payload (onEdge s) u.2)).finiteBasis
      (fun v i z => x ⟨u,v,i,z⟩) (binaryWires (k := R) Prod.fst head (payload (onEdge s) u.2)).coeff a = term x u a :=
  applyLocal_wireNetwork Prod.fst head (fun e => Fin (2 ^ payload (onEdge s) u.2 e))
    (C := DemandBasis n b h) (fun v i z => x ⟨u,v,i,z⟩) a

/-- The fixed entry tuple satisfies the base identity coordinate by coordinate. -/
def ValidTables (x : TableEntry n b h K s → R) : Prop :=
  ∀ a : ∀ v, DemandBasis n b h v, (Int.castRingHom R) (targetCoeff a) = ∑ u, term x u a

set_option backward.isDefEq.respectTransparency false in
/-- Naming the tuple loses none of the local-map data in the base identity. -/
theorem exists_validTables_iff :
    (∃ x : TableEntry n b h K s → R, ValidTables x) ↔
      BaseIdentity R (@start n) (@stop n) Prod.fst head (fun _ => b) (onEdge s) K h := by
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨fun u v a z => x ⟨u,v,a,z⟩, ?_⟩
    funext a
    rw [Finset.sum_apply, ← targetCoeff_cast (R := R) (b := b) (h := h) a]
    have heq := hx a
    rw [heq]
    apply Finset.sum_congr _ (fun u _ => (local_eq_term x u a).symm)
    exact congrArg (@Fintype.elems (Selector n K h)) (Subsingleton.elim _ _)
  · rintro ⟨L,hL⟩
    let x : TableEntry n b h K s → R := fun i => L i.1 i.2.1 i.2.2.1 i.2.2.2
    refine ⟨x, fun a => ?_⟩
    have he := congrFun hL a
    rw [targetCoeff_cast (R := R), he, Finset.sum_apply]
    apply Finset.sum_congr _ (fun u _ => local_eq_term x u a)
    exact congrArg (@Fintype.elems (Selector n K h)) (Subsingleton.elim _ _)

/-- One integral equation per demand-tensor coordinate. Its variables are the
matrix positions, so even equal-valued entries retain distinct addresses. -/
noncomputable def tableEquation (K s : ℕ) (a : ∀ v, DemandBasis n b h v) :
    MvPolynomial (TableEntry n b h K s) ℤ :=
  C (targetCoeff a) - ∑ u : Selector n K h, term (R := MvPolynomial (TableEntry n b h K s) ℤ) X u a

private theorem eval_term (x : TableEntry n b h K s → R) (u : Selector n K h)
    (a : ∀ v, DemandBasis n b h v) :
    eval₂Hom (Int.castRingHom R) x (term (R := MvPolynomial (TableEntry n b h K s) ℤ) X u a) =
      term x u a := by
  simp only [term, map_sum, map_prod, eval₂Hom_X']

/-- The vanishing of the explicit integral equations is equivalent to the exact
ordinary tensor identity over the current coefficient ring. -/
theorem validTables_iff_equations (x : TableEntry n b h K s → R) :
    ValidTables x ↔ ∀ a, eval₂Hom (Int.castRingHom R) x (tableEquation K s a) = 0 := by
  simp only [ValidTables, tableEquation, map_sub, eval₂Hom_C, map_sum, eval_term, sub_eq_zero]

/-- Read the fixed cube matrices using one shared index per supply edge.
The right side tests every original antipodal wire and allows loops to retain
their separate endpoint slots. -/
theorem ValidTables.read {x : TableEntry n b h K s → R} (hx : ValidTables x)
    (a : ∀ v, DemandBasis n b h v) :
    (∑ u : Selector n K h, ∑ z : ∀ e : Edge (n+1), Fin (2 ^ payload (onEdge s) u.2 e),
      ∏ v, x ⟨u,v,a v,edgeAssignment Prod.fst head z v⟩) =
      ∏ i, if (a (start i)).1 i rfl = (a (stop i)).2 i rfl then (1 : R) else 0 := by
  calc
    _ = ∑ u, term x u a := by
      apply Finset.sum_congr rfl
      intro u _
      unfold term
      apply Finset.sum_congr _ fun _ _ => rfl
      exact congrArg (@Fintype.elems ((e : Edge (n+1)) → Fin (2 ^ payload (onEdge s) u.2 e)))
        (Subsingleton.elim _ _)
    _ = (Int.castRingHom R) (targetCoeff a) := (hx a).symm
    _ = _ := by simp only [targetCoeff, map_prod, apply_ite, map_one, map_zero]

/-- Specialize all local matrices without changing the underlying cube, its
ports, any edge width, or its exact ordinary sum. -/
theorem ValidTables.specialize {E : Type*} [CommRing E] {x : TableEntry n b h K s → R}
    (hx : ValidTables x) (y : TableEntry n b h K s → E)
    (hrel : ∀ q : MvPolynomial (TableEntry n b h K s) ℤ, eval₂Hom (Int.castRingHom R) x q = 0 →
      eval₂Hom (Int.castRingHom E) y q = 0) : ValidTables y :=
  (validTables_iff_equations y).mpr fun a => hrel _ ((validTables_iff_equations x).mp hx a)

/-- Joint relations of the paid shortening and cube tuple preserve the latter
as well, using the right-hand block of the same specialization. -/
theorem ValidTables.specializeWith {F E : Type*} [Field F] [Field E] {D m : ℕ}
    (e : Crossing.PaidIdentity F D m) {x : TableEntry n b h K s → F} (hx : ValidTables x)
    (y : e.Entry ⊕ TableEntry n b h K s → E)
    (hrel : ∀ q : MvPolynomial (e.Entry ⊕ TableEntry n b h K s) ℤ,
      eval₂Hom (Int.castRingHom F) (Sum.elim e.entry x) q = 0 →
      eval₂Hom (Int.castRingHom E) y q = 0) : ValidTables (y ∘ Sum.inr) := by
  apply hx.specialize
  intro q hq
  have hs := hrel (rename (Sum.inr : TableEntry n b h K s → e.Entry ⊕ TableEntry n b h K s) q)
  simpa [eval₂Hom_rename, Function.comp_def, hq] using hs

end Cube

end BorderVNP
end Computability
end OAI
