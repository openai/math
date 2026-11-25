import OAI.Computability.BorderVNP.CubeGlobalExpansion
import OAI.Computability.BorderVNP.CubePhysicalCommon
import OAI.Computability.BorderVNP.DiagonalPowerSites

/-! # The global tagged cube contraction in Sections 8 and 11

A path guesses private wire words once per cell, singleton bits once globally,
each cube's independent endpoint words and selector, and its shared internal
edge words. The product of the actual local records carries both parameter
exponents and all table-position multiplicities. Zero padding rejects extra
histories. This gives the coefficient identity (11.2) at every external input.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open Crossing Diagonal.CellEntries MvPolynomial
open private passed_counters from OAI.Computability.BorderVNP.DiagonalPowerSites
open scoped Classical

set_option synthInstance.maxSize 768

variable {n d blocks b h K s D : ℕ} {P : Type*} {bits : P → ℕ}
variable {Cell : Type} [Fintype Cell] [DecidableEq Cell] {Param Gadget E : Type*} [CommRing E]
variable (N : Network D P bits) (cell : N.Site → Cell)

/-- One complete path after expanding all ordered label pairs at the
publicly chosen block width. Supply assignments depend on their actual selectors. -/
abbrev Path (n d blocks b h K s : ℕ) :=
  (∀ c, N.InsideAssignment cell c) × (SingleSlot n d blocks (h*b) → Bool) ×
    (Packet n d blocks → Ports (fun _ : Ends n => h*b)) ×
    ((u : Packet n d blocks → Selector n K h) × (∀ i, (packetNetwork D b s (u i)).Assignment))

/-- Multiply every cell and cube table event for this path. This includes
tagged unary factors and distinguishes a failed check from a zero scalar. -/
noncomputable def pathTag (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
    (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (pos : Packet n d blocks → TableEntry n b h K s → Gadget)
    (a : Path N cell n d blocks b h K s) : Entry Param Gadget :=
  globalEntry pos D (host N cell slot tags x a.1) a.2.1 a.2.2.1 a.2.2.2.1 a.2.2.2.2

private theorem sum_two {A R : Type*} [AddCommMonoid R] {l r : Fintype A} {f g : A → R}
    (h : ∀ x, f x = g x) :
    ∑ x ∈ @Finset.univ A l, f x = ∑ x ∈ @Finset.univ A r, g x :=
  Finset.sum_congr (congrArg (@Finset.univ A) (Subsingleton.elim _ _)) (fun x _ => h x)

private theorem packet_explicit {I Sing : Type} [Fintype I] [Fintype Sing]
    (ww : Fintype (Sing → Bool)) (xx : Fintype (I → Ports (fun _ : Ends n => h*b)))
    (uu : Fintype (I → Selector n K h))
    (zz : ∀ u : I → Selector n K h, Fintype (∀ i, (packetNetwork D b s (u i)).Assignment))
    (yy : Fintype (I → Vertex n → Fin (h*b) → Bool))
    (pos : I → TableEntry n b h K s → Gadget) (values : Gadget → E)
    (ht : ∀ i, ValidTables (values ∘ pos i))
    (f : (Sing → Bool) → (I → Ports (fun _ : Ends n => h*b)) → Entry Param Gadget) :
    (∑ w ∈ @Finset.univ _ ww, ∑ x ∈ @Finset.univ _ xx, ∑ u ∈ @Finset.univ _ uu,
      ∑ z ∈ @Finset.univ _ (zz u), interpret values (globalEntry pos D f w x u z)) =
    ∑ w ∈ @Finset.univ _ ww, ∑ y ∈ @Finset.univ _ yy, interpret values (f w (fun i p => y i p.1)) := by
  refine Eq.trans ?_ ((packet_global_expansion pos values ht D f).trans ?_)
  · exact sum_two fun _ => sum_two fun _ => sum_two fun _ => sum_two fun _ => rfl
  · exact sum_two fun _ => sum_two fun _ => rfl

/-- Summing the actual physical paths over all local selectors recovers the
original tagged cell network as an equality of formal polynomials. -/
theorem value_eq_physical_paths (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
    (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (pos : Packet n d blocks → TableEntry n b h K s → Gadget)
    (values : Gadget → E) (ht : ∀ i, ValidTables (values ∘ pos i)) :
    N.value (fun v r p => interpret values (tags v r p)) x =
      ∑ a : Path N cell n d blocks b h K s, interpret values (pathTag N cell slot tags x pos a) := by
  rw [← sum_common_eq_value N cell slot tags values x]
  simp only [Path, Fintype.sum_prod_type, Fintype.sum_sigma, pathTag]
  apply Finset.sum_congr rfl
  intro inside _
  exact (packet_explicit inferInstance inferInstance inferInstance (fun _ => inferInstance)
    inferInstance pos values ht (host N cell slot tags x inside)).symm

/-- Equation (11.2) with its literal passing path condition, exponent test
and scalar multiplicity product. A zero-valued selected scalar retains its
own address and count in the path record. -/
theorem coefficient_eq_passing_paths (slot : LiveBit N cell ↪ Slot n d blocks (h*b))
    (tags : N.Tables (Entry Param Gadget)) (x : Ports bits)
    (pos : Packet n d blocks → TableEntry n b h K s → Gadget)
    (values : Gadget → E) (ht : ∀ i, ValidTables (values ∘ pos i)) (μ : Param →₀ ℕ) :
    let record := pathTag N cell slot tags x pos
    (N.value (fun v r p => interpret values (tags v r p)) x).coeff μ =
      ∑ a ∈ Finset.univ.filter (fun a => record a ≠ 0 ∧ (counters (record a)).1 = μ),
        (counters (record a)).2.prod fun g m => values g ^ m := by
  intro tag
  rw [value_eq_physical_paths N cell slot tags x pos values ht, coeff_sum, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro a _
  change (interpret values (tag a)).coeff μ = _
  by_cases htag : tag a = 0
  · simp [htag]
  · have eq := congrArg (interpret values) (passed_counters htag)
    rw [← eq, interpret_passed, coeff_monomial]
    simp [htag, eq_comm]

end Cube.Physical

end BorderVNP
end Computability
end OAI
