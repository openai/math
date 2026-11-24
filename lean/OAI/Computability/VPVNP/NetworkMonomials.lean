import OAI.Computability.VPVNP.NetworkKernel
import OAI.Computability.VPVNP.Diagonal

/-!
# The monomials of an expanded contraction

In equation (12.2) of *VP and VNP differ over every field*, each path records
the old half-wire indices, a local witness for each kernel entry, and an
accepting path at each original site. Products add parameter exponents.
The choice sets are specified independently of the parameter values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace NetworkKernel

open Diagonal

variable {A : Type*} [CommRing A] {Label : Type} [Fintype Label] {κ : Label → A}

/-- An entry specified by finite witnesses, each contributing a parameter
monomial. The empty witness set represents a failed local check. -/
structure MonomialWitness (κ : Label → A) (value : A) where
  /-- Finite index type of the monomials in the witnessed sum, retaining repeated summands as
  separate choices. -/
  Choice : Type
  choiceFintype : Fintype Choice
  /-- Exponent of each label in the monomial selected by a given witness choice. -/
  exponents : Choice → Label → ℕ
  evaluates : ∑ p, labelMonomial κ (exponents p) = value

attribute [instance] MonomialWitness.choiceFintype

namespace MonomialWitness

/-- Change only the proved value of an expansion, preserving the choice
type and exponent function by definition. -/
def changeValue {x y : A} (w : MonomialWitness κ x) (h : x = y) : MonomialWitness κ y where
  Choice := w.Choice
  choiceFintype := w.choiceFintype
  exponents := w.exponents
  evaluates := w.evaluates.trans h

/-- All accepting local paths have unit weight before kernel substitution. -/
def paths (κ : Label → A) (P : Type) [Fintype P] :
    MonomialWitness κ (Fintype.card P : A) where
  Choice := P
  choiceFintype := inferInstance
  exponents _ _ := 0
  evaluates := by simp [labelMonomial]

/-- A single successful local monomial. Its witness persists under every
parameter specialization, including one sending the monomial to zero. -/
def oneMonomial (κ : Label → A) (e : Label → ℕ) : MonomialWitness κ (labelMonomial κ e) where
  Choice := Unit
  choiceFintype := inferInstance
  exponents _ := e
  evaluates := by simp

/-- A map entry that fails its syntactic checks has no witnesses. Passing
the checks contributes its monomial even if that monomial evaluates to zero. -/
def checked (κ : Label → A) (ok : Bool) (e : Label → ℕ) :
    MonomialWitness κ (if ok then labelMonomial κ e else 0) := by
  cases ok with
  | false => simpa using paths κ Empty
  | true => exact oneMonomial κ e

/-- Disjointly enumerate a finite sum of local choices. -/
noncomputable def sum {I : Type} [Fintype I] {f : I → A}
    (w : ∀ i, MonomialWitness κ (f i)) : MonomialWitness κ (∑ i, f i) where
  Choice := (i : I) × (w i).Choice
  choiceFintype := inferInstance
  exponents p := (w p.1).exponents p.2
  evaluates := by simp only [Fintype.sum_sigma, MonomialWitness.evaluates]

open scoped Classical in
/-- Independent local choices multiply. Exponents accumulate coordinatewise. -/
noncomputable def prod {I : Type} [Fintype I] {f : I → A}
    (w : ∀ i, MonomialWitness κ (f i)) : MonomialWitness κ (∏ i, f i) where
  Choice := (i : I) → (w i).Choice
  choiceFintype := inferInstance
  exponents p l := ∑ i, (w i).exponents (p i) l
  evaluates := by
    simp_rw [labelMonomial_accumulate κ]
    rw [← Fintype.prod_sum (fun i p ↦ labelMonomial κ ((w i).exponents p))]
    simp only [MonomialWitness.evaluates]

/-- Combine witnesses of two successive factors of the path weight. -/
noncomputable def mul {x y : A} (v : MonomialWitness κ x) (w : MonomialWitness κ y) :
    MonomialWitness κ (x * y) where
  Choice := v.Choice × w.Choice
  choiceFintype := inferInstance
  exponents p l := v.exponents p.1 l + w.exponents p.2 l
  evaluates := by
    rw [Fintype.sum_prod_type]
    simp only [labelMonomial, pow_add, Finset.prod_mul_distrib]
    simp only [← Finset.mul_sum, ← Finset.sum_mul]
    exact congrArg₂ (· * ·) v.evaluates w.evaluates

end MonomialWitness

open scoped Classical in
/-- Expand the hidden sums over absorbed fields in the local layout kernel.
The local entry witnesses include the syntactic map-entry checks and their
monomials. -/
noncomputable def Layout.kernelWitness {N : Network} (L : Layout A N)
    (W : ∀ v a h z, MonomialWitness κ (L.entry v a h z))
    (v : L.output.Site) (a : Placed L.place N.Half v) (z : L.output.Half v) :
    MonomialWitness κ (L.term.kernel v a z) :=
  MonomialWitness.sum (fun h ↦ W v a h z)

open scoped Classical in
/-- Expand a single new vertex factor. Its choice records the old half-wires
and witnesses only at old sites assigned to this vertex, together with the
chosen witness for the new local kernel. -/
noncomputable def Term.pushWitness {N : Network} (t : Term A N) (F : Factors A N)
    (W : ∀ u b, MonomialWitness κ (F u b))
    (K : ∀ v a z, MonomialWitness κ (t.kernel v a z)) (v : t.output.Site) (z : t.output.Half v) :
    MonomialWitness κ (t.push F v z) := by
  refine MonomialWitness.sum (fun a ↦ MonomialWitness.mul ?_ (K v a z))
  have eqn : t.placedProduct F v a =
      ∏ u : {u // v = t.place u}, F u.val (a u.val u.prop) :=
    Finset.prod_congr_set {u | v = t.place u} _ _
      (fun u h ↦ dite_eq_left h) (fun u h ↦ dite_eq_right h)
  exact (MonomialWitness.prod
      (fun (u : {u // v = t.place u}) ↦ W u.val (a u.val u.prop))).changeValue eqn.symm

open scoped Classical in
/-- Unpack a local history node into its hidden old indices, the independent
children assigned to this vertex, and its own kernel witness. -/
def Term.pushChoice {N : Network} (t : Term A N) (F : Factors A N)
    (W : ∀ u b, MonomialWitness κ (F u b)) (K : ∀ v a z, MonomialWitness κ (t.kernel v a z))
    (v : t.output.Site) (z : t.output.Half v) :
    (t.pushWitness F W K v z).Choice ≃
      (a : Placed t.place N.Half v) ×
        ((u : {u // v = t.place u}) → (W u.val (a u.val u.prop)).Choice) × (K v a z).Choice :=
  Equiv.refl _

open scoped Classical in
/-- Exponents at a local history node accumulate over precisely its own
children and its kernel entry. -/
@[simp] theorem Term.pushChoice_exponents {N : Network} (t : Term A N) (F : Factors A N)
    (W : ∀ u b, MonomialWitness κ (F u b)) (K : ∀ v a z, MonomialWitness κ (t.kernel v a z))
    (v : t.output.Site) (z : t.output.Half v) (a : Placed t.place N.Half v)
    (children : (u : {u // v = t.place u}) → (W u.val (a u.val u.prop)).Choice)
    (own : (K v a z).Choice) (l : Label) :
    (t.pushWitness F W K v z).exponents ((t.pushChoice F W K v z).symm ⟨a, children, own⟩) l =
      (∑ u, (W u.val (a u.val u.prop)).exponents (children u) l) + (K v a z).exponents own l := rfl

namespace History

/-- Finite local witnesses for every kernel that occurs in this history.
A branch can have different sites, hidden fields and templates. -/
def KernelWitnesses {N : Network} (κ : Label → A) : History A N → Type 1
  | .stop => PUnit
  | .branch s tail =>
    (∀ i v a z, MonomialWitness κ ((s.term i).kernel v a z)) ×
      ((i : s.Choice) → (tail i).KernelWitnesses κ)

/-- Complete finite witnesses for a network contraction. First select all
terms along the branch. After choosing one common value for each final edge,
each final site expands its own local history independently. -/
noncomputable def expandedWitness {N : Network} (H : History A N) (K : H.KernelWitnesses κ)
    (F : Factors A N) (W : ∀ u b, MonomialWitness κ (F u b)) :
    MonomialWitness κ (contract N F) := by
  classical
  induction H with
  | @stop N =>
    exact (MonomialWitness.sum (fun z ↦ MonomialWitness.prod
      (fun u ↦ W u (WireTensor.edgeAssignment N.src N.dst z u)))).changeValue
        (contract_edgeSum N F).symm
  | @branch N s tail ih =>
    exact (MonomialWitness.sum (fun i ↦ ih i (K.2 i) ((s.term i).push F)
      ((s.term i).pushWitness F W (K.1 i)))).changeValue (s.contract_eq_sum F).symm

open scoped Classical in
/-- At a terminal branch choose the final edge payloads once, and one local
history at each final vertex. -/
def stopChoice {N : Network} (K : (stop (k := A) (N := N)).KernelWitnesses κ)
    (F : Factors A N) (W : ∀ u b, MonomialWitness κ (F u b)) :
    (stop.expandedWitness K F W).Choice ≃ (z : (e : N.Edge) → N.Payload e) ×
      ((v : N.Site) → (W v (WireTensor.edgeAssignment N.src N.dst z v)).Choice) :=
  Equiv.refl _

open scoped Classical in
@[simp] theorem stopChoice_exponents {N : Network} (K : (stop (k := A) (N := N)).KernelWitnesses κ)
    (F : Factors A N) (W : ∀ u b, MonomialWitness κ (F u b)) (z : (e : N.Edge) → N.Payload e)
    (p : (v : N.Site) → (W v (WireTensor.edgeAssignment N.src N.dst z v)).Choice) (l : Label) :
    (stop.expandedWitness K F W).exponents ((stopChoice K F W).symm ⟨z, p⟩) l =
      ∑ v, (W v (WireTensor.edgeAssignment N.src N.dst z v)).exponents (p v) l := rfl

/-- At a branch, the selector chooses the new network and the rest of the
choice belongs to that network's continuation. -/
def branchChoice {N : Network} (s : Step A N) (tail : ∀ i, History A (s.term i).output)
    (K : (branch s tail).KernelWitnesses κ) (F : Factors A N)
    (W : ∀ u b, MonomialWitness κ (F u b)) :
    ((branch s tail).expandedWitness K F W).Choice ≃
      (i : s.Choice) × ((tail i).expandedWitness (K.2 i) ((s.term i).push F)
        ((s.term i).pushWitness F W (K.1 i))).Choice :=
  Equiv.refl _

@[simp] theorem branchChoice_exponents {N : Network} (s : Step A N)
    (tail : ∀ i, History A (s.term i).output)
    (K : (branch s tail).KernelWitnesses κ) (F : Factors A N) (W : ∀ u b, MonomialWitness κ (F u b))
    (i : s.Choice) (p : ((tail i).expandedWitness (K.2 i) ((s.term i).push F)
      ((s.term i).pushWitness F W (K.1 i))).Choice) (l : Label) :
    ((branch s tail).expandedWitness K F W).exponents ((branchChoice s tail K F W).symm ⟨i, p⟩) l =
      ((tail i).expandedWitness (K.2 i) ((s.term i).push F)
        ((s.term i).pushWitness F W (K.1 i))).exponents p l :=
  rfl

end History

/-- Natural path counts can be transported to any commutative coefficient
ring before expanding the kernels. -/
theorem natCast_contract (N : Network) (F : Factors ℕ N) :
    ((contract N F : ℕ) : A) = contract N (fun u a ↦ (F u a : A)) := by
  simp only [contract_edgeSum, Nat.cast_sum, Nat.cast_prod]

/-- Equation (12.2) for a compressed network of local path counts. Its left
side enumerates local paths explicitly, including distinct paths that have
the same exponent vector. -/
noncomputable def History.expandedCount {N : Network} (H : History A N)
    (K : H.KernelWitnesses κ) (P : ∀ u, N.Half u → Type) [∀ u b, Fintype (P u b)] :
    MonomialWitness κ ((contract N (fun u b ↦ Fintype.card (P u b)) : ℕ) : A) :=
  (H.expandedWitness K _ (fun u b ↦ MonomialWitness.paths κ (P u b))).changeValue
    (natCast_contract (A := A) N _).symm

end NetworkKernel

end VPVNP
end Computability
end OAI
