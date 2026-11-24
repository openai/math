import OAI.Computability.VPVNP.PlacedTensor

/-!
# Placed local kernels of a wire network

Equation (7.1) of *VP and VNP differ over every field* sums over motif choices
and then over one shared assignment per edge of the chosen output network.
A choice determines the topology, the widths, and the placement of whole old
vertex factors. Contracting the expansion against arbitrary factors only
requires independent old half-wire indices inside each new site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace NetworkKernel

open WireTensor

/-- An indexed wire network. The payload alphabet can vary from edge to edge. -/
structure Network where
  /-- Finite type of sites where the network's half-wire payloads are assigned. -/
  Site : Type
  siteFintype : Fintype Site
  /-- Finite type of individual directed wires whose endpoint payloads are equated by the
  network tensor. -/
  Edge : Type
  edgeFintype : Fintype Edge
  /-- Source site of a directed wire, where its outgoing half-wire payload is assigned. -/
  src : Edge → Site
  /-- Destination site of a directed wire, where its incoming half-wire payload is assigned. -/
  dst : Edge → Site
  /-- Finite alphabet of possible payloads shared by the two ends of each wire. -/
  Payload : Edge → Type
  payloadFintype : ∀ e, Fintype (Payload e)

attribute [instance] Network.siteFintype Network.edgeFintype Network.payloadFintype

/-- Independent assignments to all incoming and outgoing half-wires at a site. -/
abbrev Network.Half (N : Network) (v : N.Site) :=
  ((e : N.Edge) → v = N.src e → N.Payload e) × ((e : N.Edge) → v = N.dst e → N.Payload e)

variable {k : Type*} [CommSemiring k]

/-- The equality of the two half-wire indices on each edge. -/
noncomputable abbrev Network.tensor (N : Network) (k : Type*) [CommSemiring k] :=
  wireNetwork (k := k) N.src N.dst N.Payload

/-- Product of wire equality indicators on a global half-wire assignment. -/
noncomputable def Network.coeff (N : Network) (a : ∀ u, N.Half u) : k :=
  (N.tensor k).coeff a

/-- Local old indices assigned to a single new site by the placement. -/
abbrev Placed {U V : Type} (p : U → V) (B : U → Type) (v : V) :=
  (u : U) → v = p u → B u

/-- One admitted term of a substep. Its network and placement can depend on
the entire list of selected motif terms. -/
structure Term (k : Type*) (old : Network) where
  /-- New network used in this summand of the compression step. -/
  output : Network
  /-- Assigns each old site to the new site that receives its half-wire data. -/
  place : old.Site → output.Site
  /-- Local coefficient at a new site, depending on the old half-wire data placed there and on
  the new half-wire assignment. -/
  kernel : ∀ v, Placed place old.Half v → output.Half v → k

open scoped Classical in
/-- Wire expansion in one term, read as a local map on the output wire tensor. -/
noncomputable def Term.value {N : Network} (t : Term k N) (a : ∀ u, N.Half u) : k :=
  applyLocal t.kernel (t.output.tensor k).coeff (placedAssignmentEquiv t.place N.Half a)

open scoped Classical in
/-- Each term of (7.1) uses exactly one sum per new edge, including parallel
edges. Both ends of the edge use the same payload. -/
theorem Term.value_eq_edgeSum {N : Network} (t : Term k N) (a : ∀ u, N.Half u) :
    t.value a = ∑ z : (e : t.output.Edge) → t.output.Payload e,
      ∏ v, t.kernel v (fun u _ ↦ a u) (edgeAssignment t.output.src t.output.dst z v) :=
  applyLocal_wireNetwork t.output.src t.output.dst t.output.Payload t.kernel
    (placedAssignmentEquiv t.place N.Half a)

/-- A substep specifies its finite term list and the coefficient identity. -/
structure Step (k : Type*) [CommSemiring k] (old : Network) where
  /-- Finite index type of terms in the exact expansion of the old network's coefficient. -/
  Choice : Type
  choiceFintype : Fintype Choice
  /-- Output network, placement and local kernels chosen by a term index. -/
  term : Choice → Term k old
  exact_eq : ∀ a, old.coeff a = ∑ i, (term i).value a

attribute [instance] Step.choiceFintype

open scoped Classical in
/-- Equation (7.1), with both sums and the dependence of all incidence data on
the chosen term displayed. -/
theorem Step.edgeExpansion {N : Network} (s : Step k N) (a : ∀ u, N.Half u) :
    N.coeff a = ∑ i, ∑ z : (e : (s.term i).output.Edge) → (s.term i).output.Payload e,
      ∏ v, (s.term i).kernel v (fun u _ ↦ a u)
        (edgeAssignment (s.term i).output.src (s.term i).output.dst z v) := by
  simp only [s.exact_eq, Term.value_eq_edgeSum]

/-- Whole local factors, evaluated at a fixed choice of any external indices. -/
abbrev Factors (k : Type*) (N : Network) := ∀ u, N.Half u → k

open scoped Classical in
/-- Contract the wire equalities with arbitrary local factors. -/
noncomputable def contract (N : Network) (F : Factors k N) : k :=
  ∑ a : (u : N.Site) → N.Half u, (∏ u, F u (a u)) * N.coeff a

open scoped Classical in
/-- In a contraction against wire equalities, one common value per edge
suffices. -/
theorem contract_edgeSum (N : Network) (F : Factors k N) :
    contract N F = ∑ z : (e : N.Edge) → N.Payload e, ∏ u, F u (edgeAssignment N.src N.dst z u) :=
  applyLocal_wireNetwork N.src N.dst N.Payload (fun u (_ : Unit) z ↦ F u z) (fun _ ↦ ())

open scoped Classical in
/-- Only the original factors placed at this site enter its local product. -/
noncomputable def Term.placedProduct {N : Network} (t : Term k N) (F : Factors k N)
    (v : t.output.Site) (a : Placed t.place N.Half v) : k :=
  ∏ u, if h : v = t.place u then F u (a u h) else 1

private theorem Term.prod_placedProduct {N : Network} (t : Term k N) (F : Factors k N)
    (a : ∀ u, N.Half u) :
    (∏ v, t.placedProduct F v (fun u _ ↦ a u)) = ∏ u, F u (a u) := by
  classical
  simp only [Term.placedProduct]
  rw [Finset.prod_comm]
  simp

open scoped Classical in
/-- The new local vertex factor obtained by summing the old half-wire indices
at this site. The same kernel applies when the old factors carry free indices. -/
noncomputable def Term.push {N : Network} (t : Term k N) (F : Factors k N) :
    Factors k t.output := fun v z ↦
  ∑ a : Placed t.place N.Half v, t.placedProduct F v a * t.kernel v a z

open scoped Classical in
/-- A single placed kernel contracts locally against the complete old factors. -/
theorem Term.contract_value {N : Network} (t : Term k N) (F : Factors k N) :
    (∑ a : (u : N.Site) → N.Half u, (∏ u, F u (a u)) * t.value a) =
      contract t.output (t.push F) := by
  simp only [Term.value_eq_edgeSum, Finset.mul_sum, contract_edgeSum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  simp only [Term.push, Fintype.prod_sum]
  apply Fintype.sum_equiv (placedAssignmentEquiv t.place N.Half)
  intro a
  simp only [Finset.prod_mul_distrib, placedAssignmentEquiv, Equiv.coe_fn_mk,
    Term.prod_placedProduct]

open scoped Classical in
/-- Substitution of a kernel expansion preserves the contraction of an
arbitrary old network over the coefficient semiring. -/
theorem Step.contract_eq_sum {N : Network} (s : Step k N) (F : Factors k N) :
    contract N F = ∑ i, contract (s.term i).output ((s.term i).push F) := by
  simp only [contract, s.exact_eq, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ ↦ (s.term i).contract_value F


open scoped Classical in
/-- Push an old factor with external indices, carrying all of those indices
to its designated new site. The local map only reads the external indices
in that site's placement fiber. -/
noncomputable def Term.pushOpen {N : Network} (t : Term k N) {External : N.Site → Type}
    (F : ∀ u, External u → N.Half u → k) (v : t.output.Site) (c : Placed t.place External v)
    (z : t.output.Half v) : k :=
  ∑ a : Placed t.place N.Half v,
    (∏ u, if h : v = t.place u then F u (c u h) (a u h) else 1) * t.kernel v a z

open scoped Classical in
/-- Substep substitution with uncontracted indices. At each new site the
external input consists exactly of the old external inputs placed there. -/
theorem Step.contract_open {N : Network} (s : Step k N) {External : N.Site → Type}
    (F : ∀ u, External u → N.Half u → k) (c : (u : N.Site) → External u) :
    contract N (fun u a ↦ F u (c u) a) =
      ∑ i, contract (s.term i).output (fun v ↦ (s.term i).pushOpen F v (fun u _ ↦ c u)) :=
  s.contract_eq_sum _

/-- A layout before contraction of wires whose two endpoints land at the
same output site. Each of these wires has one payload, owned by that site. -/
structure Layout (k : Type*) (old : Network) where
  /-- Network of exposed wires remaining after internal labels are summed. -/
  output : Network
  /-- Assigns each old site to the output site at which its data enter the local coefficient. -/
  place : old.Site → output.Site
  /-- Finite type of absorbed wires or other internal summation indices. -/
  Internal : Type
  internalFintype : Fintype Internal
  /-- Finite alphabet summed over at each internal index. -/
  Label : Internal → Type
  labelFintype : ∀ e, Fintype (Label e)
  /-- Output site responsible for summing the label at each internal index. -/
  owner : Internal → output.Site
  /-- Local coefficient before summation, depending on the old data placed at the site, its
  internal labels and its exposed half-wires. -/
  entry : ∀ v, Placed place old.Half v → Placed owner Label v → output.Half v → k

attribute [instance] Layout.internalFintype Layout.labelFintype

open scoped Classical in
/-- Summing each absorbed edge once, inside the kernel at its owner. -/
noncomputable def Layout.term {N : Network} (L : Layout k N) : Term k N where
  output := L.output
  place := L.place
  kernel v a z := ∑ h : Placed L.owner L.Label v, L.entry v a h z

open scoped Classical in
/-- Local sums over internal wires are equal to one global assignment to the
internal wires. The shared edge indices of the output are summed separately. -/
theorem Layout.term_value {N : Network} (L : Layout k N) (a : ∀ u, N.Half u) :
    L.term.value a = ∑ z : (e : L.output.Edge) → L.output.Payload e,
      ∑ h : (e : L.Internal) → L.Label e,
        ∏ v, L.entry v (fun u _ ↦ a u) (fun e _ ↦ h e)
          (edgeAssignment L.output.src L.output.dst z v) := by
  rw [Term.value_eq_edgeSum]
  apply Finset.sum_congr rfl
  intro z _
  change (∏ v, ∑ h : Placed L.owner L.Label v,
    L.entry v (fun u _ ↦ a u) h (edgeAssignment L.output.src L.output.dst z v)) = _
  rw [Fintype.prod_sum]
  symm
  exact Fintype.sum_equiv (placedAssignmentEquiv L.owner L.Label) _ _ (fun _ ↦ rfl)

open scoped Classical in
/-- Assemble exact motif expansions into a step of (7.1). The hypotheses
describe the original demand factorization, the individual motif identities,
and the two properties of the selected layout: its payload bijection and
the regrouping of its map entries. The layout may depend on the whole list
of selectors. -/
noncomputable def Step.ofMotifProduct {N : Network} {M : Type} [Fintype M]
    (C : M → Type) [∀ m, Fintype (C m)] (X : (m : M) → C m → Type)
    [∀ m i, Fintype (X m i)]
    (demand : M → ((u : N.Site) → N.Half u) → k)
    (contribution : (m : M) → (i : C m) → X m i → ((u : N.Site) → N.Half u) → k)
    (old_eq : ∀ a, N.coeff a = ∏ m, demand m a)
    (motif_eq : ∀ m a, demand m a = ∑ i, ∑ x, contribution m i x a)
    (L : ((m : M) → C m) → Layout k N)
    (split : ∀ s, ((m : M) → X m (s m)) ≃
      ((e : (L s).output.Edge) → (L s).output.Payload e) × ((e : (L s).Internal) → (L s).Label e))
    (group : ∀ s x a, (∏ m, contribution m (s m) (x m) a) =
      ∏ v, (L s).entry v (fun u _ ↦ a u) (fun e _ ↦ (split s x).2 e)
        (edgeAssignment (L s).output.src (L s).output.dst (split s x).1 v)) : Step k N where
  Choice := (m : M) → C m
  choiceFintype := inferInstance
  term s := (L s).term
  exact_eq a := by
    simp only [old_eq, motif_eq, Fintype.prod_sum, Layout.term_value]
    apply Finset.sum_congr rfl
    intro s _
    let f (z : ((e : (L s).output.Edge) → (L s).output.Payload e) ×
        ((e : (L s).Internal) → (L s).Label e)) :=
      ∏ v, (L s).entry v (fun u _ ↦ a u) (fun e _ ↦ z.2 e)
        (edgeAssignment (L s).output.src (L s).output.dst z.1 v)
    exact (Fintype.sum_equiv (split s) _ f (fun x ↦ group s x a)).trans
      (Fintype.sum_prod_type f)

open scoped Classical in
/-- Fixing the old half-wire indices turns a term into a contraction of the
new network against the rows of its local kernels. -/
theorem Term.value_eq_contract {N : Network} (t : Term k N) (a : ∀ u, N.Half u) :
    t.value a = contract t.output (fun v z ↦ t.kernel v (fun u _ ↦ a u) z) :=
  (t.value_eq_edgeSum a).trans (contract_edgeSum _ _).symm

/-- Finite branch-dependent iteration of substeps. A branch can use a
different continuation for each selected term. -/
inductive History (k : Type*) [CommSemiring k] : Network → Type _
  | stop {N} : History k N
  | branch {N} (step : Step k N) (tail : ∀ i, History k (step.term i).output) : History k N

namespace History

/-- Fully enumerated paths carry every term choice, each old half-wire
assignment separately, and the one shared final payload on each final edge. -/
def Path {N : Network} : History k N → Type
  | .stop => (e : N.Edge) → N.Payload e
  | .branch s tail => (i : s.Choice) × ((u : N.Site) → N.Half u) × (tail i).Path

open scoped Classical in
noncomputable instance pathFintype {N : Network} (H : History k N) : Fintype H.Path := by
  induction H with
  | @stop N => exact inferInstanceAs (Fintype ((e : N.Edge) → N.Payload e))
  | @branch N s tail ih =>
    letI := ih
    exact inferInstanceAs (Fintype ((i : s.Choice) × ((u : N.Site) → N.Half u) × (tail i).Path))

/-- Product of original factor entries and the kernel entries selected by the
path. Every intermediate assignment is explicitly part of the path. -/
noncomputable def weight {N : Network} (H : History k N) (F : Factors k N) : H.Path → k :=
  match H with
  | .stop => fun z ↦ ∏ u, F u (edgeAssignment N.src N.dst z u)
  | .branch s tail => fun ⟨i, a, path⟩ ↦
    (∏ u, F u (a u)) *
      (tail i).weight (fun v z ↦ (s.term i).kernel v (fun u _ ↦ a u) z) path

/-- Iterated substitution as a single finite sum over fully expanded paths.
This is the exact algebra used before weighting paths in Section 12. -/
theorem contract_eq_sum_paths {N : Network} (H : History k N) (F : Factors k N) :
    contract N F = ∑ p : H.Path, H.weight F p := by
  classical
  induction H with
  | stop => exact contract_edgeSum _ _
  | @branch N s tail ih =>
    change contract N F =
      ∑ p : (i : s.Choice) × ((u : N.Site) → N.Half u) × (tail i).Path,
        (∏ u, F u (p.2.1 u)) *
          (tail p.1).weight (fun v z ↦ (s.term p.1).kernel v (fun u _ ↦ p.2.1 u) z) p.2.2
    simp only [Fintype.sum_sigma, Fintype.sum_prod_type, ← Finset.mul_sum, ← ih,
      ← Term.value_eq_contract]
    simp only [contract, s.exact_eq, Finset.mul_sum]
    exact Finset.sum_comm

end History
end NetworkKernel

end VPVNP
end Computability
end OAI
