import OAI.Computability.VPVNP.NetworkKernel

/-!
# Relabelling a placed wire-network expansion

Bijections on sites, edges and individual payload alphabets preserve each
wire equality. Transporting both the input and a choice-dependent output
therefore preserves the exact identity for a substep.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace NetworkKernel

/-- A relabelling of sites and edges, with a bijection on the alphabet of each wire. -/
structure Network.Iso (N M : Network) where
  /-- Bijection carrying sites of the original network to sites of the relabelled network. -/
  site : N.Site ≃ M.Site
  /-- Bijection carrying individual wires to the relabelled wires, including parallel wires. -/
  edge : N.Edge ≃ M.Edge
  src : ∀ e, site (N.src e) = M.src (edge e)
  dst : ∀ e, site (N.dst e) = M.dst (edge e)
  /-- For each original wire, a bijection from its payload alphabet to the alphabet of its
  image wire. -/
  payload : ∀ e, N.Payload e ≃ M.Payload (edge e)


namespace Network.Iso

variable {N M : Network}

/-- Pull a half-wire assignment at an image site back to its original site. -/
def pullHalf (f : N.Iso M) (u : N.Site) (a : M.Half (f.site u)) : N.Half u :=
  ⟨fun e h ↦ (f.payload e).symm (a.1 (f.edge e) ((congrArg f.site h).trans (f.src e))),
   fun e h ↦ (f.payload e).symm (a.2 (f.edge e) ((congrArg f.site h).trans (f.dst e)))⟩

/-- Pull every site's independent half-wire assignment back along the isomorphism. -/
def pull (f : N.Iso M) (a : ∀ u, M.Half u) (u : N.Site) : N.Half u :=
  f.pullHalf u (a (f.site u))

private theorem src_at {v : M.Site} {e : M.Edge} (a : ∀ u, M.Half u) (h : v = M.src e) :
    (a v).1 e h = (a (M.src e)).1 e rfl := by cases h; rfl

private theorem dst_at {v : M.Site} {e : M.Edge} (a : ∀ u, M.Half u) (h : v = M.dst e) :
    (a v).2 e h = (a (M.dst e)).2 e rfl := by cases h; rfl

/-- The network equality tensor is invariant under the relabelling. -/
theorem coeff_pull {k : Type*} [CommSemiring k] (f : N.Iso M) (a : ∀ u, M.Half u) :
    N.coeff (k := k) (f.pull a) = M.coeff a := by
  classical
  unfold Network.coeff Network.tensor WireTensor.wireNetwork
  apply Fintype.prod_equiv f.edge
  intro e
  simp only [pull, pullHalf, src_at a, dst_at a, Equiv.apply_eq_iff_eq]

end Network.Iso

variable {N M : Network} {k : Type*}

/-- Transport the placements and local kernels of one term along input and output
network isomorphisms. -/
noncomputable def Term.reindex (t : Term k N) (input : N.Iso M) {P : Network}
    (output : t.output.Iso P) : Term k M where
  output := P
  place u := output.site (t.place (input.site.symm u))
  kernel := Equiv.piCongrLeft _ output.site fun v a z ↦
    t.kernel v (fun u h ↦ input.pullHalf u (a (input.site u) (by simpa using congrArg output.site h)))
      (output.pullHalf v z)

/-- Transport preserves a term's value on the corresponding half-wire assignment. -/
theorem Term.value_reindex [CommSemiring k] (t : Term k N) (input : N.Iso M)
    {P : Network} (output : t.output.Iso P) (a : ∀ u, M.Half u) :
    (t.reindex input output).value a = t.value (input.pull a) := by
  classical
  rw [Term.value_eq_edgeSum, Term.value_eq_edgeSum]
  symm
  let labels := output.edge.piCongr output.payload
  apply Fintype.sum_equiv labels
  intro z
  apply Fintype.prod_equiv output.site
  intro v
  simp only [reindex, Equiv.piCongrLeft_apply_apply, Network.Iso.pull,
    Network.Iso.pullHalf, WireTensor.edgeAssignment, labels, Equiv.piCongr_apply_apply,
    Equiv.symm_apply_apply]

/-- Transport an exact step along an input network isomorphism and one output
network isomorphism for each choice. -/
noncomputable def Step.reindex [CommSemiring k] (s : Step k N) (input : N.Iso M)
    {out : s.Choice → Network} (output : ∀ i, (s.term i).output.Iso (out i)) : Step k M where
  Choice := s.Choice
  choiceFintype := s.choiceFintype
  term i := (s.term i).reindex input (output i)
  exact_eq a := by
    rw [← input.coeff_pull a, s.exact_eq]
    simp only [Term.value_reindex]

end NetworkKernel

end VPVNP
end Computability
end OAI
