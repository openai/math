import OAI.ThreeFlat.Diagonal.MotifKernel
import OAI.LinearAlgebra.SpectralBooks.PortWiring

namespace OAI
/-! # Regroup local motif factors after the common layout has been chosen

The selected histogram for every motif is fixed before selecting a layout.
Each site may then sum every absorbed edge locally. Surviving edges appear
just once in the shared boundary and feed their two incident maps.
-/

namespace ThreeFlat.Diagonal.MotifKernel

open LinearAlgebra.SpectralBooks Computability.VPVNP.WireTensor
open scoped BigOperators Classical

variable {J E G F : Type*} [Fintype J] [Fintype E] [Fintype G] [DecidableEq G] [CommSemiring F]

/-- Read a half-index in the two separate endpoint-list convention. -/
def portAt (P : PortGraph J E) {I : E → Type*} (j : J)
    (x : ((e : E) → j = P.tail e → I e) × ((e : E) → j = P.head e → I e)) : P.State I j := by
  rintro ⟨⟨e,b⟩,h⟩
  cases b with
  | false => exact x.1 e h.symm
  | true => exact x.2 e h.symm

omit [Fintype J] [Fintype E] in
private theorem portAt_assignment (P : PortGraph J E) {I : E → Type*} (z : ∀ e, I e) (j : J) :
    portAt P j (edgeAssignment P.tail P.head z j) = P.atVertex z j := by
  funext ⟨⟨e,b⟩,h⟩
  cases b <;> rfl

/-- The factor at one output position from a single motif, after summing
all edges whose two endpoint sites coincide. -/
noncomputable def groupedFactor (P : PortGraph J E) (place : J → G) {I : E → Type*} [∀ e, Fintype (I e)]
    (K : ∀ j, P.State I j → F) (g : G) (b : WiresAt P.tail P.head place (I := I) none) : F :=
  ∑ a : WiresAt P.tail P.head place (I := I) (some g),
    ∏ j : {j // place j = g}, K j (portAt P j (atParty P.tail P.head place j b (j.2.symm ▸ a)))

theorem port_contract_grouped (P : PortGraph J E) (place : J → G) {I : E → Type*} [∀ e, Fintype (I e)]
    (K : ∀ j, P.State I j → F) :
    P.contraction K = ∑ b, ∏ g, groupedFactor P place K g b := by
  let L (j : J) (_ : Unit) (a : (wireNetwork (k := F) P.tail P.head I).Basis j) := K j (portAt P j a)
  have h := applyLocal_eq_grouped P.tail P.head place L (fun _ => ())
  rw [applyLocal_wireNetwork] at h
  simpa only [L,portAt_assignment,PortGraph.contraction,groupedFactor] using h

/-- Multiple overlapping motifs choose their terms simultaneously. Their
shared layout may depend on the entire tuple of terms. All internal wire
sums stay in the unique site owning both endpoints. -/
theorem simultaneous_grouping {M : Type*} [Fintype M] (P : M → PortGraph J E)
    (H : M → Type*) [∀ m, Fintype (H m)] (I : ∀ m, H m → E → Type*) [∀ m t e, Fintype (I m t e)]
    (K : ∀ m t j, (P m).State (I m t) j → F)
    (place : (∀ m, H m) → M → J → G) :
    (∏ m, ∑ t, (P m).contraction (K m t)) =
      ∑ h : ∀ m, H m, ∑ b : ∀ m, WiresAt (P m).tail (P m).head (place h m) (I := I m (h m)) none,
        ∏ g, ∏ m, groupedFactor (P m) (place h m) (K m (h m)) g (b m) := by
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro h _
  have expand : (∏ m, (P m).contraction (K m (h m))) =
      ∏ m, ∑ b, ∏ g, groupedFactor (P m) (place h m) (K m (h m)) g b :=
    Finset.prod_congr rfl fun m _ => port_contract_grouped (P m) (place h m) (K m (h m))
  rw [expand]
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [Finset.prod_comm]

end ThreeFlat.Diagonal.MotifKernel

end OAI
