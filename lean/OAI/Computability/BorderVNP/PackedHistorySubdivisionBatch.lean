import OAI.Computability.BorderVNP.PackedHistorySubdivisionFrame
import OAI.Computability.BorderVNP.PackedHistoryDenseReady
import OAI.Computability.BorderVNP.ShortenDenseExecution

/-! # Subdivided child directories at the input of a normalized epoch -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Shortening Shortening.PublicCapacity Shortening.PublicRelative Shortening.PublicSegments
open Crossing Cover Cover.AddressCircuit Epoch Epoch.Round Packing Normalized
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D q : ℕ} (enum : Fin q ≃ Cube D) {L h : ℝ}

/-- The actual directory which the first checked stage reads at an epoch boundary. -/
noncomputable def initialDirectory {d : ℕ} {P : Type} {K : Type*} [CommSemiring K] {bits : P → ℕ}
    (p : Pack D P bits K) (r : SiteRoutes p (Cube D) d L) {s : Shape}
    (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site) (hh : 0<h) :
    Directory (r.initialPlacedPack hh) (s.subdivide ⌈L/h⌉₊).sites (s.subdivide ⌈L/h⌉₊).edges :=
  ⟨(row.siteRoutes r h).site,(row.siteRoutes r h).edge,stripeDummy p r row dummy⟩

/-- A static epoch input runs one copy of the concrete site-route subdivision for each child.
Every measured physical child supplies the exact charged/present directory expected by the
normalized shortening kernel. -/
theorem subdivision_batch (hh : 0<h) :
    ∃ C e : ℕ, ∀ (d copies : ℕ) (s : Shape) (w : ℕ), (s.subdivide ⌈L/h⌉₊).sites ≤ 2^w →
      ∃ f : Frame (Fin copies × Pins (allowedMoves (Cube D) L) q (d+1) s.sites s.edges w)
          (Fin copies × (Fin (s.subdivide ⌈L/h⌉₊).edges ⊕
            Raw (SiteFields D q d L h) (s.subdivide ⌈L/h⌉₊).sites (s.subdivide ⌈L/h⌉₊).edges w w)),
        f.size ≤ 1 + copies*(300*(s.sites+2*s.edges+1)*
          (Nat.clog 2 (s.sites+2*s.edges)+w+Fintype.card (ProductSlots q (d+1))+1)^3 +
          1 + (s.subdivide ⌈L/h⌉₊).sites*C*(d+2)^e + (s.subdivide ⌈L/h⌉₊).edges*(2+3*w)*8) ∧
        ∀ {P : Type} {K : Type*} [CommSemiring K] {bits : P → ℕ} (i : Fin copies) (p : Pack D P bits K)
          (r : SiteRoutes p (Cube D) d L) (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site) x,
          Ready enum p r row dummy (fun j => x (i,j)) →
          (initialDirectory p r row dummy hh).Reads (SiteRoutes.startingSites (Cube D) L h)
            (segmentField enum (SiteRoutes.startingSites (Cube D) L h) (lev := d) rfl) (fun j => f.eval x (i,j)) := by
  obtain ⟨C,e,rows⟩ := subdivision_frame (L := L) enum hh
  refine ⟨C,e,?_⟩
  intro d copies s w fit
  obtain ⟨one,hs,he⟩ := rows d s w fit
  let next := s.subdivide ⌈L/h⌉₊
  let X := Pins (allowedMoves (Cube D) L) q (d+1) s.sites s.edges w
  let Y := Fin next.edges ⊕ Raw (SiteFields D q d L h) next.sites next.edges w w
  let cell (i : Fin copies) := one.subst (Frame.initial (fun j : X => (i,j)))
  obtain ⟨all,ha,ea⟩ := exists_parallelFrames (out := fun _ : Fin copies => Y) cell
  let f := all.select (fun j : Fin copies × Y => ⟨j.1,j.2⟩)
  refine ⟨f,?_,?_⟩
  · have hv := ha.trans (Nat.add_le_add_left (Finset.sum_le_sum (fun (i : Fin copies) _ =>
        show (cell i).size ≤ _ by simpa [cell] using hs)) 1)
    simpa [f] using hv
  · intro P K _ bits i p r row dummy x ready
    have hx : (Frame.initial (fun j : X => (i,j))).eval x = fun j => x (i,j) := funext fun _ => by simp
    have ev : (fun j => f.eval x (i,j)) = one.eval (fun j => x (i,j)) := by
      funext j
      simp [f,ea,cell,hx]
    rw [ev]
    obtain ⟨geometry,present⟩ := he p r row dummy _ ready
    exact ⟨geometry,present⟩

/-- The routed input used by a normalized execution is the same original network and the
same integral move data passed to the public subdivision. Only its depth index is transported. -/
theorem actual_initial {D d j : ℕ} {P : Type} {K : Type*} [CommSemiring K] {bits : P → ℕ}
    (hh : 0<h) (z : PlacedPack D P bits K (Cube D) j) (init : InitialSites z L hh)
    (p : Pack D P bits K) (r : SiteRoutes p (Cube D) d L) (level : j=d)
    (pack : init.pack=p) (routes : HEq init.routes r) : HEq z (r.initialPlacedPack hh) := by
  subst d
  subst p
  have eq := eq_of_heq routes
  subst r
  exact heq_of_eq init.realizes

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI
