import OAI.Computability.BorderVNP.PackedHistorySubdivisionBatch
import OAI.Computability.BorderVNP.ShortenEnrichedSiteExecution
import OAI.Computability.BorderVNP.PackedHistoryNamedState

/-! # Installing the computed initial rows in the enriched physical history -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Shortening Shortening.PublicCapacity Shortening.PublicRelative Shortening.PublicSegments
open Crossing Cover Cover.AddressCircuit Epoch Epoch.Round Packing Normalized
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D q d j : ℕ} (enum : Fin q ≃ Cube D) {L h : ℝ} {P : Type} {bits : P → ℕ} {K : Type*} [CommSemiring K]

/-- Transport the computed subdivision directory to the exact leaf state of the geometric
execution. The underlying sparse row numbering, dummy sites, and bit assignment agree. -/
theorem initial_reads (hh : 0<h) (z : PlacedPack D P bits K (Cube D) j) (init : InitialSites z L hh)
    (p : Pack D P bits K) (r : SiteRoutes p (Cube D) d L) (level : j=d)
    (hp : init.pack=p) (hr : HEq init.routes r) {s : Shape} (row : Rows s p.layout)
    (dummy : Fin s.edges → p.layout.Site) {w : ℕ}
    (x : Fin (s.subdivide ⌈L/h⌉₊).edges ⊕ Raw (SiteFields D q d L h) (s.subdivide ⌈L/h⌉₊).sites
      (s.subdivide ⌈L/h⌉₊).edges w w → Bool)
    (read : (initialDirectory p r row dummy hh).Reads (SiteRoutes.startingSites (Cube D) L h)
      (segmentField enum (SiteRoutes.startingSites (Cube D) L h) (lev := d) rfl) x) :
    ∃ a : Directory z (s.subdivide ⌈L/h⌉₊).sites (s.subdivide ⌈L/h⌉₊).edges,
      HEq a (initialDirectory p r row dummy hh) ∧ a.Reads (SiteRoutes.startingSites (Cube D) L h)
        (segmentField enum (SiteRoutes.startingSites (Cube D) L h) (congrArg (·+1) level)) x := by
  subst d
  have h := eq_of_heq (actual_initial hh z init p r rfl hp hr)
  subst z
  exact ⟨_,HEq.rfl,read⟩

end PackedHistoryCircuit.RouteRows

namespace PackedHistoryCircuit.Normalized.SiteSchedule

open Shortening Shortening.PublicCapacity Shortening.PublicRelative Shortening.PublicSegments
open Crossing Cover Cover.AddressCircuit Epoch Epoch.Round Packing
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D m q d : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m}
    (S : SiteSchedule e) (enum : Fin q ≃ Cube D) (levels : S.FitsLevels d) (leaves : S.HasLeaves d)
    {P : Type} {bits : P → ℕ} (input : Fin (S.fanIn^S.rounds) → Pack D P bits K)
    (route : ∀ i, SiteRoutes (input i) (Cube D) (S.high d) S.budget) {s : Shape}
    (rows : ∀ i, Rows s (input i).layout) (dummy : ∀ i, Fin s.edges → (input i).layout.Site)
    {w : ℕ} {Aux : Type*} (aux : Fin (S.fanIn^S.rounds) → Aux)

include leaves in
/-- The initial named states of the genuine enriched traversal hold exactly the computed
Boolean row vectors, their actual physical directories, and the supplied retained metadata.
The original input tensor, integral route, and potential witnesses are the ones used
by the uniform site calibration. -/
theorem named_leaves
    (words : Fin (S.fanIn^S.rounds) → Fin (s.subdivide ⌈S.budget/S.radius⌉₊).edges ⊕
      Raw (RouteRows.SiteFields D q (S.high d) S.budget S.radius) (s.subdivide ⌈S.budget/S.radius⌉₊).sites
        (s.subdivide ⌈S.budget/S.radius⌉₊).edges w w → Bool)
    (reads : ∀ i, (RouteRows.initialDirectory (input i) (route i) (rows i) (dummy i) S.radius_pos).Reads
      (SiteRoutes.startingSites (Cube D) S.budget S.radius)
      (segmentField enum (SiteRoutes.startingSites (Cube D) S.budget S.radius) (lev := S.high d) rfl) (words i)) :
    let sites := s.subdivide ⌈S.budget/S.radius⌉₊
    let data := RouteRows.SiteFields D q (S.high d) S.budget S.radius
    ∃ flat : Fin (S.fanIn^S.rounds) → NamedState D P bits K (S.level d 0) sites.sites sites.edges
        (Fin sites.edges ⊕ Raw data sites.sites sites.edges w w) Aux,
    ∃ init : ∀ i, InitialSites (flat i).placed S.budget S.radius_pos,
      ∀ i, (init i).pack=input i ∧ (init i).routes.potential S.weight=(route i).potential S.weight ∧
        HEq (init i).routes (route i) ∧ (flat i).words = words i ∧ (flat i).payload = aux i ∧
        Catalog.PlacedAt (S.source.catalog 0) S.radius (flat i).placed ∧
        HEq (flat i).names (RouteRows.initialDirectory (input i) (route i) (rows i) (dummy i) S.radius_pos) ∧
        (flat i).names.Reads (SiteRoutes.startingSites (Cube D) S.budget S.radius)
          (segmentField enum (SiteRoutes.startingSites (Cube D) S.budget S.radius)
            (congrArg (·+1) levels.1)) (words i) := by
  intro sites data
  obtain ⟨states,init,hp,hcost,hr⟩ := leaves input route
  choose dirs he hrds using fun i => RouteRows.initial_reads enum S.radius_pos (states i).val (init i)
    (input i) (route i) levels.1 (hp i) (hr i) (rows i) (dummy i) (words i) (reads i)
  let flat (i : Fin (S.fanIn^S.rounds)) : NamedState D P bits K (S.level d 0) sites.sites sites.edges
      (Fin sites.edges ⊕ Raw data sites.sites sites.edges w w) Aux :=
    ⟨(states i).val,dirs i,words i,aux i⟩
  exact ⟨flat,init,fun i => ⟨hp i,hcost i,hr i,rfl,rfl,(states i).property,he i,hrds i⟩⟩

end PackedHistoryCircuit.Normalized.SiteSchedule

end BorderVNP
end Computability
end OAI
