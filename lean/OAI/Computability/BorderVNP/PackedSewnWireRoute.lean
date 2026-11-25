import OAI.Computability.BorderVNP.PackedSewnWireImage
import OAI.Computability.BorderVNP.PackedFinalTieSewn

/-! # Retained cable fragments on a real routed terminal assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField.WireFragments

open Crossing Shortening Shortening.PublicCapacity Cover PackedHistoryCircuit Inherited Inherited.WorkWords
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport VPVNP.VerifierNetwork
open scoped Classical

variable {D q d w C b n : ℕ} {A P K : Type} [Fintype A] {I : Type} [Fintype I] {bits : A → ℕ}
    (enum : Fin q ≃ I) (number : (I → Deck (d+1)) ≃ Fin C) (cf : C ≤ 2^b)
    (L : Pack D A bits K) {dist : ℝ} (r : SiteRoutes L I d dist) {s : Shape} (rows : Rows s L.layout)
    (dummy : Fin s.edges → L.layout.Site) (ports : A ↪ Fin n) (vf : s.sites ≤ 2^w)
    (hosts widths : Fin n → ℕ) {σ : Type} [Fintype σ]
    (route : Frame σ (RouteRows.Pins (allowedMoves I dist) q (d+1) s.sites s.edges w))
    (aux : Frame σ (Fin s.sites × Fin w)) (x : σ → Bool)
    (p : Params) (hp : p.Valid) (lane : P ↪ Σ a, Fin (bits a))
    {physical : PublicPort p.R p.processors p.literal p.link ≃ P}
    (h : BlockHosts (FineView.layout L.layout lane) physical p.g) (name : ℕ → ℕ → ℕ)
local notation3 (prettyPrint := false) "F" => TerminalCells.fields (Move:=allowedMoves I dist) (q:=q) (d:=d) (E:=s.edges) vf cf hosts widths
local notation3 (prettyPrint := false) "source" => TerminalCells.boundFrame enum number cf route aux
local notation3 (prettyPrint := false) "after" => withSewnFields source
local notation3 (prettyPrint := false) "wire" => sewnFrame F p name FinalTies.routePresent
local notation3 (prettyPrint := false) "cell" => fun v => number (reduceMove d (r.origin v))
local notation3 (prettyPrint := false) "part" => wireInterval L.layout lane h.bundle (fun _ : FreeBlock p.R p.sites => p.g)
  h.groupOwner rows.edge ports (mergedEdges p hp rows.edge) finProdFinEquiv.toEmbedding

/-- A true physical route directory supplies both endpoint scans, the cable
presence flags and the numerical site names needed by every retained-wire fragment. -/
theorem routed_siteRuns (ready : RouteRows.Ready enum L r rows dummy (route.eval x))
    (portAddr : ∀ z, hosts (ports z) = (rows.site (L.layout.attach z)).val)
    (portWidth : ∀ z, widths (ports z) = bits z) (portRoom : ∀ i, widths i < 2^w)
    (portHole : ∀ i ∉ Set.range ports, widths i=0) (amount : L.layout.Site → ℕ)
    (covered : WorkWords.Covers rows.site amount aux x)
    (host : ∀ (u : Fin (p.R+1)) i, i < p.sites → name u.val i = (rows.site (h.host (u,i))).val)
    (groupRoom : p.g < 2^w) (oldFit : ∀ v, incoming L.layout v < 2^w)
    (newFit : ∀ v, incoming (finalLayout p h) v < 2^w) (v : L.layout.Site) :
    (Fragment.siteRuns (rows.site v).val (Fragment.list ((wire).eval ((after).eval x)))).Perm
      (((Finset.univ.toList : List (Incident L.layout v)).map (part v)).filter (fun a => decide (0<a.width))) := by
  have checked := TerminalCells.route_represents enum number L r rows dummy ports vf cf hosts widths
    portAddr portWidth portRoom portHole route aux x ready amount covered.live covered.hole
  have post := frame_represents p hp L.layout lane h cell amount rows.site rows.edge ports F source x checked name host groupRoom
  have previous : (after).eval x ∘ Sum.inl = (source).eval x := by
    funext z; simp only [withSewnFields,Frame.subst_eval,constants_eval,Function.comp_apply,Sum.elim_inl]
  have data : Views.EndpointData L.layout F rows.site rows.edge ports ((after).eval x ∘ Sum.inl) := by
    rw [previous]
    exact Views.EndpointData.of_rep L.layout F rows.site rows.edge ports checked
  have used (i : Fin s.edges) : (after).eval x (.inl (FinalTies.routePresent i)) = true ↔ i ∈ Set.range rows.edge := by
    have read := congrFun previous (FinalTies.routePresent i)
    change (after).eval x (.inl (FinalTies.routePresent i)) = (source).eval x (FinalTies.routePresent i) at read
    rw [read]
    exact FinalTies.route_present enum number cf L r rows dummy route aux x ready i
  rw [List.filter_map]
  exact sewn_siteRuns L.layout rows.site rows.edge ports F p name FinalTies.routePresent hp lane h ((after).eval x)
    data (Views.EndpointData.of_rep _ _ _ _ _ post) oldFit newFit used v Finset.univ.toList
    Finset.univ.nodup_toList (fun z => by simp)

end Packing.SewnField.WireFragments

end BorderVNP
end Computability
end OAI
