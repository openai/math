import OAI.Computability.BorderVNP.PackedHistorySubdivisionLive

/-! # Vacant stripe rows of the geometric subdivision -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.RouteRows

open Shortening Shortening.PublicCapacity Shortening.PublicEndpoints Crossing Cover Cover.AddressCircuit Epoch Packing.Names
open ParseBatchSort
open scoped Classical

variable {D q d w : ℕ} {P : Type*} {K : Type*} [CommSemiring K] {bits : P → ℕ}
    {I : Type*} [Fintype I] {L h : ℝ} (enum : Fin q ≃ I) (p : Pack D P bits K)
    (r : SiteRoutes p I d L) {s : Shape} (row : Rows s p.layout) (dummy : Fin s.edges → p.layout.Site)
    {x : Pins (allowedMoves I L) q (d+1) s.sites s.edges w → Bool} (ready : Ready enum p r row dummy x)

include ready in
/-- A stripe slot is occupied exactly when the original wire exists and the slot
is its first hop or it carries an active site motion. -/
theorem stripe_range (i : Fin s.edges) (j : Fin (⌈L/h⌉₊+1)) :
    edgeIndex s.edges ⌈L/h⌉₊ (i,j) ∈ Set.range (row.siteRoutes r h).edge ↔
      i ∈ Set.range row.edge ∧ (j.val=0 ∨ x (.inr (.inl i))=true) := by
  constructor
  · rintro ⟨⟨e,t⟩,ht⟩
    have he := (edgeIndex s.edges ⌈L/h⌉₊).injective ((live_edgeIndex p r row e t).symm.trans ht)
    obtain rfl : row.edge e = i := congrArg Prod.fst he
    refine ⟨⟨e,rfl⟩,?_⟩
    rw [ready.active e]
    by_cases ha : r.active e
    · exact Or.inr ha
    · have hv : t.val = j.val := congrArg (fun z => z.2.val) he
      have hi : (r.routes h).interior e = 0 := by simp [SiteRoutes.routes,ha]
      have hlt := t.isLt
      exact Or.inl (by omega)
  · rintro ⟨⟨e,rfl⟩,hj⟩
    rw [ready.active e] at hj
    have fits : j.val < (r.routes h).interior e+1 := by
      rcases hj with hz | ha
      · omega
      · simpa [SiteRoutes.routes,ha] using j.isLt
    let t : Fin ((r.routes h).interior e+1) := ⟨j.val,fits⟩
    exact ⟨⟨e,t⟩,(live_edgeIndex p r row e t).trans (congrArg (edgeIndex _ _) (Prod.ext rfl (Fin.ext rfl)))⟩

private noncomputable def publicName (n : ℕ) : Fin n ≃ Fin n :=
  (Fintype.equivFin (Fin n)).trans (finCongr (Fintype.card_fin n))

/-- A vacant hop refers to the old padded cable's source site. The input
and output padded layouts may use different finite naming permutations. -/
noncomputable def stripeDummy (i : Fin ((⌈L/h⌉₊+1)*s.edges)) : (r.subdivided h).layout.Site :=
  .inl ((layout p.layout row.edge dummy).src (rowSlot (((edgeIndex s.edges ⌈L/h⌉₊).symm (publicName _ i)).1)))

private theorem dummy_site (i : Fin s.edges) (j : Fin (⌈L/h⌉₊+1)) :
    ((row.siteRoutes r h).site (stripeDummy p r row dummy (rowSlot (edgeIndex s.edges ⌈L/h⌉₊ (i,j))))).val =
      (storedSite p.layout row.site row.edge dummy i true).val := by
  have hi : publicName _ (rowSlot (edgeIndex s.edges ⌈L/h⌉₊ (i,j))) = edgeIndex _ _ (i,j) :=
    (publicName _).apply_symm_apply _
  simp only [stripeDummy,hi,Equiv.symm_apply_apply]
  rfl

include ready in
/-- On unused slots both endpoint pointers name the specified dummy site,
and the width and the charge are zero. -/
theorem empty_stripe (i : Fin s.edges) (j : Fin (⌈L/h⌉₊+1))
    (vacant : edgeIndex s.edges ⌈L/h⌉₊ (i,j) ∉ Set.range (row.siteRoutes r h).edge) :
    let key := edgeIndex s.edges ⌈L/h⌉₊ (i,j)
    let f := cableFrame (allowedMoves I L) q (d+1) s.sites s.edges w ⌈L/h⌉₊
    (∀ side, value (fun b => f.eval x (key,.inr (.inr (side,b)))) =
      ((row.siteRoutes r h).site (stripeDummy p r row dummy (rowSlot key))).val) ∧
    value (fun b => f.eval x (key,.inr (.inl b))) = 0 ∧ f.eval x (key,.inl false) = false := by
  intro key f
  have miss := mt (stripe_range enum p r row dummy ready i j).mpr vacant
  have inactive : x (.inr (.inl i)) = false := by
    by_cases hi : i ∈ Set.range row.edge
    · exact Bool.eq_false_iff.mpr (fun h => miss ⟨hi,Or.inr h⟩)
    · exact ready.hole _ hi
  have zeroMiss : j.val=0 → i ∉ Set.range row.edge := fun hz hi => miss ⟨hi,Or.inl hz⟩
  constructor
  · intro side
    rw [cableFrame_pointer,inactive,dummy_site]
    by_cases hz : j.val=0
    · have unused := unused_row p.layout row.edge dummy i (zeroMiss hz)
      simp only [pointer,Bool.false_eq_true,ite_false,hz,ite_true,Pointer.value]
      rw [ready.names.addresses i side]
      cases side with
      | true => rfl
      | false => exact congrArg (fun a => (row.site a).val) (unused.2.1.trans unused.1.symm)
    · simpa [pointer,hz,Pointer.value] using ready.names.addresses i true
  · constructor
    · rw [cableFrame_width,inactive]
      by_cases hz : j.val=0
      · simpa [hz] using (ready.names.widths i).trans (unused_row p.layout row.edge dummy i (zeroMiss hz)).2.2
      · simp [hz]
    · exact (cableFrame_charge x i j).trans inactive

include ready in
/-- The Boolean occupancy flag identifies the exact range of the subdivision row embedding. -/
theorem stripe_present (i : Fin s.edges) (j : Fin (⌈L/h⌉₊+1)) :
    (cableFrame (allowedMoves I L) q (d+1) s.sites s.edges w ⌈L/h⌉₊).eval x
        (edgeIndex s.edges ⌈L/h⌉₊ (i,j),.inl true) = true ↔
      edgeIndex s.edges ⌈L/h⌉₊ (i,j) ∈ Set.range (row.siteRoutes r h).edge := by
  rw [cableFrame_present,stripe_range enum p r row dummy ready]
  by_cases hj : j.val=0
  · simpa [hj] using ready.present i
  · simp only [hj,ite_false,false_or]
    exact ⟨fun ha => ⟨by by_contra hn; simp [ready.hole i hn] at ha,ha⟩,And.right⟩

end PackedHistoryCircuit.RouteRows

end BorderVNP
end Computability
end OAI
