import OAI.Computability.BorderVNP.DiagonalTallyAllocatedInputsDirectory
import OAI.Computability.BorderVNP.PackedBottomReportBundle

/-! # The true one-copy private placement supplies each allocated scanner site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open RoutingISA Packing.BottomReports Packing.BundleDirectory

/-- The site intervals follow from the actual slot writes of the private placement pass.
The original supplied count and fixed report gap precede the cumulative private string
volume of this cell, including descriptions with identical six-word headers. -/
theorem siteIntervals_of_placement {w : ℕ} {l : ReportLayout} (cs : List (ReportCell l))
    (place : PrivatePlacement.Layout) (before placed : ℕ → ℕ) (img : place.Image before place.entries placed)
    (fit : place.Fits w before) (receive stride : ℕ) {C : ℕ}
    (owner : Fin place.entries → Fin C) (src : Fin place.entries → ReportBundle)
    (owns : ∀ j, place.owner before j.val=(owner j).val)
    (grouped : ∀ c∈cs, c.bundles=(sourceRows owner c.number).map src)
    (physical : ∀ j, (src j).header.siteSlot =
      placed (receive+2*placed (place.raw+2*j.val)+1)+placed (place.raw+2*j.val+1))
    (banks : ∀ c∈cs, c.external=placed (receive+2*c.number+1) ∧ c.supplied=before (place.supplied+c.number))
    (tailGap : ∀ c∈cs, c.tailWidth ≤ place.gap)
    (volume : ∀ c∈cs, c.supplied+place.gap+placed (place.scratch+c.number) ≤ stride) :
    SiteIntervals cs place.desc stride := by
  intro c hc b hb
  rw [grouped c hc,List.mem_map] at hb
  obtain ⟨j,hj,rfl⟩ := hb
  have realOwner := (owns j).trans (mem_sourceRows.mp hj)
  have hn : c.number < place.cells := realOwner ▸ fit.owners j.val j.isLt
  have addr := physical j
  rw [img.owner_eq fit j.isLt,img.slots _ j.isLt,realOwner] at addr
  obtain ⟨bank,supplied⟩ := banks c hc
  rw [←bank,←supplied] at addr
  let cnt := fun i => PrivatePlacement.prefixCounts (place.owner before) place.desc i c.number
  have mono : Monotone cnt := monotone_nat_of_le_succ fun i => by
    simp [cnt,PrivatePlacement.prefixCounts,Finset.sum_range_succ]
  have succ : cnt (j.val+1)=cnt j.val+place.desc := by simp [cnt,PrivatePlacement.prefixCounts,Finset.sum_range_succ,realOwner]
  have bound := mono j.isLt
  rw [succ] at bound
  have total := img.counters c.number hn
  change placed (place.scratch+c.number)=cnt place.entries at total
  change (src j).header.siteSlot=c.external+(c.supplied+place.gap+cnt j.val) at addr
  have gap := tailGap c hc
  have endAddr := volume c hc
  omega

/-- A physical bottom bundle, including the padded grid's reportBundle, has the
native private-row arithmetic bounds from its actual original marked sources and
reserved one-copy lane capacity. -/
theorem physicalBundle_siteRoom (h : BundleHeader) (body original : List CellSparse.Factor) (bank : ℕ → Bool)
    (l : ReportLayout) (w description : ℕ)
    (bodyRoom : (CellSparse.Packet.Source.boxBody body).length ≤ l.bodyCap)
    (descriptionRoom : l.fieldWidth+l.bodyCap+(TallySidecar.bits l.fieldWidth (positions h.orig original)).length ≤ description)
    (values : TallySidecar.Fits l.fieldWidth (positions h.orig original))
    (capacity : count original ≤ h.cap) (endAddr : h.boxBase+(h.orig+h.cap)<2^w) :
    (physicalBundle h body original bank).SiteRoom l w description := by
  refine ⟨bodyRoom,descriptionRoom,values,?_,?_,?_⟩
  · simpa only [physicalBundle,positions_length] using capacity
  · simp only [physicalBundle,positions_length]
    omega
  · intro i hi
    change i < (positions h.orig original).length at hi
    have hcount : i<count original := (positions_length h.orig original) ▸ hi
    have entry := congrArg (fun xs : List ℕ => xs[i]?) (positions_ranks h.orig original)
    have hg : i < (List.range' h.orig (count original)).length := by simpa using hcount
    simp only [List.getElem?_map,List.getElem?_eq_getElem hi,List.getElem?_eq_getElem hg,Option.map_some,
      Option.some.injEq,List.getElem_range'] at entry
    simp only [ReportBundle.relative,physicalBundle,List.getElem?_eq_getElem hi,Option.map_some,Option.getD_some,entry]
    omega

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
