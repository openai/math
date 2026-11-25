import OAI.Computability.BorderVNP.ShortenEpochRoundClosure

/-!
# Flattening the external ports of an actual output at sites

The row-major port equivalence gives the ordinary site pack for the next
epoch. Its entire integral site routing, width and endpoint populations
are transported exactly. In the record count the only relabelled summands
are the external port descriptors.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.SiteRoutes

open BorderVNP.Crossing BorderVNP.Epoch BorderVNP.Epoch.Round BorderVNP.Shortening BorderVNP.Shortening.Adaptive Finset
open scoped Classical

variable {I P : Type} [Fintype I] {D k b d : ℕ} {L : ℝ} {bits : P → ℕ} {R : Type*}
variable {p : Pack D (Port k P b) (width bits k b) R} (s : SiteRoutes p I d L)

/-- Integral routes on the ordinary flat external port list of this site pack. -/
noncomputable def flatten : SiteRoutes (flattenPack b p) I d L where
  origin := s.origin
  active := s.active
  step := s.step
  aligned := s.aligned

/-- Source and destination addresses and incident widths are the original ones. -/
theorem flatten_width_incidence :
    s.flatten.nonlocalWidth = s.nonlocalWidth ∧ s.flatten.incidence = s.incidence ∧
    s.flatten.incidenceConcentration = s.incidenceConcentration := ⟨rfl,rfl,rfl⟩

/-- Flattening the external labels preserves the exact site potential. -/
theorem flatten_potential (weight : ℝ) : s.flatten.potential weight = s.potential weight := rfl

/-- A free port labelled by its flat row-major index still attaches to the same site. -/
theorem flatten_port_site (z : Port k P b) :
    s.flatten.site ((flattenPack b p).layout.attach (portEquiv k P b z)) = s.site (p.layout.attach z) := by
  change s.site (p.layout.attach ((portEquiv k P b).symm ((portEquiv k P b) z))) = _
  rw [Equiv.symm_apply_apply]

/-- All descriptor and expanded record counts agree, even for an arbitrary set of sites. -/
theorem flatten_records [Fintype P] [Fintype (Port k P b)] (p : Pack D (Port k P b) (width bits k b) R)
    (ex : Bool) (prior payload : p.layout.Site → ℕ) (test : p.layout.Site → Prop) :
    localRecords (flattenPack b p).layout ex prior payload test = localRecords p.layout ex prior payload test := by
  classical
  unfold localRecords testedWidth
  apply congrArg₂ Nat.add rfl
  rw [← Equiv.sum_comp (portEquiv k P b) (fun z => if test ((flattenPack b p).layout.attach z)
    then recordCost ex (bits z.2) else 0)]
  apply sum_congr rfl
  intro z _
  change (if test (p.layout.attach ((portEquiv k P b).symm ((portEquiv k P b) z))) then
      recordCost ex (bits ((portEquiv k P b z).2)) else 0) = _
  rw [Equiv.symm_apply_apply,← width_portEquiv bits k b z]

end Cover.SiteRoutes

end BorderVNP
end Computability
end OAI
