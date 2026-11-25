import OAI.Hierarchy.DescentResidentDonorNames
import OAI.Hierarchy.DescentIssuedChronology
import OAI.Hierarchy.DescentPackedCensusInvoice
import OAI.Hierarchy.DescentChronologicalGrains

namespace OAI
/-! # Names, selector choice and counter values at the actual incoming ordinary stage -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentStageEdgeReceipt
noncomputable section
variable {F P : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {dim k : ℕ}
    {bits : P→ℕ} {q ε : ℝ} {W₀ W₁ W₂ : MarkedWorld F dim P bits}
    {i₀ z₀ D₀ i z D i₂ z₂ D₂ wire hist : ℕ}
    {first : Reached W₀ G q ε S k i₀ z₀ D₀ wire hist} {middle : Reached W₁ G q ε S k i z D wire hist}
    {last : Reached W₂ G q ε S k i₂ z₂ D₂ wire hist}

theorem Path.site_named (path : Path first middle)
    (start : first.placement.SiteNamed (groupRank Fin.valEmbedding (first.vertex.trans Fin.valEmbedding))) :
    middle.placement.SiteNamed (groupRank Fin.valEmbedding (middle.vertex.trans Fin.valEmbedding)) := by
  cases path with
  | here=>exact start
  | ordinary prev ticket=>exact (Reached.donor_names _ (Nat.zero_lt_succ _)).1
  | reset prev b=>exact (b.next.donor_names (Nat.zero_lt_succ _)).1

variable {rate : ℝ} {he : 0≤ε} {T : StageInput W₁ G rate ε} {choice : (T.result he).Choice}
    {norm : Normalize ((T.result he).state choice)} {z' D' : ℕ}
    {target : Reached norm.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink middle he T choice norm target)

include ticket in
theorem OrdinaryLink.stage_choice : ∃actual : (middle.placement.stage.result he).Choice, HEq choice actual := by
  obtain rfl:=ticket.sourceRate
  obtain rfl:=eq_of_heq ticket.placement
  exact ⟨choice,HEq.rfl⟩

theorem OrdinaryLink.observed_mass {p : ℕ} (before : Path first middle) (tail : Path target last) {run : Path first last}
    (cut : (before.ordinary ticket).append tail=run) (dates : run.GrainDates p)
    (height : 0<S.height) (age : i≤S.length)
    (wireSize : wire=S.epochPower^S.priceExponent) (branch : G.b≤2^S.capGain) :
    middle.placement.wire*(middle.placement.z*G.b)*middle.placement.cap<2^(S.censusBits p) := by
  exact (middle.placement.census_caps S middle.valid height age
    (ticket.quantum.symm.trans (ticket.grain_on_cut before tail cut dates)) (middle.edges.trans wireSize) branch).2

end
end Hierarchy.DescentSixParty.Chronology

end OAI
