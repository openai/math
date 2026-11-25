import OAI.Hierarchy.DescentIssuedChronology

namespace OAI
/-! # Recover the precise ordinary degree from the public capacity-calendar digit -/
namespace Hierarchy.DescentSixParty.Chronology.OrdinaryLink
open DescentCompiler DescentHostDegree DescentKernelHistory DescentStageEdgeReceipt DescentInitialHost Catalyst
open DescentRotor DescentPacking DescentColonies

section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {q ε u : ℝ} {S : AtomSchedule}
  {W : MarkedWorld F d P bits} {k age z D z' D' wire hist : ℕ}
  {source : Reached W G q ε S k age z D wire hist} {he : 0≤ε} {T : StageInput W G u ε}
  {c : (T.result he).Choice} {n : Normalize ((T.result he).state c)}
  {target : Reached n.result G q ε S k (age+1) z' D' wire hist}
  (link : OrdinaryLink source he T c n target)

theorem public_degree : publicDegree S.rounds G.b link.factor=source.placement.degree := by
  obtain ⟨j,hj,code⟩:=link.degreeSlot
  rw [publicDegree,link.degreeClass_factor,source.branch,code,roundFor_exact hj]
  rfl

theorem public_degree_at {X Y : MarkedWorld F d P bits} {start zz₀ dd₀ finish zz₁ dd₁ : ℕ}
    {first : Reached X G q ε S k start zz₀ dd₀ wire hist}
    {last : Reached Y G q ε S k finish zz₁ dd₁ wire hist}
    (before : Path first source) (later : Path target last) (calendar : List ℕ)
    (schedule : ((Path.ordinary before link).append later).capFactors=calendar) :
    publicDegree S.rounds G.b ((calendar.drop (age-start)).head?.getD 0)=source.placement.degree := by
  rw [link.factor_at before later calendar schedule]
  exact link.public_degree

end
end Hierarchy.DescentSixParty.Chronology.OrdinaryLink

end OAI
