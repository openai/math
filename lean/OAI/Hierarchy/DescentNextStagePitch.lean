import OAI.Hierarchy.DescentIncomingPitchNumber
import OAI.Hierarchy.DescentResetSignedTokenKey
import OAI.Hierarchy.DescentDatedOrdinaryArea
import OAI.Hierarchy.DescentGrainCalendar

namespace OAI
/-! # The normalized incoming width at a public epoch, ordinary slot or final tape -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentPackedWalsh DescentPacking.PackedMatch.Local.Stage DescentResetSignedTokens
noncomputable section

namespace NativePitch
variable (S:AtomSchedule) (k tail p f payload:ℕ) (ordinary:ℕ→Dated.Ordinary)

variable {F P:Type} [Field F] {d D n C i h₀ z g cut wire hist:ℕ}
  {bs:P→ℕ} {W:MarkedWorld F d P bs} {G:PoweredGadget F} {q ε:ℝ}
theorem both_signed (r:Reached W G q ε S k i z D wire hist) (rates:ResetRates G S k D n h₀ C f g cut tail)
    (alive:i<S.length)(boundary:i%(S.rounds+1)=S.rounds)(H groups short:ℕ)
    (small:8*S.localWalshBits p (S.groupWidth k tail i+k) f (quota S.rounds)≤payload):
    let M:=incoming S k tail p f payload ordinary i
    let s:=datedLayout r.placement H groups M (2^(resetCut S k tail p f payload i)) short
    s.bits*s.sourceLanes≤payload/2 ∧ s.bits*s.targetLanes≤payload/2:=by
  simp only [incoming,ite_eq_left alive,ite_eq_left boundary]
  exact reached_both_keys r rates p payload H groups _ short alive.le small (Nat.sub_le ..)

end NativePitch
end
end Hierarchy.DescentSixParty

end OAI
