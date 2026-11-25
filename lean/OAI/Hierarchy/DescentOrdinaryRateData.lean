import OAI.Hierarchy.DescentCalendarNumbers

namespace OAI
/-! # Eight stage-wide inequalities governing the ordinary period -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentHostDegree
variable {F : Type} [Field F]

structure OrdinaryRates (G : PoweredGadget F) (S : AtomSchedule) (k f : ℕ) : Prop where
  height : 0<S.height
  radix : S.radix=2^k
  adr : k=groupBits S.rounds S.height S.hostGain S.capGain f
  host : ∀j<S.rounds,2*(2^packExponent 20 (atRound j)+2)≤2^S.hostGain
  gain : ∀j<S.rounds,2^gainExponent 20 (atRound j)*G.b≤2^S.capGain
  fineGain : ∀j<S.rounds,2^gainExponent 20 (atRound j)*G.b≤2^(S.capGain-(G.b+3))
  cut : ∀j<S.rounds,packExponent 20 (atRound (j+1))≤f
  room : ∀j<S.rounds,gainExponent 20 (atRound j)≤k

end Hierarchy.DescentSixParty

end OAI
