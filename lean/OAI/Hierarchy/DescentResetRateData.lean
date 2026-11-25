import OAI.Hierarchy.DescentOrdinaryRateData
import OAI.Hierarchy.DescentResetRateNumbers
import OAI.Hierarchy.DescentResetPublicDepth
import OAI.Hierarchy.DescentRoundQuota
import OAI.Hierarchy.DescentRotorTables
import OAI.Hierarchy.NonlinearExpanders

namespace OAI
/-! # A common physical rotor and its word size for an entire reset period -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentColonies DescentResetInvoice DescentBaseProfile DescentRotor DescentHostDegree
open NonlinearExpanders

/-- Numerical data common to every reached choice of the same ordinary period. -/
structure ResetRates {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) (k D n h C f g cut tail : ℕ) where
  board : Graph n h
  bitsR : ℕ
  enough : 4*quota S.rounds≤2^n
  degree : D*2^decayExponent D≤quota S.rounds
  bits_positive : 0<bitsR
  rows : (2^n)^2*bitsR≤2^f
  menu : ∀π : Equiv.Perm (Fin (2^n)),Configures F board.arcs C bitsR π
  loss : 128*resetTail f+4*(quota S.rounds:ℝ)^2/(2:ℝ)^f≤1/(nonhubHops D (2^n):ℝ)
  base : S.baseGroups=2^tail
  radix : S.radix=2^k
  fixed : k=groupBits S.rounds S.height S.hostGain S.capGain cut
  height : 0<S.height
  fcut : f≤cut
  gk : g≤k
  gain : g=reserveGain h C f
  host : ResetInput.resetHostGain h (2^n) (GroupStage.depthBound D n f g)≤S.hostGain
  cap : g≤S.capGain
  fineCap : g≤S.capGain-(G.b+3)
  seed : packExponent 20 3≤cut

end Hierarchy.DescentSixParty

end OAI
