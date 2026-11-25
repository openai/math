import OAI.Hierarchy.DescentResetSignedTokenShape
import OAI.Hierarchy.DescentResetCanvasAmount

namespace OAI
/-! # Numeric layout of the reset canvas ingress -/
namespace Hierarchy.DescentResetCanvasIngress
open DescentSIMDLookup ProtocolRAM
noncomputable section
structure Layout extends DescentResetSignedTokens.Layout where
  oldBits : ℕ
  bits : ℕ
  hist : ℕ
  unitFee : ℕ
namespace Layout
variable (s : Layout)
abbrev signed := s.toLayout
def amounts : DescentVenueSlabs.Shape := ⟨2^s.k,s.hosts,s.groups,s.sourceLanes,s.targetLanes,s.oldBits⟩
def collector : DescentResetCanvasAmount.Layout := ⟨s.hosts,s.groups,s.targetLanes,2^s.k,s.degree,s.cap,
  s.oldBits,s.bits,s.hist,s.unitFee⟩
def signedEnd (base : ℕ) := s.signed.endAddress base
def atomEnd (base : ℕ) := DescentVenueSlabs.endAddress s.amounts (s.signedEnd base)
def atomBank (base : ℕ) (x : Fin (2^s.k)) := DescentVenueSlabs.page s.amounts (s.signedEnd base) x.val
def endAddress (base : ℕ) := s.collector.endAddress (s.atomEnd base)

end Layout
end
end Hierarchy.DescentResetCanvasIngress

end OAI
