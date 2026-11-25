import OAI.Hierarchy.GridPinPublisherLayout

namespace OAI
/-! # Source intervals read by the physical program header -/
namespace Hierarchy.GridPinHeaderNative

def source (B : Banks) (a : ℕ) : Prop :=
  (B.textBase≤a ∧ a<B.textBase+B.text) ∨
  (B.operandBase≤a ∧ a<B.operandBase+B.operandBits) ∨
  (B.selectorBase≤a ∧ a<B.selectorBase+B.selector)

end Hierarchy.GridPinHeaderNative

end OAI
