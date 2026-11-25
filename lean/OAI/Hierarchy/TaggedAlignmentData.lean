import OAI.Hierarchy.TaggedSortedKeys

namespace OAI
/-! # Indexed digit readings and order conditions in a real prefix -/

noncomputable section
namespace Hierarchy.Tagged
open ThreeFlat Routing SortNetwork
open ExactQuantumFactoring
open scoped Classical

namespace AlignRows
def digitValue {h d w : ℕ} (digit : Fin d → Fin w) (input : Records h w) (i : Row h) : BitVec d :=
  bitsValue (input i ∘ digit)

def Ordered {d j t w : ℕ} (real : Fin w) (digit : Fin d → Fin w) (input : Records (j+t) w) : Prop :=
  ∀ e : Edge (j+t), input e.1 real = true → input (next e) real = true →
    (digitValue digit input e.1).toNat ≤ (digitValue digit input (next e)).toNat

end AlignRows

namespace AlignBlock
open AlignRows
variable {d j t w : ℕ} (real : Fin w) (digit : Fin d → Fin w) (input : Records (j+t) w)

def key (i : Row (j+t)) : Row d := (digitValue digit input i).toFin

def initial (r : ℕ) : Prop := ∀ i : Row (j+t), input i real = true ↔ i.val < r

end AlignBlock
end Hierarchy.Tagged

end
end OAI
