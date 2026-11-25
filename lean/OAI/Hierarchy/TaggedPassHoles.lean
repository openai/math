import OAI.Hierarchy.TaggedPassGeometry
import OAI.Hierarchy.TaggedRadixStages
import OAI.Hierarchy.CorrectionFrame
import OAI.Hierarchy.TaggedData

namespace OAI
/-! # The three oracle sockets and their exact exposed weight in a radix pass -/

namespace Hierarchy.Tagged.Radix.PassShape
open RadixStage CorrectionFrame
open scoped Classical
noncomputable section

def upperBits (s : PassShape) := 2*s.digitBits+1-s.packBits
def localBits (s : PassShape) := s.packBits+s.upperBits

def sourceArity (s : PassShape) (w : ℕ) := s.blocks*pins s.localBits (s.localBits+w)
def alignArity (s : PassShape) (w : ℕ) := s.blocks*pins s.localBits w
def wideArity (s : PassShape) (w : ℕ) := pins s.globalHeight (s.globalHeight+s.pack*w)

abbrev PassHoles (s : PassShape) (w : ℕ) :=
  ((((Empty ⊕ Fin (s.sourceArity w)) ⊕ Fin (s.alignArity w)) ⊕ Empty) ⊕ Fin (s.wideArity w)) ⊕ Empty

/-- Hole numbering groups the two parallel banks and the global tagged sort. -/
def holeEquiv (s : PassShape) (w : ℕ) : s.PassHoles w ≃
    Fin (s.sourceArity w) ⊕ (Fin (s.alignArity w) ⊕ Fin (s.wideArity w)) :=
  (Equiv.sumEmpty _ _).trans ((Equiv.sumCongr
      ((Equiv.sumEmpty _ _).trans (Equiv.sumCongr (Equiv.emptySum _ _) (Equiv.refl _)))
      (Equiv.refl _)).trans (Equiv.sumAssoc _ _ _))

def weight (F : Type*) [CommSemiring F] (s : PassShape) (w : ℕ) : (s.PassHoles w → Bool) → F :=
  pairWeight (pairWeight (pairWeight (pairWeight (pairWeight (fun _ => 1)
    (dataProduct s.blocks (coeff F s.localBits (s.localBits+w))))
    (dataProduct s.blocks (coeff F s.localBits w))) (fun _ => 1))
    (coeff F s.globalHeight (s.globalHeight+s.pack*w))) (fun _ => 1)

end
end Hierarchy.Tagged.Radix.PassShape

end OAI
