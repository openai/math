import OAI.Computability.NearSquareRoot.CRTControlledPrefixStage
import OAI.Computability.NearSquareRoot.CRTControlledCross
import OAI.Computability.NearSquareRoot.CRTPositionPairs

/-! # Native chunk positions and the binary prefix view -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication.Adic IntegerMultiplication.Strip

theorem lowPrefixBit {p n k : ℕ} (size : p+n=k) (a : Block 2 p) (b : Block 2 n)
    (j : Fin n) : prefixBit ((prefixView size).cast (a,b)) ⟨j.val,by omega⟩ = prefixBit b j := by
  simp only [prefixBit,prefixView_least,List.getElem_append_left (by simp : j.val < (least b).length)]

theorem highPrefixBit {p n k : ℕ} (size : p+n=k) (a : Block 2 p) (b : Block 2 n)
    (j : Fin p) : prefixBit ((prefixView size).cast (a,b)) ⟨n+j.val,by omega⟩ = prefixBit a j := by
  simp only [prefixBit,prefixView_least,List.getElem_append_right (by simp : (least b).length ≤ n+j.val),length',
    Nat.add_sub_cancel_left]

theorem chunkFactor (k : ℕ) : k%3 + crossWidth (k/3) = k := by unfold crossWidth; omega

theorem bulkPrefixBit (k : ℕ) (a : Block 2 (k%3)) (b : Block 2 (crossWidth (k/3)))
    (c : Fin 3) (j : Fin (k/3)) :
    prefixBit ((prefixView (chunkFactor k)).cast (a,b)) ((threeChunksWithTail k).symm (.inl (c,j))) =
      crossBits b (c.rev,j) := by
  have e : ((threeChunksWithTail k).symm (.inl (c,j))) =
      (⟨(crossPort (k/3) (c.rev,j)).val,by have := (crossPort (k/3) (c.rev,j)).isLt; have := chunkFactor k; omega⟩ : Fin k) := by
    apply Fin.ext
    rw [threeChunksWithTail_bulk]
    fin_cases c <;> simp [crossPort,Fin.rev,Nat.mul_comm,Nat.add_comm]
  rw [e]
  exact lowPrefixBit (chunkFactor k) a b (crossPort _ (c.rev,j))

theorem tailPrefixBit (k : ℕ) (a : Block 2 (k%3)) (b : Block 2 (crossWidth (k/3)))
    (j : Fin (k%3)) :
    prefixBit ((prefixView (chunkFactor k)).cast (a,b)) ((threeChunksWithTail k).symm (.inr j)) = prefixBit a j := by
  have e : ((threeChunksWithTail k).symm (.inr j)) =
      (⟨crossWidth (k/3)+j.val,by have := chunkFactor k; omega⟩ : Fin k) := by
    apply Fin.ext; rw [threeChunksWithTail_tail]; simp [crossWidth]; omega
  rw [e]
  exact highPrefixBit (chunkFactor k) a b j

@[simp] theorem underPrefix_pair {p n k : ℕ} (size : p+n=k) (f : Block 2 n → Block 2 n)
    (a : Block 2 p) (b : Block 2 n) :
    underPrefix size f ((prefixView size).cast (a,b)) = (prefixView size).cast (a,f b) := by simp [underPrefix]

end Controlled

end NearSquareRoot
end Computability
end OAI
