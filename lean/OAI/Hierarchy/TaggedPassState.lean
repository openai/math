import OAI.Hierarchy.TaggedSortedBlock
import OAI.Hierarchy.TaggedPassRead
import OAI.Hierarchy.TaggedLocalDestinationData

namespace OAI
/-! # The deterministic row map and its canonical block inputs for each digit -/

namespace Hierarchy.Tagged.Radix.PassShape
open ThreeFlat Routing SortNetwork RadixStage
open SortedBlock CorrectionFrame
open scoped Classical
noncomputable section

variable {w d : ℕ} (s : PassShape) (dummy : Fin w → Bool) (real isDummy : Fin w) (digit : Fin s.digitBits → Fin w)

def shapeFlags (n : ℕ) (real isDummy : Fin w) (x : RowBits n w → Bool) :=
  ∀ i, x (i,isDummy) = !(x (i,real))

def sortData {l k w : ℕ} (digit : Fin k → Fin w) (x : SortRelation.Data l w → Bool) := SortNetwork.pack (stable digit (unwrap x))

def byBlock {I O : Type*} {n : ℕ} (f : (I → Bool) → O → Bool) (x : Fin n × I → Bool) (i : Fin n × O) :=
  f (fun j => x (i.1,j)) i.2

def alignData {j t d w : ℕ} (digit : Fin d → Fin w) (real : Fin w) (x : SortRelation.Data (j+t) w → Bool) :=
  SortNetwork.pack (align digit real (unwrap x))

def localSortRun := byBlock (n := s.blocks) (sortData (l := s.localBits) (maskedDigit digit isDummy))

def localAlignRun := byBlock (n := s.blocks) (alignData (j := s.packBits) (t := s.upperBits) digit real)

def run : (RowBits s.rows w → Bool) → (RowBits s.nextRows w → Bool) :=
  staticRead s.leave ∘ sortData (s.wideDigit digit isDummy) ∘ staticRead (s.wideInput dummy) ∘
    s.localAlignRun real digit ∘ s.localSortRun isDummy digit ∘ staticRead (s.enter dummy)

private theorem enter_word (x : RowBits s.rows w → Bool) (b : Fin s.blocks) (i : Row s.localBits) :
    unwrap (fun k => staticRead (s.enter dummy) x (b,k)) i =
      if i.val < s.block then if h : b.val*s.block+i.val < s.rows then fun j => x (⟨_,h⟩,j) else dummy else dummy :=
  s.enter_block_word dummy x b i

theorem local_ok (space : s.packBits+2 ≤ s.digitBits) (blank : dummy real = false) (comp : dummy isDummy = !(dummy real))
    (x : RowBits s.rows w → Bool) (valid : shapeFlags s.rows real isDummy x) (b : Fin s.blocks) :
    AlignedInput digit real (unwrap (fun i => (s.localSortRun isDummy digit (staticRead (s.enter dummy) x)) (b,i))) := by
  let input := unwrap (fun k => staticRead (s.enter dummy) x (b,k))
  have sane (i : Row s.localBits) : input i isDummy = !(input i real) := by
    dsimp [input]; rw [enter_word]; split <;> first | (split <;> first | exact valid _ | exact comp) | exact comp
  have support (i : Row s.localBits) : input i real = true → i.val < s.block := by
    intro hi
    by_contra! h
    simp [input,enter_word,not_lt.mpr h,blank] at hi
  change AlignedInput digit real (unwrap (SortNetwork.pack (stable (maskedDigit digit isDummy) input)))
  rw [unwrap_pack]
  refine ⟨sort_prefix digit real isDummy input sane,sorted_digit digit real isDummy input sane,?_⟩
  have le := bound (maskedDigit digit isDummy) real input support
  have vol := s.local_height space
  have same : s.localBits = 2*s.digitBits+1 := by unfold localBits upperBits; omega
  calc
    _ ≤ s.block + 2^s.digitBits*2^s.packBits := Nat.add_le_add_right le _
    _ ≤ s.perBlock := by unfold perBlock Radix.PassShape.pack; rw [Nat.add_mul]; omega
    _ ≤ 2^(2*s.digitBits+1) := vol
    _ = _ := congrArg (fun n => (2:ℕ)^n) same.symm

def localOut (x : RowBits s.rows w → Bool) :=
  s.localAlignRun real digit (s.localSortRun isDummy digit (staticRead (s.enter dummy) x))

theorem aligned_input (room : s.packBits+2 ≤ s.digitBits) (blank : dummy real = false) (flags : dummy isDummy = !(dummy real))
    (x : RowBits s.rows w → Bool) (valid : shapeFlags s.rows real isDummy x) (b : Fin s.blocks) :
    AlignedInput digit real (s.blockWord (s.localSortRun isDummy digit (staticRead (s.enter dummy) x)) b) :=
  s.local_ok dummy real isDummy digit room blank flags x valid b


end
end Hierarchy.Tagged.Radix.PassShape

end OAI
