import OAI.ThreeFlat.Diagonal.TraceBinaryWitness
import OAI.ThreeFlat.Diagonal.TraceCpuBits
import OAI.ThreeFlat.Diagonal.TracePhysicalAddress
import OAI.ThreeFlat.Diagonal.TraceClockSites

namespace OAI
/-! # Physical shared-bit addresses and local CPU/sort input pins -/

namespace ThreeFlat.Diagonal.TracePhysical

open Computability.VPVNP RAMSerialization TraceRows TraceSlots
variable {w r f S d : ℕ}

/-- Group the three categories of guesses into one address space without
creating any additional assignments. -/
def sharedBits (w r f d : ℕ) :
    (CpuBits w r f × SortBits d (w+1)) ≃ (Shared w r f d → Bool) where
  toFun x
    | .inl (t,j) => x.1 t j
    | .inr (.inl (l,v,s,j)) => x.2.1 l v s j
    | .inr (.inr (v,j)) => x.2.2 v j
  invFun x :=
    (fun t j => x (.inl (t,j)),
     (fun l v s j => x (.inr (.inl (l,v,s,j))), fun v j => x (.inr (.inr (v,j)))))
  left_inv x := rfl
  right_inv x := by
    funext i
    obtain ⟨t,j⟩ | (⟨l,v,s,j⟩ | ⟨v,j⟩) := i <;> rfl

/-- Finite ordinals for the shared-wire prefix of the physical bit network. -/
noncomputable def ordinalBits (w r f d : ℕ) :
    (CpuBits w r f × SortBits d (w+1)) ≃ (Fin (Fintype.card (Shared w r f d)) → Bool) :=
  (sharedBits w r f d).trans (Equiv.arrowCongr (sharedOrdinal w r f d) (Equiv.refl _))

@[simp] theorem ordinalBits_at (x : CpuBits w r f × SortBits d (w+1)) (i : Shared w r f d) :
    ordinalBits w r f d x (sharedOrdinal w r f d i) = sharedBits w r f d x i := by simp [ordinalBits]

def headerPins (h : Fin S → Computability.VPVNP.BurstRAM.Word w) : Fin (S*w) → Bool := arrayBits S w h

/-- Direct read rule, before introducing the ordinal address space. -/
def valuation (hw : 2 ≤ w+1) (v : Fin (2^d)) (header : Fin S → Computability.VPVNP.BurstRAM.Word w)
    (cpu : CpuBits w r f) (sort : SortBits d (w+1)) : Port w r d → Bool
  | .inl (c,j) => atClock false S (fun t => cpu t j) (2*v.val+c.val)
  | .inr (.inl (s,k)) => if h : 2*v.val+s.val < S then wordBits w (header ⟨_,h⟩) k else false
  | .inr (.inr (.inl (l,own,s,j))) =>
    sort.1 l (if own then v else ((RAMLayout.layerEquiv d).symm l).partner v) s j
  | .inr (.inr (.inr (true,j))) =>
    if h : v.val+1 < 2^d then sort.2 ⟨v.val,by omega⟩ j else (slotFormat hw).encode none j
  | .inr (.inr (.inr (false,j))) =>
    if h : 0 < v.val then sort.2 ⟨v.val-1,by have := v.isLt; omega⟩ j else (slotFormat hw).encode none j

theorem address_read (hw : 2 ≤ w+1) (v : Fin (2^d)) (h : Fin S → Computability.VPVNP.BurstRAM.Word w)
    (cpu : CpuBits w r f) (sort : SortBits d (w+1)) (i : Port w r d) :
    (address hw S f v i).read (ordinalBits w r f d (cpu,sort)) (headerPins h) = valuation hw v h cpu sort i := by
  rcases i with ⟨c,j⟩ | (⟨s,k⟩ | (⟨l,own,s,j⟩ | ⟨out,j⟩))
  · simp only [address, valuation, atClock]
    split <;> first | rfl | split <;> simp [shared, BitSource.read, sharedBits]
  · simp only [address, valuation]
    split <;> simp [headerPins, BitSource.read, arrayBits_at]
  · simp [address, valuation, shared, BitSource.read, sharedBits]
  · cases out with
    | false =>
      by_cases hv : 0 < v.val <;> simp [valuation,address,hv,shared,BitSource.read,sharedBits]
    | true =>
      by_cases hv : v.val+1 < 2^d <;> simp [valuation,address,hv,shared,BitSource.read,sharedBits]

end ThreeFlat.Diagonal.TracePhysical

end OAI
