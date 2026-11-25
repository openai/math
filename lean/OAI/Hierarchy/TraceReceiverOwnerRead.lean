import OAI.Hierarchy.TraceReceiverOwnerRun
import OAI.Hierarchy.GridReceiverDirectoryFrame

namespace OAI
/-! # The three physical inputs of the receiver's owner mount -/
namespace Hierarchy.TraceReceiverOwnerMount
open ThreeFlat Diagonal.TickWorkspace
theorem sector {w u : ℕ} (positive : 0 < w) (upper : u^10 ≤ 5*w) :
    64*stride u ≤ GridDescription.sector w := by
  change 2^6*(2^(u^10))^4 ≤ 2^(32*w)
  rw [←pow_mul,←pow_add]
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- The published bound on the complete chronological directory implies every
size condition for the owner scan at an admitted receiver age. -/
theorem directory_fits {w u f n : ℕ} (pos : 0 < w) (lower : 3*w ≤ u^10)
    (count : f+n ≤ 2^(3*w/5)) :
    128 ≤ stride u ∧ 8*(f+n) ≤ stride u ∧ n ≤ GridPinArena.slab w := by
  have power : stride u=2^(u^10*4):=by unfold stride;rw [pow_mul]
  rw [power]
  refine ⟨?_,?_,?_⟩
  · change 2^7 ≤ _
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · calc
      8*(f+n) ≤ 8*2^(3*w/5) := Nat.mul_le_mul_left _ count
      _ = 2^(3+3*w/5) := (pow_add 2 3 (3*w/5)).symm
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  · exact (Nat.le_add_left n f).trans (count.trans (Nat.pow_le_pow_right (by decide)
      (show 3*w/5 ≤ 16*w by omega)))

theorem native_room {w u f n : ℕ} (pos : 0 < w) (lower : 3*w ≤ u^10) (upper : u^10 ≤ 5*w)
    (count : f+n ≤ 2^(3*w/5)) :
    Room (64*w) u f n (GridReceiverTickDirectory.banks w u).owners ((GridReceiverTickDirectory.banks w u).scratch+1) := by
  obtain ⟨width,old,roots⟩:=directory_fits pos lower count
  have scale:=sector pos upper
  have words:=GridPinArena.scales w pos
  have positive : 0 < GridPinArena.slab w:=Nat.two_pow_pos _
  refine ⟨width,old,?_,?_,?_⟩
  · change 47*stride u ≤ 15*GridDescription.sector w+3*GridPinArena.slab w;omega
  · change 15*GridDescription.sector w+3*GridPinArena.slab w+n ≤ 15*GridDescription.sector w+20*GridPinArena.slab w+1
    omega
  · change 15*GridDescription.sector w+20*GridPinArena.slab w+1+1 < 2^(64*w);omega

/-- Only the recorded parent column, the classifier's original owner bank, and
the single decoded tick word are read from the pre-mount source image. -/
def Reads (u first n owners target a : ℕ) :=
  (base u 44 ≤ a ∧ a < base u 44+8*(first+n)) ∨ (owners ≤ a ∧ a < owners+n) ∨ a=target

theorem read_bands {w u f n a : ℕ} (old : 8*(f+n) ≤ stride u) (live : n ≤ GridPinArena.slab w)
    (rd : Reads u f n (GridReceiverTickDirectory.banks w u).owners ((GridReceiverTickDirectory.banks w u).scratch+1) a) :
    (base u 44 ≤ a ∧ a < base u 45) ∨
      (15*GridDescription.sector w+3*GridPinArena.slab w ≤ a ∧ a < 15*GridDescription.sector w+4*GridPinArena.slab w) ∨
      a=15*GridDescription.sector w+20*GridPinArena.slab w+1 := by
  rcases rd with front|owner|target
  · exact .inl ⟨front.1,by have h:=front.2;change 45*stride u+8*(f+n)>a at h;change a < 46*stride u;omega⟩
  · right;left
    change 15*GridDescription.sector w+3*GridPinArena.slab w ≤ a ∧ a < 15*GridDescription.sector w+3*GridPinArena.slab w+n at owner
    exact ⟨owner.1,by omega⟩
  · exact .inr (.inr target)

end Hierarchy.TraceReceiverOwnerMount

end OAI
