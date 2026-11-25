import OAI.ThreeFlat.RAM.PackedStageArchive

namespace OAI
/-! # Running the word collector on a physically mounted bit segment -/

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure
open scoped Classical Fin.CommRing
variable {W : ℕ}

def Mount (x : PackedStageArchive.Layout) (word : ℕ→Word W) (m : Memory W) : Prop :=
  x.phase<2^W ∧ x.source m+W*x.count≤x.destination ∧ x.destination+x.count<2^W ∧
  ∀ i<x.count,∀ j<W,m (x.source m+W*i+j)=(((word (x.destination+i)).val.testBit (W-1-j)).toNat : Word W)

theorem mount_spec (x : PackedStageArchive.Layout) (word : ℕ→Word W) (m : Memory W)
    (loaded : Mount x word m) :
    (PackedStageArchive.procedure x).Spec (fun p=>p=m) (fun _ o=>o=fillSegment x.destination x.count word m)
      (x.count*(5*W+6)+10) := by
  intro n r k M pc reg pub exit inst data cfg input entry same
  subst input
  obtain ⟨phase,apart,fit,bits⟩ := loaded
  obtain ⟨out,run,done⟩ := PackedStageArchive.generate x M pc reg pub exit inst cfg m entry phase word
    (.inr apart) fit (by omega) bits
  exact ⟨_,le_rfl,out,_,run,done,rfl⟩

end ThreeFlat.Diagonal.NavigationPass

end OAI
