import OAI.Computability.BorderVNP.PackedRoutingImage
import OAI.Computability.BorderVNP.RoutingISABoot
import OAI.Computability.BorderVNP.RoutingISAExtendedFrame

/-! # Frame fields for the routing result arrays

The public initialization table supplies fields 6, 7 and 11. The extended
literal header installs 64, 65 and 87, which point directly into the geometry
result. Other stage-specific fields can be selected independently.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

/-- ABI entries for cable rows, private/live placements, and supplied wire offsets. -/
structure Header (head origin m C J : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- Cable triples start at the geometry result. -/
  cables : mem (head+6) = origin
  /-- Sparse edge capacity includes hole slots. -/
  edges : mem (head+7) = m
  /-- Native cell ordinals range up to this count. -/
  cells : mem (head+11) = C
  /-- The private pairs are overwritten in place by the private prefix stage. -/
  privatePairs : mem (head+64) = (bases origin m C J).privatePairs
  /-- Live pairs already carry their final supplied offsets. -/
  livePairs : mem (head+65) = (bases origin m C J).livePairs
  /-- The cable source/destination supplied offsets follow the triples. -/
  ends : mem (head+87) = (bases origin m C J).ends

/-- Native boot copies public argument j+1 into frame slot j. -/
def core {W : ℕ} (other : Arg → Word W) (origin m C : ℕ) (i : Arg) : Word W :=
  match i.val with
  | 7 => word W origin
  | 8 => word W m
  | 12 => word W C
  | _ => other i

/-- The three array pointers carried in the 81-word extended header. -/
def extension {W : ℕ} (other : Fin 81 → Word W) (origin m C J : ℕ) (i : Fin 81) : Word W :=
  let h := bases origin m C J
  match i.val+31 with
  | 64 => word W h.privatePairs
  | 65 => word W h.livePairs
  | 87 => word W h.ends
  | _ => other i

/-- Inputs of the other native stages can be selected independently. -/
theorem extension_other {W : ℕ} (other : Fin 81 → Word W) (origin m C J : ℕ) (i : Fin 81)
    (outside : i.val+31 ∉ [64,65,87]) : extension other origin m C J i = other i := by
  unfold extension
  split <;> simp_all

/-- Read the routing header directly from the physical boot and extended-frame installer images. -/
theorem installed_header {W : ℕ} (pub : Arg → Word W) (ext : Fin 81 → Word W) (before : Memory W)
    (origin m C J : ℕ) (room : (bases origin m C J).livePairs < 2^W) :
    let args := core pub origin m C
    let mem := ExtendedFrame.installed (bootMemory args before 31) (args 0).val (extension ext origin m C J)
    Header (args 0).val origin m C J (readings mem) := by
  intro args mem
  have coreAt (i : Fin 31) : mem ((args 0).val+i.val) = args ⟨i.val+1,by omega⟩ := by
    have outside : (args 0).val+i.val < (args 0).val+31 := by have := i.isLt; omega
    rw [show mem ((args 0).val+i.val) = bootMemory args before 31 ((args 0).val+i.val) from
      ExtendedFrame.installed_outside _ _ _ _ (Or.inl outside)]
    simp [bootMemory,i.isLt]
  have extAt (j : Fin 81) : mem ((args 0).val+31+j.val) = extension ext origin m C J j :=
    ExtendedFrame.installed_at ..
  have v1 := congrArg Fin.val (coreAt 6)
  have v2 := congrArg Fin.val (coreAt 7)
  have v3 := congrArg Fin.val (coreAt 11)
  have v4 := congrArg Fin.val (extAt 33)
  have v5 := congrArg Fin.val (extAt 34)
  have v6 := congrArg Fin.val (extAt 56)
  dsimp only [bases] at room
  constructor
  · exact v1.trans (word_val _ _ (by omega))
  · exact v2.trans (word_val _ _ (by omega))
  · exact v3.trans (word_val _ _ (by omega))
  · simpa only [readings,Nat.add_assoc,show 31+(33 : Fin 81).val = 64 by decide] using v4.trans (word_val _ _ (by dsimp [bases]; omega))
  · simpa only [readings,Nat.add_assoc,show 31+(34 : Fin 81).val = 65 by decide] using v5.trans (word_val _ _ room)
  · simpa only [readings,Nat.add_assoc,show 31+(56 : Fin 81).val = 87 by decide] using v6.trans (word_val _ _ (by dsimp [bases]; omega))

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
