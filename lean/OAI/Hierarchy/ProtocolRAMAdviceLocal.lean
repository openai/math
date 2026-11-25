import OAI.Hierarchy.ProtocolRAMStaticSlabs
import OAI.ThreeFlat.RAM.WordSegment

namespace OAI
/-! # Initial advice installers that access the incoming tape only at the output address -/
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM ThreeFlat.RAM

def AdviceLocal {A : Type*} (U : (ℕ→A)→(ℕ→A)) : Prop :=
  ∀m n x,m x=n x→U m x=U n x

namespace AdviceLocal
variable {A I : Type*} {w : ℕ}

theorem id : AdviceLocal (fun m : ℕ→A=>m) := fun _ _ _ h=>h

theorem comp {U V : (ℕ→A)→(ℕ→A)} (u : AdviceLocal U) (v : AdviceLocal V) :
    AdviceLocal (fun m=>U (V m)) := fun m n x h=>u _ _ _ (v m n x h)

theorem fill (p len : ℕ) (f : ℕ→Word w) : AdviceLocal (fillSegment p len f) := by
  intro m n x h
  simp only [fillSegment,h]

theorem run {q : ℕ} (lo hi : Fin q→ℕ) (data : Fin q→(ℕ→A)→ℕ→A)
    (localData : ∀i,AdviceLocal (data i)) :
    AdviceLocal (fun m=>ProtocolRAMStaticSlabs.mounted lo hi (fun i=>data i m) m) := by
  intro m n x h
  cases how : ProtocolRAMStaticSlabs.owner lo hi x with
  | none => simpa only [ProtocolRAMStaticSlabs.mounted,how] using h
  | some i => simpa only [ProtocolRAMStaticSlabs.mounted,how] using localData i m n x h

theorem foldr (xs : List I) (load : I→(ℕ→A)→(ℕ→A)) (ok : ∀i,AdviceLocal (load i)) :
    AdviceLocal (fun m=>xs.foldr load m) := by
  induction xs with
  | nil => exact id
  | cons a xs ih=>exact (ok a).comp ih

theorem foldl (xs : List I) (load : (ℕ→A)→I→(ℕ→A)) (ok : ∀i,AdviceLocal (fun m=>load m i)) :
    AdviceLocal (fun m=>xs.foldl load m) := by
  induction xs with
  | nil => exact id
  | cons a xs ih=>exact ih.comp (ok a)

end AdviceLocal
end Hierarchy.ProtocolRAM

end OAI
