import OAI.Hierarchy.ProbeStageFastField
import OAI.Hierarchy.ProbeStageMaskChoice

namespace OAI
/-! # The physical chunk search returns the greedy candidate-bit index -/

namespace Hierarchy.ProbeStage.FastField
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing

/-- The two mutable bit banks and the literal least-position table for this query. -/
structure Represents {B ℓ w : ℕ} (s : Layout) (m : Memory w) (row : Fin ℓ → Fin B)
    (leftFull rightFull : Finset (Fin B)) : Prop where
  left : ∀ k<s.chunks, (m (m (s.leftMask:Word w).val + m (s.wordOffset:Word w).val + (k:Word w)).val).val =
    PackedMask.word row leftFull s.width k
  right : ∀ k<s.chunks, (m (m (s.rightMask:Word w).val + m (s.wordOffset:Word w).val + (k:Word w)).val).val =
    PackedMask.word row rightFull s.width k
  table : ∀ k<s.chunks, m ((s.leastTable:Word w)+availableWord s m k).val =
    (MaskWords.least (availableWord s m k).val : Word w)

theorem machine_choice {B ℓ w : ℕ} (s : Layout) (m : Memory w) (row : Fin ℓ → Fin B)
    (L R good : Finset (Fin B)) (rep : Represents s m row L R) (len : s.length=ℓ)
    (pos : 0<s.width) (room : ℓ ≤ s.chunks*s.width) (avail : ∀ c,c∈good ↔ c∉L∪R) :
    WordStore.value s.output (code s) m=(PackedMask.firstIndex row good:Word w) := by
  let get := PackedMask.word row (L∪R) s.width
  have value (k : ℕ) (hk : k<s.chunks) : (availableWord s m k).val=get k := by
    simp only [availableWord,BinaryOp.eval,Fin.val_ofNat]
    rw [Nat.mod_eq_of_lt (Nat.and_le_left.trans_lt (m _).isLt),rep.left k hk,rep.right k hk,PackedMask.and_word]
  have eval (ks : List ℕ) (bound : ∀ k∈ks,k<s.chunks) : lookup s m ks=(PackedMask.findWord s.width ℓ get ks:Word w) := by
    induction ks with
    | nil => simp [lookup,PackedMask.findWord,len]
    | cons k ks ih =>
      have hk := bound k (by simp)
      have eqn := value k hk
      have next := ih (fun t ht => bound t (by simp [ht]))
      by_cases hz : availableWord s m k=0
      · have zero : get k=0 := by rw [←eqn,hz];rfl
        simp [lookup,PackedMask.findWord,hz,zero,next]
      · have nonzero : get k≠0 := fun h => hz (Fin.ext (eqn.trans h))
        simp only [lookup,hz,ite_false,PackedMask.findWord,nonzero,rep.table k hk,eqn,Nat.cast_add]
  rw [code,first_eval,eval (List.range s.chunks) (fun _ h=>List.mem_range.mp h),
    PackedMask.find_prescribed row (L∪R) good avail s.width s.chunks pos room]

end Hierarchy.ProbeStage.FastField

end OAI
