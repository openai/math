import OAI.ThreeFlat.RAM.PhysicalPinRoute

namespace OAI
namespace ThreeFlat.RAM.PhysicalPinsExpr.Shape

open Diagonal Diagonal.BoundaryWire BitLayout

variable (s : Shape) [NeZero s.period]

def choice (block : Fin (s.last+1)) := AlignedChunks.active s.period block.val

def retained (block : Fin (s.last+1)) : Fin s.chunks → Bool :=
  AlignedChunks.keep (AlignedChunks.phase s.period block.val)

theorem retained_spec (block : Fin (s.last+1)) (j : Fin s.chunks) :
    s.retained block j=true ↔ j∉ Finset.univ.image (s.slots block.val) :=
  AlignedChunks.keep_spec _ _

def guardSource (right : Bool) (block : Fin (s.last+1)) (j : Fin s.halfBits) :
    Source s.chunks s.bits s.last s.inside s.advice :=
  ApproximateNetwork.guard s.choice s.retained (if right then newSource else oldSource) block j

theorem guard_addr (right : Bool) (block : Fin (s.last+1)) (j : Fin s.halfBits) :
    sourceAddress (s.guardSource right block j) =
      if j.val/s.bits/(s.inside+1)=block.val%s.period then 0
      else ApproximateAddress.endpoint s.chunks s.bits s.last s.advice right block.val
        ((s.choice block).toNat*s.halfBits+j.val) := by
  obtain ⟨⟨k,bit⟩,rfl⟩ := finProdFinEquiv.surjective j
  have idx : (finProdFinEquiv (k,bit)).val=k.val*s.bits+bit.val := by
    change bit.val+s.bits*k.val = _
    ac_rfl
  have d : (k.val*s.bits+bit.val)/s.bits=k.val := by
    rw [Nat.mul_comm k.val,Nat.mul_add_div (Nat.zero_lt_of_lt bit.isLt),
      Nat.div_eq_of_lt bit.isLt,Nat.add_zero]
  have phase : (AlignedChunks.phase s.period block.val).val = block.val%s.period := rfl
  have keepEq : s.retained block k = decide (k.val/(s.inside+1)≠block.val%s.period) :=
    AlignedChunks.keep_nat (width:=s.inside+1) (AlignedChunks.phase s.period block.val) k
  by_cases viewed : k.val/(s.inside+1)=block.val%s.period
  · simp [guardSource,ApproximateNetwork.guard,keepEq,idx,d,viewed,sourceAddress]
  · have pos : (chunkSite (s.choice block) k bit).val =
        (s.choice block).toNat*s.halfBits+(k.val*s.bits+bit.val) := by
      rw [chunkSite_val]
      cases s.choice block <;> simp [Shape.halfBits,Nat.add_assoc]
    cases right <;> simp [guardSource,ApproximateNetwork.guard,keepEq,
      idx,d,viewed,oldSource_addr,newSource_addr,ApproximateAddress.endpoint,pos]

end ThreeFlat.RAM.PhysicalPinsExpr.Shape

end OAI
