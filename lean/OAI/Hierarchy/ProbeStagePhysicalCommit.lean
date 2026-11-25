import OAI.Hierarchy.ProbeStageEndpointInput

namespace OAI
/-! # Physical postconditions of a single endpoint in its named banks -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => ramWidth h d

structure Commit (l : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) (prior : ℕ)
    (m : Memory W) : Prop where
  rank : (RankUpdate.image (physicalSide j i l) m (rankAddr h d j.val (roleRank l) i)).val=prior
  counter : (RankUpdate.image (physicalSide j i l) m (counterLocation h d j.val l b c)).val=prior+1
  clears : RankUpdate.occurrenceCount (physicalSide j i l) m=
    (RankUpdate.edits (formatAdvice h d).row c prior (quota (radix h d))).length
  frame : ∀ x, x∉(coreTargets hd j i l b c).map (Cell.addr j.val) → frozenMask j l b x →
    RankUpdate.image (physicalSide j i l) m x=m x
  masks : ∀ r k (S : Finset (Fin (radix h d))),
    (m (maskLocation h d j.val l b r k)).val=PackedMask.word ((formatAdvice h d).row r) S (fieldWidth h) k.val →
    (RankUpdate.image (physicalSide j i l) m (maskLocation h d j.val l b r k)).val=
      PackedMask.word ((formatAdvice h d).row r) (if prior+1=quota (radix h d) then insert c S else S) (fieldWidth h) k.val

include hd in
theorem endpoint_commit (l : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d)) (r : ℕ) (m : Memory W)
    (src : SideSource j i l b c r m) : Commit hd j i l b c r m := by
  let s := physicalSide j i l
  have si := endpoint_input hd j i l b c r m src
  obtain ⟨rank,counter,count,frame⟩ := RankUpdate.committed s m si.distinct r si.previous si.quotaFit si.rankFit
    (formatAdvice h d).row c si.length (fieldWidth h) (packedPlace h d j.val l b) (frozenMask j l b)
    si.literal si.rankAddr si.counterAddr
  have address : (RankUpdate.counter s m).val=counterLocation h d j.val l b c := by
    simpa [countTag,Cell.addr,counterLocation,Nat.add_assoc] using countAddress hd j i l m b c src.countPtr src.selected
  have rankAddrEq : s.rank=rankAddr h d j.val (roleRank l) i := by cases l <;> rfl
  rw [rankAddrEq] at rank
  rw [address] at counter
  refine ⟨rank,counter,count,?_,?_⟩
  · intro x apart frozen
    apply frame x frozen
    change x∉RankUpdate.touched (physicalSide j i l) m
    rw [physical_touched hd j i l m b c src.countPtr src.selected]
    exact apart
  · intro row k S hword
    let x := maskTag hd j l b row k
    have other : x∉coreTargets hd j i l b c := by cases l <;> simp [x,maskTag,coreTargets,countTag,maskArea,countArea]
    have original := setup_other hd j i _ _ _ _ _ src x other
    change RankUpdate.prepared s m (Cell.addr j.val x)=m (Cell.addr j.val x) at original
    rw [show x=maskTag hd j l b row k from rfl,maskTag_addr hd] at original
    have width : fieldWidth h ≤ W := by
      have size := least_size h d
      have room := regionSize_fits (h:=h) (d:=d) j
      exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (le_trans size room.le)
    have equation := RankUpdate.mask_after s m r (formatAdvice h d).row c S (fieldWidth h)
      (by simp [fieldWidth]) width (packedPlace h d j.val l b) _ si.literal count row k.val
      (by rw [packedPlace_at hd j l b row k,original,hword]) (fun p _ => by
        have bound := wordChunk p.2
        simpa [Fin.ext_iff] using packedPlace_eq hd j l b p.1 row ⟨_,bound⟩ k)
    have q : s.quota=quota (radix h d) := rfl
    simpa only [q,packedPlace_at hd j l b row k] using equation

theorem commit_typed_frame {l : Bool} {b : Fin (groupBlocks h d j.val)} {c : Fin (radix h d)}
    {r : ℕ} {m : Memory W} (out : Commit hd j i l b c r m) (x : Cell h d)
    (untouched : x∉coreTargets hd j i l b c) (different : ∀ row k, x≠maskTag hd j l b row k) :
    RankUpdate.image (physicalSide j i l) m (Cell.addr j.val x)=m (Cell.addr j.val x) := by
  apply out.frame
  · intro hm
    obtain ⟨z,hz,eqn⟩ := List.mem_map.mp hm
    exact untouched ((cell_injective h d j.val eqn) ▸ hz)
  · intro row k he
    exact different row k (cell_injective h d j.val (he.trans (maskTag_addr hd j l b row k).symm))

end
end Hierarchy.ProbeStage.Native

end OAI
