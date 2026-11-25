import OAI.Hierarchy.ProbeStageCompactWindow
import OAI.Hierarchy.ProbeStageEndpointInput

namespace OAI
/-! # Both endpoint scatters read the same frozen directory and update the same actual mask bank -/
namespace Hierarchy.ProbeStage.Native.Compact
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section
set_option maxRecDepth 4096
variable {h d : ℕ} (j : Fin (rounds d)) (i : Fin (2^h))
local notation "W" => wordBits h d copies
local notation "A" => recordAdvice h d j
local notation "S" => recordScratch h d j

private theorem edit_update {w : ℕ} (e : ScatterRefinement.Edit w) (m : Memory w) :
    e.apply m=Function.update m e.dst.val (BinaryOp.bitAnd.eval (m e.dst.val) e.keep) := by
  funext x
  by_cases eqn : x=e.dst.val
  · subst x
    simp [ScatterRefinement.Edit.apply,writeMemory]
  · simp [ScatterRefinement.Edit.apply,writeMemory,eqn]

private theorem fold_model (ds : List (ScatterRefinement.Edit W)) (saved : Fin 8→Word W)
    (m n : Memory W) (s : Model j i saved m n) (targets : ∀ e∈ds,Common j i e.dst.val) :
    Model j i saved (ds.foldl ScatterRefinement.Edit.apply m) (ds.foldl ScatterRefinement.Edit.apply n) := by
  induction ds generalizing m n with
  | nil => exact s
  | cons e ds ih =>
    have target:=targets e (List.mem_cons_self)
    have next : Model j i saved (e.apply m) (e.apply n) := by
      rw [edit_update,edit_update,s.common _ target]
      exact s.update_common target _
    exact ih _ _ next (fun d hd=>targets d (List.mem_cons_of_mem _ hd))

private theorem scatter_shared (pg : MaskUpdate.Parameters W) (m n : Memory W) (saved : Fin 8→Word W)
    (s : Model j i saved m n) (ds : List (ScatterRefinement.Edit W)) (frozen : ℕ→Prop)
    (ptr : frozen (pg 1).val ∧ frozen (pg 2).val)
    (ptrCommon : Common j i (pg 1).val ∧ Common j i (pg 2).val)
    (slot : ∀ t<ds.length,frozen (pg 3+ScatterRefinement.index pg m t).val ∧
      frozen (pg 4+ScatterRefinement.index pg m t).val)
    (slotCommon : ∀ t<ds.length,Common j i (pg 3+ScatterRefinement.index pg m t).val ∧
      Common j i (pg 4+ScatterRefinement.index pg m t).val)
    (entries : ∀t (ht : t<ds.length),ScatterRefinement.read pg m t=ds[t])
    (targets : ∀ e∈ds,¬frozen e.dst.val ∧ Common j i e.dst.val) :
    Model j i saved (MaskUpdate.image pg m ds.length) (MaskUpdate.image pg n ds.length) := by
  have index (t : ℕ) : ScatterRefinement.index pg n t=ScatterRefinement.index pg m t := by
    simp only [ScatterRefinement.index,s.common _ ptrCommon.1]
  have read (t : ℕ) (ht : t<ds.length) : ScatterRefinement.read pg n t=ScatterRefinement.read pg m t := by
    simp only [ScatterRefinement.read,index,s.common _ ptrCommon.2,s.common _ (slotCommon t ht).1,
      s.common _ (slotCommon t ht).2]
  have apart := fun e he => (targets e he).1
  have left := ScatterRefinement.image_eq pg m ds frozen ptr slot entries apart
  have right := ScatterRefinement.image_eq pg n ds frozen ptr
    (fun t ht=>by rw [index];exact slot t ht) (fun t ht=>(read t ht).trans (entries t ht)) apart
  rw [left.1,right.1]
  exact fold_model j i ds saved m n s (fun e he=>(targets e he).2)

/-- The original prepared heads and lengths determine the full native instruction run on both
sides. Repeated occurrences on one mask word are processed in the original order. -/
theorem scatter_model (hd : 1≤d) (hh : 4≤h) (l : Bool) (b : Fin (groupBlocks h d j))
    (c : Fin (radix h d)) (r : ℕ) (m n : Memory W) (saved : Fin 8→Word W)
    (src : SideSource j i l b c r m)
    (setup : Model j i saved (RankUpdate.prepared (physicalSide j i l) m)
      (RankUpdate.prepared (Record.side A (row h) S l) n)) :
    Model j i saved (RankUpdate.image (physicalSide j i l) m) (RankUpdate.image (Record.side A (row h) S l) n) ∧
      RankUpdate.occurrenceCount (Record.side A (row h) S l) n=RankUpdate.occurrenceCount (physicalSide j i l) m := by
  let orig:=physicalSide j i l
  let stg:=Record.side A (row h) S l
  let old:=RankUpdate.prepared orig m
  let new:=RankUpdate.prepared stg n
  change Model j i saved old new at setup
  let pg:=RankUpdate.page W orig
  let place:=packedPlace h d j.val l b
  let ps:=RankUpdate.edits (formatAdvice h d).row c r orig.quota
  let ds:=ps.map (ScatterRefinement.event (fieldWidth h) place)
  let frozen:=frozenMask j l b
  have input:=endpoint_input hd j i l b c r m src
  have dir:=input.literal
  have cnt : RankUpdate.occurrenceCount orig m=ds.length := by
    simpa only [ds,List.length_map,ps] using RankUpdate.edits_length orig m input.distinct r input.previous
      input.quotaFit input.rankFit (formatAdvice h d).row c input.length
  have count : RankUpdate.occurrenceCount stg n=RankUpdate.occurrenceCount orig m := by
    change (new (scratch h d j 11:Word W).val).val=(old (scratch h d j 11:Word W).val).val
    rw [Fin.val_cast_of_lt (scratch_fits j 11)]
    exact congrArg Fin.val (setup.common _ (common_temp j i hh 11))
  refine ⟨?_,count⟩
  change Model j i saved (MaskUpdate.image pg old (RankUpdate.occurrenceCount orig m))
    (MaskUpdate.image pg new (RankUpdate.occurrenceCount stg n))
  rw [count,cnt]
  have headAddr : (pg 1).val=scratch h d j 10 := Fin.val_cast_of_lt (scratch_fits j 10)
  have baseAddr : (pg 2).val=scratch h d j (maskTemp l) := by cases l <;> apply Fin.val_cast_of_lt <;> apply scratch_fits j
  have head : old (pg 1).val=((c.val*directoryCapacity (radix h d) (stringLength h):ℕ):Word W) := by
    rw [headAddr]
    change RankUpdate.prepared orig m orig.head=_
    rw [RankUpdate.prepared_head orig m input.distinct]
    change m ((region h d j 8:Word W)+m ((physicalSide j i l).chosen:Word W).val).val=_
    rw [src.selected,add_word (region_word j.isLt 8 (c.isLt.trans_le (region_room hd j.isLt.le).2.1))]
    exact (occurrence_header hd j m src.rom c).1
  apply scatter_shared j i pg old new saved setup ds frozen dir.pointers
    (by rw [headAddr,baseAddr];exact ⟨common_temp j i hh 10,common_temp j i hh _⟩)
    (by simpa only [ds,List.length_map] using dir.slots)
  · intro t ht
    have live : t<(PackedMask.occurrences (formatAdvice h d).row c).length := by
      by_cases sat : r+1=orig.quota
      · simpa [ds,ps,RankUpdate.edits,sat] using ht
      · simp [ds,ps,RankUpdate.edits,sat] at ht
    have off:=occurrence_offset hd c t live
    have index : ScatterRefinement.index pg old t=((c.val*directoryCapacity (radix h d) (stringLength h)+t:ℕ):Word W) := by
      simp only [ScatterRefinement.index,head,Nat.cast_add]
    have offsets : pg 3=(region h d j 10:Word W) := rfl
    have clear : pg 4=(region h d j 11:Word W) := rfl
    rw [offsets,clear,index,add_word (region_word j.isLt 10 off),add_word (region_word j.isLt 11 off)]
    exact ⟨common_area j i hh 10 ⟨_,off⟩,common_area j i hh 11 ⟨_,off⟩⟩
  · intro t ht
    simpa [ds,ps] using dir.entry t (by simpa [ds,ps] using ht)
  · intro e he
    obtain ⟨u,hu,rfl⟩:=List.mem_map.mp he
    refine ⟨dir.disjoint u hu,?_⟩
    let chunk : Fin (fieldChunks h):=⟨u.2.val/fieldWidth h,wordChunk (h:=h) u.2⟩
    change Common j i (packedPlace h d j l b u.1 chunk.val).val
    rw [packedPlace_at hd j l b u.1 chunk]
    simpa only [maskLocation,Nat.add_assoc] using common_area j i hh (maskArea l)
      ⟨_,mask_offset hd j.isLt.le b u.1 chunk⟩

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
