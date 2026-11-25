import OAI.Hierarchy.ProbeStagePhysicalEndpoint

namespace OAI
/-! # Frozen input words and the concrete destination of a candidate-list update -/

namespace Hierarchy.ProbeStage.Native
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open scoped Fin.CommRing
noncomputable section

variable {h d : ℕ} (hd : 1≤d) (j : Fin (rounds d))

def maskTag (l : Bool) (b : Fin (groupBlocks h d j.val)) (r : MaskIndex (radix h d)) (k : Fin (fieldChunks h)) : Cell h d :=
  .area (maskArea l) ⟨b.val*((radix h d)^4*fieldChunks h)+rowCode r*fieldChunks h+k.val,
    mask_offset hd j.isLt.le b r k⟩

theorem maskTag_addr (l : Bool) (b : Fin (groupBlocks h d j.val)) (r : MaskIndex (radix h d)) (k : Fin (fieldChunks h)) :
    Cell.addr j.val (maskTag hd j l b r k)=maskLocation h d j.val l b r k := by simp [maskTag,Cell.addr,maskLocation,add_assoc]

def frozenMask (l : Bool) (b : Fin (groupBlocks h d j.val)) (x : ℕ) : Prop :=
  ∀ r k, x≠maskLocation h d j.val l b r k

include hd in
theorem temp_frozen (l : Bool) (b : Fin (groupBlocks h d j.val)) (p : Fin 12) :
    frozenMask j l b (scratch h d j.val p) := by
  intro r k equal
  rw [← maskTag_addr hd] at equal
  have e : Cell.temp p = maskTag hd j l b r k := cell_injective h d j.val equal
  cases e

include hd in
theorem area_frozen (l : Bool) (b : Fin (groupBlocks h d j.val)) (p : Fin 16) (q : ℕ)
    (hq : q<regionSize h d) (ne : p ≠ maskArea l) : frozenMask j l b (region h d j.val p+q) := by
  intro r k equal
  rw [←maskTag_addr hd] at equal
  exact region_address_ne hq (mask_offset hd j.isLt.le b r k) ne equal

include hd in
theorem rank_frozen (l : Bool) (b : Fin (groupBlocks h d j.val)) (p : Fin 3) (i : Fin (2^h)) :
    frozenMask j l b (rankAddr h d j.val p i) := by
  intro r k equal
  rw [←maskTag_addr hd] at equal
  have e : Cell.rank p i=maskTag hd j l b r k := cell_injective h d j.val equal
  cases e

include hd in
theorem finite_directory (i : Fin (2^h)) (l : Bool) (b : Fin (groupBlocks h d j.val)) (c : Fin (radix h d))
    (rank : ℕ) (m : Memory (ramWidth h d))
    (rom : immutable h d _ j (RankUpdate.prepared (physicalSide j i l) m))
    (head : RankUpdate.prepared (physicalSide j i l) m (scratch h d j.val 10)=
      ((c.val*directoryCapacity (radix h d) (stringLength h):ℕ):Word (ramWidth h d)))
    (base : RankUpdate.prepared (physicalSide j i l) m (scratch h d j.val (maskTemp l))=
      (blockMaskBase h d j.val l b:Word (ramWidth h d))) :
    RankUpdate.Directory (physicalSide j i l) m
      (RankUpdate.edits (formatAdvice h d).row c rank (physicalSide j i l).quota) (fieldWidth h)
      (packedPlace h d j.val l b) (frozenMask j l b) := by
  let s := physicalSide j i l
  let mem := RankUpdate.prepared s m
  let v := RankUpdate.page (ramWidth h d) s
  have headAddr : (v 1).val = scratch h d j.val 10 :=
    Fin.val_cast_of_lt (Nat.lt_of_succ_lt (temp_room (h:=h) hd j 10))
  have baseAddr : (v 2).val = scratch h d j.val (maskTemp l) := by
    cases l <;> apply Fin.val_cast_of_lt <;> first | exact (Nat.lt_of_succ_lt (temp_room (h:=h) hd j 2)) | exact (Nat.lt_of_succ_lt (temp_room (h:=h) hd j 3))
  have hhead : mem (v 1).val=((c.val*directoryCapacity (radix h d) (stringLength h):ℕ):Word (ramWidth h d)) := by rw [headAddr];exact head
  have hbase : mem (v 2).val=(blockMaskBase h d j.val l b:Word (ramWidth h d)) := by rw [baseAddr];exact base
  have offsets : v 3=(region h d j.val 10:Word (ramWidth h d)) := rfl
  have clearing : v 4=(region h d j.val 11:Word (ramWidth h d)) := rfl
  have pointers : frozenMask j l b (v 1).val ∧ frozenMask j l b (v 2).val :=
    by rw [headAddr,baseAddr];exact ⟨temp_frozen hd j l b 10,temp_frozen hd j l b _⟩
  by_cases sat : rank+1=(physicalSide j i l).quota
  · rw [RankUpdate.edits,ite_eq_left sat]
    refine ⟨pointers,?_,?_,?_⟩
    · intro t ht
      have off := occurrence_offset hd c t ht
      have get : ScatterRefinement.index v mem t=((c.val*directoryCapacity (radix h d) (stringLength h)+t:ℕ):Word (ramWidth h d)) := by
        simp only [ScatterRefinement.index,hhead,Nat.cast_add]
      change frozenMask j l b (v 3+ScatterRefinement.index v mem t).val ∧ frozenMask j l b (v 4+ScatterRefinement.index v mem t).val
      rw [offsets,clearing,get,add_word (region_word j.isLt 10 off),add_word (region_word j.isLt 11 off)]
      constructor <;> apply area_frozen hd j _ _ _ _ off <;> cases l <;> decide
    · intro t ht
      exact read_edit hd j l b mem rom v c hhead hbase offsets clearing t ht
    · intro p hp frozen
      have fit := wordChunk (h:=h) p.2
      exact frozen p.1 ⟨_,fit⟩ (packedPlace_at hd j l b p.1 ⟨_,fit⟩)
  · rw [RankUpdate.edits,ite_eq_right sat]
    exact ⟨pointers,fun t ht => (Nat.not_lt_zero t ht).elim,fun t ht => (Nat.not_lt_zero t ht).elim,by simp⟩

end
end Hierarchy.ProbeStage.Native

end OAI
