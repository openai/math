import OAI.Computability.VPVNP.LiveAuxiliaryStages
import OAI.Computability.VPVNP.LiveAuxiliaryHeaderSweep
import OAI.Computability.VPVNP.LiveHeaderProtectedCore

/-!
# Executing the indirect cursor guard on the complete sparse header copy

Each live call rereads the last descriptor's packed end. The source sweep
writes only its current sparse destination, so all descriptors retain their
values across the active calls. At the packed end one additional call reads
the limit and accepts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveAuxiliaryStages

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM LiveAuxiliaryHeaders LiveHeaderCopyDispatch
open scoped Fin.CommRing

variable {w : ℕ} {desc : Word w} {base : ℕ} {L : Lengths}
variable {hdr : Header L → Bool} {hist : List (Word w)} {src : Fin 7 → Word w}

private abbrev guarded (desc : Word w) := (copy.instantiate w (copyData desc)).program

private theorem loaded_limit {m : Memory w} (h : Prepared desc base L hdr hist src m) :
    LiveCountedStage.limit true (address desc 6 0) m = (populated L hist.length : Word w) :=
  h.descriptors.ends 6

/-- Add the four indirect-guard instructions to each call of a successful
source prefix. The two runs have identical memory at every return. -/
private theorem lift_prefix (fit : base+span L hist.length ≤ 2^w) (width : populated L hist.length < 2^w)
    (sep : Separated desc base L hist.length src fit) (fuel : ℕ) (room : 68 ≤ fuel)
    (tag : Word w) (outside : tag.val < base ∨ base+span L hist.length ≤ tag.val)
    (len start : ℕ) (bound : start+len ≤ populated L hist.length) {m : Memory w}
    (ready : Prepared desc base L hdr hist src m) {rs : List (Report w)}
    (run : runSegment (program desc) 64 (some (start : Word w)) m (List.replicate len []) = some rs) :
    ∃ gs, runSegment (guarded desc) fuel (some (start : Word w)) m (List.replicate len []) = some gs ∧
      endState (some (start : Word w)) gs = some ((start+len : ℕ) : Word w) ∧
      after m (eventLog gs) = after m (eventLog rs) ∧ Prepared desc base L hdr hist src (after m (eventLog gs)) ∧
      gs.length = len ∧ (∀ r ∈ gs, r.events.length < 68 ∧ r.probes ≤ 12 ∧ choiceBits r.events = []) ∧
      LiveStageLink.PreservesTagOnReturns tag m gs := by
  induction len generalizing start m rs with
  | zero =>
    simp only [List.replicate_zero, runSegment, Option.some.injEq] at run
    subst rs
    exact ⟨[],rfl,rfl,rfl,ready,rfl,by simp,trivial⟩
  | succ len ih =>
    let i : Fin (populated L hist.length) := ⟨start, by omega⟩
    obtain ⟨es, hr, hm, hl, hp, hb⟩ := native_cell fit width ready i
    let raw : Report w := ⟨es,some ((start : Word w)+1)⟩
    let gsHead := LiveCountedStage.prefixReport true (address desc 6 0) m raw
    have guard : (start : Word w) < LiveCountedStage.limit true (address desc 6 0) m := by
      rw [loaded_limit ready]
      change (start : Word w).val < (populated L hist.length : Word w).val
      rw [Fin.val_cast_of_lt (i.isLt.trans width), Fin.val_cast_of_lt width]
      exact i.isLt
    have hg : execute (guarded desc) 68 ((guarded desc).start (start : Word w)) m [] = some gsHead := by
      rw [show execute (guarded desc) 68 ((guarded desc).start (start : Word w)) m [] = _ from
        LiveCountedStage.execute_active (flow.template (some 11)) true (fun _ => desc)
          (address desc 6 0) 64 (start : Word w) m guard []]
      change (execute (program desc) 64 ((program desc).start (start : Word w)) m []).map _ = _
      rw [hr]; rfl
    have hgfuel := execute_extend hg (fuel-68)
    rw [Nat.add_sub_cancel' room] at hgfuel
    have prepared : Prepared desc base L hdr hist src (after m es) := hm ▸ ready.write sep i _
    have head_mem : after m gsHead.events = after m es := rfl
    have head_st : gsHead.result = some ((start+1 : ℕ) : Word w) := by simp [gsHead,raw]
    have preserve : after m gsHead.events tag.val = m tag.val := by
      rw [head_mem, hm]
      apply ite_eq_right
      change tag.val ≠ base+(sparseOffset L hist.length i).val
      have hi := (sparseOffset L hist.length i).isLt
      omega
    rw [List.replicate_succ,runSegment,hr] at run
    obtain ⟨rest, hrest, rfl⟩ := Option.map_eq_some_iff.mp run
    change runSegment (program desc) 64 (some ((start : Word w)+1)) (after m es) _ = _ at hrest
    rw [← Nat.cast_one (R := Word w), ← Nat.cast_add] at hrest
    obtain ⟨gs, hs, he, same, prepared', length, costs, frame⟩ :=
      ih (start+1) (by omega) prepared hrest
    refine ⟨gsHead::gs, ?_, ?_, ?_, ?_, by simp [length], ?_, ?_⟩
    · simp only [List.replicate_succ, runSegment, hgfuel, head_st, head_mem, hs, Option.map_some]
    · change endState gsHead.result gs = _
      rw [head_st, he]
      congr 2
      omega
    · change after m (gsHead.events ++ eventLog gs) = after m (es ++ eventLog rest)
      simp only [after,List.foldl_append]
      change after (after m gsHead.events) (eventLog gs) = after (after m es) (eventLog rest)
      rw [head_mem]
      exact same
    · change Prepared _ _ _ _ _ _ (after m (gsHead.events ++ eventLog gs))
      simp only [after,List.foldl_append]
      change Prepared _ _ _ _ _ _ (after (after m gsHead.events) (eventLog gs))
      rw [head_mem]
      exact prepared'
    · intro r h
      rcases List.mem_cons.mp h with rfl | h
      · refine ⟨?_,?_,hb⟩
        · change (LiveCountedStage.guardEvents true (address desc 6 0) m ++ es).length < 68
          rw [List.length_append,LiveCountedStage.guardEvents_length]; omega
        · change 1+countProbes es ≤ 12
          omega
      · exact costs r h
    · exact ⟨fun _ => preserve, head_mem ▸ frame⟩

/-- The actual auxiliary copy component performs one guarded call for every
populated word and one closing call. Its final memory is precisely the sparse
installation used by the virtual auxiliary machine. -/
theorem guarded_copy_native (fit : base+span L hist.length ≤ 2^w) (width : populated L hist.length < 2^w)
    (sep : Separated desc base L hist.length src fit) (fuel : ℕ) (room : 68 ≤ fuel)
    (tag : Word w) (outside : tag.val < base ∨ base+span L hist.length ≤ tag.val)
    {m : Memory w} (ready : Prepared desc base L hdr hist src m) :
    let n := populated L hist.length
    let P := (copy.instantiate w (copyData desc)).program
    ∃ (active : List (Report w)) (closed : Report w),
      runSegment P fuel (some 0) m (List.replicate (n+1) []) = some (active++[closed]) ∧
      endState (some 0) (active++[closed]) = none ∧
      after m (eventLog (active++[closed])) = install base L hdr hist fit m ∧
      active.length = n ∧ (∀ r ∈ active, r.events.length < 68 ∧ r.probes ≤ 12 ∧ choiceBits r.events = []) ∧
      closed.events.length = 4 ∧ closed.probes = 1 ∧ choiceBits closed.events = [] ∧
      LiveStageLink.PreservesTagOnReturns tag m (active++[closed]) := by
  dsimp only
  let n := populated L hist.length
  obtain ⟨rs, run, _, mem, _, _⟩ := sweep_native fit width sep ready
  obtain ⟨active, hg, he, same, prep, len, costs, frame⟩ := lift_prefix fit width sep fuel room tag outside n 0
    (by simp [n]) ready (by simpa only [Nat.cast_zero] using run)
  simp only [Nat.cast_zero, Nat.zero_add] at hg he
  let current := after m (eventLog active)
  let closed : Report w := ⟨LiveCountedStage.guardEvents true (address desc 6 0) current, none⟩
  have hc : execute (guarded desc) fuel ((guarded desc).start (n : Word w)) current [] = some closed := by
    rw [show fuel = (fuel-5)+5 by omega]
    exact copy_closed desc (records L hist.length base src) current prep.descriptors (fuel-5) (n : Word w) le_rfl []
  refine ⟨active,closed,?_,?_,?_,len,costs,rfl,rfl,rfl,
    frame.append (LiveStageLink.PreservesTagOnReturns.singleton_accept _ _ closed rfl)⟩
  · change runSegment (guarded desc) fuel (some 0) m (List.replicate (n+1) []) = _
    rw [List.replicate_succ',PrimedSchedule.runSegment_append,hg]
    simp only [Option.bind_some,he,runSegment,show execute (guarded desc) fuel
      ((guarded desc).start (n : Word w)) (after m (eventLog active)) [] = _ from hc,Option.map_some]
  · rw [endState_append]; rfl
  · simp only [eventLog,List.flatMap_append,List.flatMap_singleton,after,List.foldl_append]
    exact same.trans mem

end LiveAuxiliaryStages

end VPVNP
end Computability
end OAI
