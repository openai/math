import OAI.Computability.VPVNP.CompressorRecordPreimageScan

/-!
# The persistent cursor and memory frame of the preimage pass

Every successful call checks the owner and the current row length before its two
writes. Thus a scan in one descriptor level preserves other levels' tables, even
when the initial contents of the latter are arbitrary. The persistent cursor
advances once per call, including in a partial scan.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

private theorem collectPreimage_reject (pub : Fin 6 → Word w) (mem : Memory w) (i : Word w)
    (bad : ¬ (i < pub 0 ∧ ownerAt pub mem i < pub 2 ∧ mem (countAt pub (ownerAt pub mem i)).val < pub 4)) :
    let M := (template collectPreimage 3).instantiate w pub
    execute M.program 23 (M.program.start i) mem [] = none := by
  change execute ((template collectPreimage 3).instantiate w pub).program (1 + collectPreimage.length)
    ⟨_, i, fun _ => 0, fun _ => 0⟩ mem [] = _
  rw [execute_template, run_eq_trace, collectPreimage_invalid pub i _ mem bad]
  rfl

/-- The two writable intervals of the preimage pass are the count column and the
rectangular row data. Space between these intervals is also preserved. -/
def OutsidePreimageWrites (pub : Fin 6 → Word w) (addr : ℕ) : Prop :=
  (addr < (pub 3).val ∨ (pub 3).val + (pub 2).val ≤ addr) ∧
  (addr < (pub 5).val ∨ (pub 5).val + (pub 2).val * (pub 4).val ≤ addr)

private theorem collectUpdate_frame {pub : Fin 6 → Word w} (regions : RowRegions pub)
    (mem : Memory w) (i : Word w) (ho : ownerAt pub mem i < pub 2)
    (hcap : mem (countAt pub (ownerAt pub mem i)).val < pub 4) (addr : ℕ)
    (outside : OutsidePreimageWrites pub addr) : collectUpdate pub mem i addr = mem addr := by
  let owner := ownerAt pub mem i
  let length := mem (countAt pub owner).val
  change owner.val < (pub 2).val at ho
  change length.val < (pub 4).val at hcap
  have hc := regions.countsBeforeRows
  have hf := regions.rowsFit
  have hb := (pub 5).isLt
  have hcval : (countAt pub owner).val = (pub 3).val + owner.val := by
    rw [countAt, Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  have hmul := Nat.mul_le_mul_right (pub 4).val (Nat.succ_le_of_lt ho)
  rw [Nat.succ_mul] at hmul
  have hrval : (rowAt pub owner + length).val = (pub 5).val + owner.val * (pub 4).val + length.val := by
    rw [Fin.val_add, rowAt, Fin.val_add, Fin.val_mul, Nat.add_mod_mod,
      Nat.mod_eq_of_lt (show (pub 5).val + owner.val * (pub 4).val < 2^w by omega),
      Nat.mod_eq_of_lt (by omega)]
  obtain ⟨hcount, hrow⟩ := outside
  have ha : addr ≠ (countAt pub owner).val := by rw [hcval]; omega
  have hd : addr ≠ (rowAt pub owner + length).val := by rw [hrval]; omega
  change writeMemory (writeMemory mem (rowAt pub owner + length) i) (countAt pub owner) (length+1) addr = _
  simp only [writeMemory, ite_eq_right ha, ite_eq_right hd]

/-- Any successful native scan retains its exact end cursor and preserves each
address outside the two writable intervals. This applies directly to the reports
produced by `collectPreimages_run`. -/
theorem collectPreimages_cursor_frame {pub : Fin 6 → Word w} (regions : RowRegions pub)
    {mem : Memory w} {k steps : ℕ} {rs : List (Report w)}
    (hrun : runSegment ((template collectPreimage 3).instantiate w pub).program 23
      (some (Fin.ofNat (2^w) k)) mem (List.replicate steps []) = some rs) :
    endState (some (Fin.ofNat (2^w) k)) rs = some (Fin.ofNat (2^w) (k+steps)) ∧
      ∀ addr, OutsidePreimageWrites pub addr → after mem (eventLog rs) addr = mem addr := by
  induction steps generalizing k mem rs with
  | zero =>
    change some [] = some rs at hrun
    cases hrun
    exact ⟨rfl, fun _ _ => rfl⟩
  | succ steps ih =>
    let i := Fin.ofNat (2^w) k
    let owner := ownerAt pub mem i
    let valid := i < pub 0 ∧ owner < pub 2 ∧ mem (countAt pub owner).val < pub 4
    rw [List.replicate_succ, runSegment] at hrun
    by_cases h : valid
    · obtain ⟨hi, ho, hcap⟩ := h
      rw [collectPreimage_native pub mem i hi ho hcap] at hrun
      have hnext : i + 1 = Fin.ofNat (2^w) (k+1) := by
        apply Fin.ext
        simp [i, Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]
      simp only [after_collectEvents, hnext, Option.map_eq_some_iff] at hrun
      obtain ⟨tail, htail, rfl⟩ := hrun
      obtain ⟨hs, hf⟩ := ih htail
      refine ⟨?_, ?_⟩
      · change endState (some (Fin.ofNat (2^w) (k+1))) tail = _
        rw [hs, show k+1+steps = k+(steps+1) by omega]
      · intro addr ha
        change ((collectEvents pub mem i ++ eventLog tail).foldl update mem) addr = _
        rw [List.foldl_append]
        exact (hf addr ha).trans (collectUpdate_frame regions mem i ho hcap addr ha)
    · rw [collectPreimage_reject pub mem i h] at hrun
      cases hrun

/-- In particular every cell in a previous or subsequent level's disjoint interval
keeps its value through this pass. -/
theorem collectPreimages_frame {pub : Fin 6 → Word w} (regions : RowRegions pub)
    {mem : Memory w} {k steps : ℕ} {rs : List (Report w)}
    (hrun : runSegment ((template collectPreimage 3).instantiate w pub).program 23
      (some (Fin.ofNat (2^w) k)) mem (List.replicate steps []) = some rs) :
    endState (some (Fin.ofNat (2^w) k)) rs = some (Fin.ofNat (2^w) (k+steps)) ∧
      ∀ addr, addr < (pub 3).val ∨ (pub 5).val + (pub 2).val * (pub 4).val ≤ addr →
        after mem (eventLog rs) addr = mem addr := by
  obtain ⟨hs, hf⟩ := collectPreimages_cursor_frame regions hrun
  refine ⟨hs, fun addr h => hf addr ?_⟩
  have hc := regions.countsBeforeRows
  unfold OutsidePreimageWrites
  omega

end CompressorRecords

end VPVNP
end Computability
end OAI
