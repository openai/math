import OAI.Computability.VPVNP.CompressorBundleFixedGather

/-!
# A complete fixed-program scan of the two bundle key tables

A cursor visits the live positions of the uniform-stride rectangle. At each
position the program reads the stored arc ID, follows it to the original key,
and writes the key at the same physical slot in the output. The slot embedding
determines every live address and lets the frame include all padding.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleGather.Fixed

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w N S A : ℕ}

/-- Fit and pairwise separation from the output rectangle. -/
structure ScanLayout (p : Fin 7 → Word w) (S A : ℕ) : Prop where
  idsFit : (p 4).val + S ≤ 2 ^ w
  keysFit : (p 5).val + A ≤ 2 ^ w
  outputFits : (p 6).val + S ≤ 2 ^ w
  idsApart : (p 4).val + S ≤ (p 6).val ∨ (p 6).val + S ≤ (p 4).val
  keysApart : (p 5).val + A ≤ (p 6).val ∨ (p 6).val + S ≤ (p 5).val

/-- Readback and memory frame after the first `k` calls. -/
structure Filled (p : Fin 7 → Word w) (initial m : Memory w) (slot : Fin N ↪ Fin S) (k : ℕ) : Prop where
  readback : ∀ j : Fin N, j.val < k → m ((p 6).val + (slot j).val) =
    initial ((p 5).val + (initial ((p 4).val + (slot j).val)).val)
  frame : ∀ a, (∀ j : Fin N, j.val < k → a ≠ (p 6).val + (slot j).val) → m a = initial a

private theorem filled_step {p : Fin 7 → Word w} {initial m : Memory w} {slot : Fin N ↪ Fin S}
    (reg : ScanLayout p S A) (decode : ∀ j : Fin N, (offset p (word j.val)).val = (slot j).val)
    (legal : ∀ j : Fin N, (initial ((p 4).val + (slot j).val)).val < A)
    {k : ℕ} (hk : k < N) (prior : Filled p initial m slot k) :
    Filled p initial (after m (events p m (word k))) slot (k+1) := by
  let j : Fin N := ⟨k,hk⟩
  let off := offset p (word k)
  have hOff : off.val = (slot j).val := decode j
  have hs := (slot j).isLt
  have src : (p 4 + off).val = (p 4).val + (slot j).val := by
    have fit := reg.idsFit
    rw [Fin.val_add, hOff, Nat.mod_eq_of_lt (by omega)]
  have dst : (p 6 + off).val = (p 6).val + (slot j).val := by
    have fit := reg.outputFits
    rw [Fin.val_add, hOff, Nat.mod_eq_of_lt (by omega)]
  have sameId : m (p 4 + off).val = initial ((p 4).val + (slot j).val) := by
    rw [src]
    apply prior.frame
    intro l _
    have := (slot l).isLt
    have := reg.idsApart
    omega
  let id := initial ((p 4).val + (slot j).val)
  have hi : id.val < A := legal j
  have key : (p 5 + id).val = (p 5).val + id.val := by
    have fit := reg.keysFit
    rw [Fin.val_add, Nat.mod_eq_of_lt (by omega)]
  have sameKey : m (p 5 + id).val = initial ((p 5).val + id.val) := by
    rw [key]
    apply prior.frame
    intro l _
    have := (slot l).isLt
    have := reg.keysApart
    omega
  rw [after_events]
  change Filled p initial (writeMemory m (p 6 + off) (m (p 5 + m (p 4 + off).val).val)) slot (k+1)
  rw [sameId, sameKey]
  constructor
  · intro l hl
    by_cases eq : l = j
    · subst l
      simp only [writeMemory, dst, ite_true, id]
    · have hne : (slot l).val ≠ (slot j).val := fun h => eq (slot.injective (Fin.ext h))
      have hn : l.val ≠ k := fun h => eq (Fin.ext h)
      rw [writeMemory, dst, ite_eq_right (fun h => hne (Nat.add_left_cancel h))]
      exact prior.readback l (by omega)
  · intro a h
    rw [writeMemory, dst, ite_eq_right (h j (Nat.lt_succ_self k))]
    exact prior.frame a fun l hl => h l (Nat.lt_succ_of_lt hl)

private theorem run_aux {p : Fin 7 → Word w} {initial m : Memory w} {slot : Fin N ↪ Fin S}
    (reg : ScanLayout p S A) (decode : ∀ j : Fin N, (offset p (word j.val)).val = (slot j).val)
    (legal : ∀ j : Fin N, (initial ((p 4).val + (slot j).val)).val < A)
    {k : ℕ} (prior : Filled p initial m slot k) (count : ℕ) (fit : k + count ≤ N) :
    let P := ((template visit 0).instantiate w p).program
    ∃ rs, runSegment P 29 (some (word k)) m (List.replicate count []) = some rs ∧
      endState (some (word k)) rs = some (word (k+count)) ∧
      Filled p initial (after m (eventLog rs)) slot (k+count) ∧
      rs.length = count ∧ (∀ r ∈ rs, r.events.length = 28 ∧ r.probes = 3) ∧
      RAMBuckets.cost Report.probes rs = 4*count := by
  induction count generalizing k m with
  | zero => exact ⟨[],rfl,rfl,prior,rfl,by simp,rfl⟩
  | succ n ih =>
    let r : Report w := ⟨events p m (word k), some (word k+1)⟩
    have inc : word (w := w) k + 1 = word (k+1) := by
      apply Fin.ext
      simp [word, Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]
    have shift : (k+1)+n = k+(n+1) := by omega
    obtain ⟨rs,hr,hs,hf,hl,hw,hc⟩ := ih (filled_step reg decode legal (by omega) prior) (by omega)
    refine ⟨r::rs, ?_, ?_, ?_, by simp [hl], ?_, ?_⟩
    · rw [List.replicate_succ, runSegment, native, inc]
      simpa only [r, inc, Option.map_some] using congrArg (Option.map (r :: ·)) hr
    · change endState (some (word k+1)) rs = _
      rw [inc, hs, shift]
    · change Filled p initial ((events p m (word k) ++ eventLog rs).foldl BurstRAM.update m) slot _
      rw [List.foldl_append, ← shift]
      exact hf
    · intro s h
      rcases List.mem_cons.mp h with rfl | h
      · exact work p m (word k)
      · exact hw s h
    · rw [RAMBuckets.cost, show r.probes = 3 from (work ..).2, hc, Nat.mul_succ]
      omega

/-- The same public bank and program execute every visit. All live slots
contain the corresponding original classifier key. Every other cell,
including a padding slot in the output rectangle, retains its value. -/
structure FullRun (p : Fin 7 → Word w) (initial : Memory w) (slot : Fin N ↪ Fin S)
    (rs : List (Report w)) : Prop where
  executed : runSegment ((template visit 0).instantiate w p).program 29 (some 0)
    initial (List.replicate N []) = some rs
  cursor : endState (some 0) rs = some (word N)
  readback : ∀ j : Fin N, after initial (eventLog rs) ((p 6).val + (slot j).val) =
    initial ((p 5).val + (initial ((p 4).val + (slot j).val)).val)
  frame : ∀ a, (∀ j : Fin N, a ≠ (p 6).val + (slot j).val) → after initial (eventLog rs) a = initial a
  length : rs.length = N
  work : ∀ r ∈ rs, r.events.length = 28 ∧ r.probes = 3
  cost : RAMBuckets.cost Report.probes rs = 4*N

/-- Run the whole native gather through its actual cursor in increasing order. -/
theorem full_run (p : Fin 7 → Word w) (initial : Memory w) (slot : Fin N ↪ Fin S)
    (reg : ScanLayout p S A) (decode : ∀ j : Fin N, (offset p (word j.val)).val = (slot j).val)
    (legal : ∀ j : Fin N, (initial ((p 4).val + (slot j).val)).val < A) :
    ∃ rs, FullRun p initial slot rs := by
  have empty : Filled p initial initial slot 0 := ⟨by simp, fun _ _ => rfl⟩
  obtain ⟨rs,hr,hs,hf,hl,hw,hc⟩ := run_aux reg decode legal empty N (by simp)
  rw [Nat.zero_add] at hs hf
  exact ⟨rs, hr, hs, fun j => hf.readback j j.isLt, fun a h => hf.frame a (fun j _ => h j), hl, hw, hc⟩

end CompressorRecords.BundleGather.Fixed

end VPVNP
end Computability
end OAI
