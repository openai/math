import OAI.Computability.VPVNP.CompressorShrinkHistoryAccess
import OAI.Computability.VPVNP.CompressorShrinkSlotOrdinals
import OAI.Computability.VPVNP.CompressorSlotFillFootprint
import OAI.Computability.VPVNP.CompressorScanProgress

/-! # Progress and address bounds of selected layout and child-directory scans -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkHistoryTrace

open BurstRAM Compression PrimedStackRAM SourceTransport SelectedArena
open scoped Fin.CommRing Classical

variable {w : ℕ}

theorem emptyScanned {Q : Type*} (P : BurstRAM.Program w Q) (f : ℕ)
    (advance : ∀ m i r, execute P f (P.start i) m [] = some r → r.result=some (i+1))
    {j n N : ℕ} (size : j+n=N) (m : Memory w) (rs : List (Report w))
    (run : runSegment P f (some (j : Word w)) m (List.replicate n [])=some rs) :
    StageFrame.Scanned j N rs := by
  induction n generalizing j rs m with
  | zero =>
    change some []=some rs at run
    rw [← Option.some.inj run,show j=N by omega]
    exact .done _
  | succ n ih =>
    rw [List.replicate_succ,runSegment] at run
    cases head : execute P f (P.start (j : Word w)) m [] with
    | none => rw [head] at run; contradiction
    | some r =>
      rw [head] at run
      obtain ⟨tail,ht,rfl⟩ := Option.map_eq_some_iff.mp run
      have ret := advance m (j : Word w) r head
      rw [← Nat.cast_add_one] at ret
      rw [ret] at ht
      exact .next (by omega) ret (ih (by omega) _ tail ht)

open private append_result from OAI.Computability.VPVNP.CompressorShrinkSlotOrdinals

theorem append_scanned (p : Fin 6 → Word w) (n : ℕ) (m : Memory w) (rs : List (Report w))
    (run : runSegment ((template collectPreimage 3).instantiate w p).program 23 (some 0) m (List.replicate n [])=some rs) :
    StageFrame.Scanned 0 n rs :=
  emptyScanned _ _ (append_result p) (Nat.zero_add n) m rs run

theorem clear_scanned (b : Word w) (n : ℕ) (room : b.val+n ≤ 2^w) (m : Memory w) (rs : List (Report w))
    (run : runSegment ((template SliceRAM.clearOps 0).instantiate w (fun _ => b)).program 8 (some 0) m (List.replicate n [])=some rs) :
    StageFrame.Scanned 0 n rs ∧ Reads (fun _ => False) (eventLog rs) ∧
      Writes (SlotFillFootprint.InColumn b.val n) (eventLog rs) := by
  obtain ⟨hs,_,hr,hw⟩ := StageFrame.scan _ 8 0 n (fun _ _ => True)
    (fun _ i => (SliceRAM.clearReport b i).events) (fun _ => False) (SlotFillFootprint.InColumn b.val n)
    (fun j _ _ mem => SliceRAM.clearVisit_native b (j : Word w) mem) (fun j _ hj mem _ => by
      have addr : (b+(j : Word w)).val=b.val+j := by
        rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (show j<2^w by omega),Nat.mod_eq_of_lt (show b.val+j<2^w by omega)]
      refine ⟨trivial,?_,?_⟩
      · intro a v h; simp [SliceRAM.clearReport] at h
      · intro a v h
        simp [SliceRAM.clearReport] at h
        rw [h.1,addr]; exact ⟨Nat.le_add_right ..,Nat.add_lt_add_left hj _⟩)
    (Nat.zero_le n) m rs trivial (by simpa only [Nat.sub_zero,Nat.cast_zero] using run)
  exact ⟨hs,hr,hw⟩

end CompressorRecords.ShrinkHistoryTrace

end VPVNP
end Computability
end OAI
