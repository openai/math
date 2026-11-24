import OAI.Computability.VPVNP.LiveHeaderRuns
import OAI.Computability.VPVNP.GroupContraction

/-!
# Scanning the index in the physical live-group headers

Group `g` in the contraction has one-based number `g.val + 1`. Its bits
occupy slot zero of the first `h+2` processor headers. The native scan reads
those packed words and writes only its designated scratch, leaving all four
fields of every processor header available to the later phases.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeader

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ChainAssignments
open scoped Fin.CommRing

variable {w d a h Δ : ℕ}

/-- Only the copy buffer and the two summary words can change. -/
def IndexFrame (pub : Fin 3 → Word w) (len : ℕ) (before out : Memory w) : Prop :=
  ∀ addr, (addr < (pub 0).val ∨ (pub 0).val + len ≤ addr) →
    addr ≠ (pub 1).val → addr ≠ (pub 2).val → out addr = before addr

private theorem index_scan_frame (hw : 4 ≤ w) (pub : Fin 3 → Word w) (len : ℕ) (m : Memory w)
    (layout : ScanLayout pub len) :
    let P := ((template indexCell 11).instantiate w pub).program
    ∃ rs, runSegment P 22 (some 0) m (List.replicate len []) = some rs ∧
      IndexFrame pub len m (after m (eventLog rs)) := by
  obtain ⟨rs, hr, _, frame, _, _⟩ := run_cursor_segment
    ((template indexCell 11).instantiate w pub).program 22 len 6
    (fun _ mem => IndexFrame pub len m mem) m (fun _ _ _ _ => rfl) (by
      intro j hj mem hframe
      have hafter := layout.highAfter
      have hfit := (pub 1).isLt
      have hjv : (j : Word w).val = j := (Fin.val_natCast ..).trans (Nat.mod_eq_of_lt (by omega))
      have ha : (pub 0 + (j : Word w)).val = (pub 0).val + j := by
        rw [Fin.val_add, hjv, Nat.mod_eq_of_lt (by omega)]
      obtain ⟨es, rs', ht, hn, _, hp, _⟩ := indexCell_trace hw pub (j : Word w) (fun _ => 0) mem
      refine ⟨es, ?_, ?_, hp.le⟩
      · change execute ((template indexCell 11).instantiate w pub).program (1+indexCell.length)
          ⟨_,(j : Word w),fun _ => 0,fun _ => 0⟩ mem [] = _
        rw [execute_template, run_eq_trace, ht]
        simp [hn]
      · rw [trace_after ht]
        intro addr hout hhi hcount
        simpa [indexUpdate, writeMemory, ha, hhi, hcount, show addr ≠ (pub 0).val + j by omega]
          using hframe addr hout hhi hcount)
  exact ⟨rs, hr, frame⟩

/-- The original scan invariant and the full memory frame hold on the same
deterministic segment. -/
theorem index_scan_native_framed (hw : 4 ≤ w) (pub : Fin 3 → Word w) (index len : ℕ)
    (m : Memory w) (layout : ScanLayout pub len) (init : ScanInv pub index len 0 m) :
    let P := ((template indexCell 11).instantiate w pub).program
    ∃ rs, runSegment P 22 (some 0) m (List.replicate len []) = some rs ∧
      endState (some 0) rs = some (len : Word w) ∧ rs.length = len ∧
      (∀ x ∈ rs, countProbes x.events ≤ 6) ∧ ScanInv pub index len len (after m (eventLog rs)) ∧
      IndexFrame pub len m (after m (eventLog rs)) := by
  obtain ⟨rs, hr, he, inv, hlen, hp⟩ := index_scan_native hw pub index len m layout init
  obtain ⟨rs', hr', frame⟩ := index_scan_frame hw pub len m layout
  have eq : rs = rs' := Option.some.inj (hr.symm.trans hr')
  exact ⟨rs, hr, he, hlen, hp, inv, eq ▸ frame⟩

private theorem group_fit (g : Fin (2^(h+1))) : g.val+1 < 2^(h+2) := by
  have := g.isLt
  have : 2^(h+2) = 2^(h+1) * 2 := pow_succ 2 (h+1)
  omega

/-- Slot zero of each occupied processor holds the corresponding bit of the
one-based group number, including the highest bit of the last group. -/
theorem physical_index_bit (advice : CutSchedule.Bits a) (cuts : AllCuts h Δ)
    (g : Fin (2^(h+1))) (v : Fin (2^d)) (hv : v.val < h+2) :
    physicalHeader advice cuts g v 0 = (g.val + 1).testBit v.val := by
  let n : Word (h+2) := ⟨g.val+1, group_fit g⟩
  change distributedBit (RAMSerialization.wordBits (h+2) n) v.val = _
  rw [distributedBit, dite_eq_left hv]
  exact (testBit_wordBits n ⟨v.val,hv⟩).symm

/-- The actual memory installed for a live group in the contraction. -/
abbrev physicalMemory (hw : 4 ≤ w) (advice : CutSchedule.Bits a) (cuts : AllCuts h Δ)
    (g : Fin (2^(h+1))) : Memory w :=
  RAMMemory.initialMemory (2^d) (liveHeader (d := d) hw advice cuts g)

/-- Readback of all four physical header bits as their original packed word. -/
theorem physicalMemory_word (hw : 4 ≤ w) (advice : CutSchedule.Bits a) (cuts : AllCuts h Δ)
    (g : Fin (2^(h+1))) (v : Fin (2^d)) :
    physicalMemory (d := d) hw advice cuts g v.val = ProcessorInput.headerWord hw (physicalHeader advice cuts g v) := by
  simp [physicalMemory, RAMMemory.initialMemory, liveHeader, v.isLt]

/-- Exact summaries and bit arrays available to the live program after the
scan. All later reads of the site headers see the prescribed physical words. -/
structure PhysicalIndex (hw : 4 ≤ w) (pub : Fin 3 → Word w) (advice : CutSchedule.Bits a)
    (cuts : AllCuts h Δ) (g : Fin (2^(h+1))) (out : Memory w) : Prop where
  copied : ∀ j < h+2, out ((pub 0).val+j) = PrimedInputRAM.encodeBit w ((g.val+1).testBit j)
  high : (out (pub 1).val).val = Nat.log 2 (g.val+1)
  count : (out (pub 2).val).val = (prefixOnes (g.val+1) (h+2)).card
  low : out (pub 0).val = PrimedInputRAM.encodeBit w ((g.val+1).testBit 0)
  first : (out (pub 1).val).val = 0 ↔ g.val = 0
  singleton : (out (pub 2).val).val = 1 ↔ g.val+1 = 2^(Nat.log 2 (g.val+1))
  headers : ∀ v : Fin (2^d), out v.val = ProcessorInput.headerWord hw (physicalHeader advice cuts g v)
  frame : IndexFrame pub (h+2) (physicalMemory (d := d) hw advice cuts g) out

/-- Run the index scan starting at the actual header memory of the group,
with its two scalar scratch cells initially zero by RAM initialization. -/
theorem physical_index_scan_native (hw : 4 ≤ w) (pub : Fin 3 → Word w) (advice : CutSchedule.Bits a)
    (cuts : AllCuts h Δ) (g : Fin (2^(h+1))) (sites : h+2 ≤ 2^d) (scratch : 2^d ≤ (pub 0).val)
    (layout : ScanLayout pub (h+2)) :
    let P := ((template indexCell 11).instantiate w pub).program
    let m := physicalMemory (d := d) hw advice cuts g
    ∃ rs, runSegment P 22 (some 0) m (List.replicate (h+2) []) = some rs ∧
      endState (some 0) rs = some ((h+2 : ℕ) : Word w) ∧ rs.length = h+2 ∧
      (∀ x ∈ rs, countProbes x.events ≤ 6) ∧
      PhysicalIndex (d := d) hw pub advice cuts g (after m (eventLog rs)) := by
  let m := physicalMemory (d := d) hw advice cuts g
  have hafter := layout.highAfter
  have hcafter := layout.countAfter
  have hmod := (pub 2).isLt
  have hinit : ScanInv pub (g.val+1) (h+2) 0 m := by
    constructor
    · intro j hj
      let v : Fin (2^d) := ⟨j, hj.trans_le sites⟩
      change (physicalMemory (d := d) hw advice cuts g v.val).val.testBit (0 : Fin 4).val = _
      rw [physicalMemory_word]
      change (ProcessorInput.headerWord hw (physicalHeader advice cuts g v)).val.testBit
        ((0 : Fin 4).castLE hw).val = _
      rw [testBit_wordBits, ProcessorInput.headerWord_bit]
      exact physical_index_bit advice cuts g v hj
    · simp [m, physicalMemory, RAMMemory.initialMemory, show ¬(pub 1).val < 2^d by omega,
        prefixHigh, prefixOnes]
    · simp [m, physicalMemory, RAMMemory.initialMemory, show ¬(pub 2).val < 2^d by omega,
        prefixOnes]
    · omega
  obtain ⟨rs, run, last, len, hp, inv, frame⟩ := index_scan_native_framed hw pub _ _ m layout hinit
  have hfit := group_fit g
  have ⟨hhigh, hone⟩ := summary_correct (by omega : g.val+1 ≠ 0) hfit
  have hlog : Nat.log 2 (g.val+1) < h+2 := (Nat.log_lt_iff_lt_pow (by decide) (by omega)).mpr hfit
  have hcount : (prefixOnes (g.val+1) (h+2)).card ≤ h+2 := by
    simpa [prefixOnes] using Finset.card_filter_le (Finset.range (h+2)) (fun j => (g.val+1).testBit j)
  have high : ((after m (eventLog rs)) (pub 1).val).val = Nat.log 2 (g.val+1) := by
    rw [inv.high, hhigh, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have count : ((after m (eventLog rs)) (pub 2).val).val = (prefixOnes (g.val+1) (h+2)).card := by
    rw [inv.count, Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  refine ⟨rs, run, last, len, hp, inv.copied, high, count, ?_, ?_, count ▸ hone, ?_, frame⟩
  · simpa using inv.copied 0 (by omega)
  · rw [high, Nat.log_eq_zero_iff]
    omega
  · intro v
    have hv := v.isLt
    rw [frame v.val (Or.inl (hv.trans_le scratch)) (by omega) (by omega)]
    exact physicalMemory_word hw advice cuts g v

end LiveHeader

end VPVNP
end Computability
end OAI
