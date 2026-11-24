import OAI.Computability.VPVNP.CompressorShrinkResidentRun
import OAI.Computability.VPVNP.CompressorShrinkResidentHeaders
import OAI.Computability.VPVNP.CompressorShrinkSelectedScans

/-! # Cursors and probe addresses in the resident counter, append, and publication scans -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkResidentPackets

open Compression BurstRAM PrimedStackRAM SourceTransport SourceOnline ShrinkResidentLayout ShrinkResidentRun
open scoped Fin.CommRing

variable {w : ℕ}

theorem clear_bounds {base : Word w} {n : ℕ} (fit : base.val+n < 2^w) {m : Memory w} {rs : List (Report w)}
    (run : runSegment ((template SliceRAM.clearOps 0).instantiate w (fun _ => base)).program 8 (some 0) m
      (List.replicate n []) = some rs) :
    Progress (n : Word w) 0 rs ∧ Reads (fun _ => False) (eventLog rs) ∧
      Writes (fun x => base.val ≤ x ∧ x < base.val+n) (eventLog rs) := by
  obtain ⟨order,read,write⟩ := ShrinkHistoryTrace.clear_scanned base n fit.le m rs run
  exact ⟨order.toProgress (by omega),read,write⟩

theorem append_bounds {p : Fin 6 → Word w} (regions : RowRegions p) {m : Memory w} {rs : List (Report w)}
    (run : runSegment ((template collectPreimage 3).instantiate w p).program 23 (some 0) m
      (List.replicate (p 0).val []) = some rs) :
    Progress (p 0) 0 rs ∧ Reads (SlotFillFootprint.AppendReads p) (eventLog rs) ∧
      Writes (SlotFillFootprint.AppendWrites p) (eventLog rs) := by
  have order := ShrinkHistoryTrace.append_scanned p (p 0).val m rs run
  have prog := order.toProgress (p 0).isLt
  have word : ((p 0).val : Word w) = p 0 := Fin.ext (Nat.mod_eq_of_lt (p 0).isLt)
  rw [word] at prog
  exact ⟨prog,SlotFillFootprint.append_run regions run⟩

variable {a g : ℕ} (X : State a (packingLaneBits a g)) (first : ℕ) (absolute roles : Word w) (side maps : Bool)
variable {m : Memory w} {r : Passes w} (h : Built X first absolute roles side maps m r)

include h in
theorem counter_scan (fit : (layout X first).endAddr < 2^w) :
    Progress ((layout X first).sites : Word w) 0 r.clear ∧ Reads (fun _ => False) (eventLog r.clear) ∧
      Writes (fun x => (layout X first).counts maps ≤ x ∧ x < (layout X first).rows maps) (eventLog r.clear) := by
  obtain ⟨_,_,_,_,hc,_,_⟩ := frame X first maps fit
  obtain ⟨_,_,next,stop⟩ := (layout X first).ranges maps
  let p := outputBank (w := w) X first maps
  change (p 3).val = _ at hc
  have bound : (p 3).val+(layout X first).sites < 2^w := by omega
  obtain ⟨prog,rd,wr⟩ := clear_bounds bound h.clear
  rw [hc,next] at wr
  exact ⟨prog,rd,wr⟩

include h in
theorem preimage_scan (fit : (layout X first).endAddr < 2^w) :
    Progress ((layout X first).size maps : Word w) 0 r.collect ∧
      Reads (fun x => first ≤ x ∧ x < (layout X first).endAddr) (eventLog r.collect) ∧
      Writes (fun x => first ≤ x ∧ x < (layout X first).endAddr) (eventLog r.collect) := by
  let L := layout X first
  let p := outputBank (w := w) X first maps
  obtain ⟨reg,h0,h1,h2,h3,h4,h5⟩ := frame X first maps fit
  have h0p : (p 0).val = L.size maps := h0
  have run := h.collect
  change runSegment _ 23 _ _ (List.replicate (L.size maps) []) = some r.collect at run
  rw [← h0p] at run
  obtain ⟨prog,rd,wr⟩ := append_bounds reg run
  obtain ⟨owner,counts,rows,last⟩ := L.ranges maps
  have size := size_eq_rows X first maps
  refine ⟨prog,?_,?_⟩
  · intro a v hit
    have ha := rd a v hit
    simp only [SlotFillFootprint.AppendReads,SlotFillFootprint.InColumn,h0,h1,h3,h2] at ha
    change first ≤ a.val ∧ a.val < L.endAddr
    change (L.owner maps ≤ a.val ∧ a.val < L.owner maps+L.size maps) ∨
      (L.counts maps ≤ a.val ∧ a.val < L.counts maps+L.sites) at ha
    change first ≤ L.owner maps at owner
    omega
  · intro a v hit
    have ha := wr a v hit
    simp only [SlotFillFootprint.AppendWrites,SlotFillFootprint.InColumn,h3,h2,h5,h4] at ha
    change first ≤ a.val ∧ a.val < L.endAddr
    change (L.counts maps ≤ a.val ∧ a.val < L.counts maps+L.sites) ∨
      (L.rows maps ≤ a.val ∧ a.val < L.rows maps+L.sites*rowCapacity _ maps) at ha
    change L.size maps = L.sites*rowCapacity _ maps at size
    change first ≤ L.owner maps at owner
    omega

theorem header_scan (level : ℕ) (L : Layout) (j : Fin 6) (fit : level+36 ≤ 2^w) :
    let rs := [ShrinkResidentsPlan.headerReport level L w j]
    Progress (1 : Word w) 0 rs ∧ Reads (fun _ => False) (eventLog rs) ∧
      Writes (fun x => x = level+(30+j.val)) (eventLog rs) := by
  refine ⟨.next ?_ rfl (.done le_rfl),?_,?_⟩
  · change 0 % (2^w) < 1 % (2^w)
    rw [Nat.zero_mod,Nat.mod_eq_of_lt (by omega : 1 < 2^w)]
    decide
  · intro a v hv
    simp [eventLog,ShrinkResidentsPlan.headerReport] at hv
  · intro a v hv
    simp only [eventLog,List.flatMap_cons,List.flatMap_nil,List.append_nil,ShrinkResidentsPlan.headerReport,
      List.mem_cons,List.not_mem_nil,or_false,false_or,reduceCtorEq,Event.write.injEq] at hv
    obtain ⟨rfl,_⟩ := hv
    exact Nat.mod_eq_of_lt (by have := j.isLt; omega)

end CompressorRecords.ShrinkResidentPackets

end VPVNP
end Computability
end OAI
