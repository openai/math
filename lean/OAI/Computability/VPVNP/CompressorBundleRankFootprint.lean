import OAI.Computability.VPVNP.CompressorRecordsPortRankScan
import OAI.Computability.VPVNP.CompressorSlotScanFootprint

/-! # Probe addresses of the absolute-port rank scan

A ranking call reads the owner and pivot, reads the owner's count and then
scans the whole fixed-stride row, including its padding. Its only write is
the rank indexed by the visiting old port.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRankRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SourceTransport
open private preEvents walkEvents finalEvents setup_trace walk_trace finish_trace word_succ
  from OAI.Computability.VPVNP.CompressorRecordsPortRankRAM

variable {w : ℕ}

private def exactEvents (p : Fin 6 → Word w) (cap : ℕ) (m : Memory w) (i : Word w) :=
  preEvents p m i ++ (walkEvents m (start p m i) cap ++ finalEvents p i (result p m i cap))

private theorem native_events (p : Fin 6 → Word w) (cap : ℕ) (m : Memory w) (i : Word w) :
    let P := ((template (visit cap) 0).instantiate w p).program
    execute P (1+(visit cap).length) (P.start i) m [] = some ⟨exactEvents p cap m i,some (i+1)⟩ := by
  obtain ⟨r,hs,h0,hptr,hpiv,hrem,hacc,hu⟩ := setup_trace p m i
  obtain ⟨s,hw,hs0,hsu,hs4⟩ := walk_trace p m i cap r hu
  obtain ⟨t,hf,hret⟩ := finish_trace p m i s (hs0.trans h0) hsu
  have val : s 4 = result p m i cap := by simpa only [result,row,hptr,hpiv,hrem,hacc,zero_add] using hs4
  rw [val] at hf
  change execute ((template (visit cap) 0).instantiate w p).program (1+(visit cap).length)
    ⟨_,i,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _
  rw [execute_template,run_eq_trace,visit,trace_append,trace_append,hs]
  simp [hw,hf,hret,hptr,exactEvents,List.append_assoc]

private theorem walk_access (m : Memory w) (ptr : Word w) (cap : ℕ) (rd : ℕ → Prop)
    (live : ∀ j < cap, rd (ptr+Fin.ofNat (2^w) j).val) :
    Reads rd (walkEvents m ptr cap) ∧ Writes (fun _ ↦ False) (walkEvents m ptr cap) := by
  induction cap generalizing ptr with
  | zero => simp [walkEvents,Reads,Writes]
  | succ n ih =>
    have later (j : ℕ) (hj : j < n) : rd (ptr+1+Fin.ofNat (2^w) j).val := by
      have eq : ptr+1+Fin.ofNat (2^w) j = ptr+Fin.ofNat (2^w) (j+1) := by
        rw [word_succ,add_right_comm,add_assoc]
      rw [eq]; exact live _ (by omega)
    obtain ⟨rs,ws⟩ := ih (ptr+1) later
    constructor <;> intro a v h
    · rw [walkEvents] at h
      rcases List.mem_append.mp h with h | h
      · simp only [List.mem_cons,List.not_mem_nil,or_false,reduceCtorEq,Event.read.injEq] at h
        obtain ⟨rfl,_⟩ := h
        simpa using live 0 (Nat.zero_lt_succ n)
      · exact rs a v h
    · rw [walkEvents] at h
      rcases List.mem_append.mp h with h | h
      · simp at h
      · exact ws a v h

private theorem row_access (p : Fin 6 → Word w) (cap : ℕ) (m : Memory w) (i : Word w) (rd wr : ℕ → Prop)
    (bounds : ∀ x ∈ inputs p m i cap, rd x.val) (dest : wr (p 5+i).val) :
    Reads rd (exactEvents p cap m i) ∧ Writes wr (exactEvents p cap m i) := by
  obtain ⟨walkRd,walkWr⟩ := walk_access m (start p m i) cap rd fun j hj ↦
    bounds _ (List.mem_append_right _ (List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩))
  constructor <;> intro a v h
  · rcases List.mem_append.mp h with h | h
    · simp only [preEvents,List.mem_cons,List.not_mem_nil,or_false,false_or,reduceCtorEq,Event.read.injEq] at h
      rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩ <;> exact bounds _ (by simp [inputs])
    · rcases List.mem_append.mp h with h | h
      · exact walkRd a v h
      · simp [finalEvents] at h
  · rcases List.mem_append.mp h with h | h
    · simp [preEvents] at h
    · rcases List.mem_append.mp h with h | h
      · exact (walkWr a v h).elim
      · simp only [finalEvents,List.mem_cons,List.not_mem_nil,or_false,false_or,reduceCtorEq,Event.write.injEq] at h
        exact h.1 ▸ dest

/-- Accesses in every report of an actual completed native ranking scan. -/
theorem scan_access (p : Fin 6 → Word w) (init : Memory w) (cap A : ℕ)
    (reg : Regions p init cap A) (rd wr : ℕ → Prop)
    (read : ∀ j < A, ∀ x ∈ inputs p init (Fin.ofNat _ j) cap, rd x.val)
    (write : ∀ j < A, wr ((p 5).val+j)) (rs : List (Report w))
    (run : runSegment ((template (visit cap) 0).instantiate w p).program (1+(visit cap).length)
      (some 0) init (List.replicate A []) = some rs) : Reads rd (eventLog rs) ∧ Writes wr (eventLog rs) := by
  let I (mem : Memory w) := ∀ j < A, owner p mem (Fin.ofNat _ j) = owner p init (Fin.ofNat _ j)
  apply SlotEventBounds.scan _ _ A (exactEvents p cap) I rd wr (native_events p cap) _ init rs (fun _ _ ↦ rfl) run
  intro j hj mem same
  let i := Fin.ofNat (2^w) j
  have hd : (p 5+i).val = (p 5).val+j := by
    rw [Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod,Nat.mod_eq_of_lt (by have := reg.outputFits; omega)]
  have equal : inputs p mem i cap = inputs p init i cap := by simp only [inputs,start,same j hj,i]
  obtain ⟨hr,hw⟩ := row_access p cap mem i rd wr (fun x hx ↦ read j hj x (equal ▸ hx)) (hd ▸ write j hj)
  refine ⟨hr,hw,fun k hk ↦ ?_⟩
  obtain ⟨es,he,afterEq,_,_⟩ := run_one p mem i cap
  obtain ⟨rfl,_⟩ := Report.mk.inj (Option.some.inj (he.symm.trans (native_events p cap mem i)))
  have src := reg.reads k hk (p 0+Fin.ofNat _ k) (by simp [inputs])
  unfold owner at *
  rw [afterEq,writeMemory,ite_eq_right (by omega)]
  exact same k hk

end CompressorRecords.PortRankRAM

end VPVNP
end Computability
end OAI
