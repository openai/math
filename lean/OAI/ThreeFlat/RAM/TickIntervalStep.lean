import OAI.ThreeFlat.RAM.TickIntervalRows

namespace OAI
/-! # One descriptor in the native grouped interval scan -/

namespace ThreeFlat.RAM.TickIntervalCursor

open Computability.VPVNP.BurstRAM PrivateRAM Fin.CommRing Diagonal.TickGroupIntervals

variable {w p r k : ℕ} {L : Layout} {reg : Fin 15 ↪ Fin r} {c d : Config w p r}
    {a z : ℕ} {e : Interval}

theorem Ready.jump (h : Ready L reg c a z) (q : Fin p) : Ready L reg {c with pc := q} a z :=
  ⟨h.cursor,h.stop,h.lo,h.hi,h.target,h.group,h.unit⟩

theorem RecordRegs.jump (h : RecordRegs reg c e) (q : Fin p) :
    RecordRegs reg {c with pc := q} e := ⟨h.group,h.first,h.stop,h.packed⟩

theorem Frame.jump (h : Frame reg c d) (q : Fin p) : Frame reg c {d with pc := q} :=
  ⟨h.registers,h.persistent,h.privateMem⟩

variable (M : Machine w p r k) (pc : Fin 27 → Fin p) (reg : Fin 15 ↪ Fin r) (exit : Fin p)
    (rom : Installed M pc reg exit)

include rom in
/-- From a matching four-word record, compute the clipped segment, write its
payload ramp, and restore the descriptor loop's program counter. -/
theorem advance_matching (L : Layout) (fit : L.Fits w) (e : Interval) (bounds : FitsRow e w)
    (hg : e.group = L.group) (a z : ℕ) (c : Config w p r) (m : Memory w)
    (start : c.pc = pc 11) (hc : Ready L reg c a z) (regs : RecordRegs reg c e) :
    ∃ out, advance M.program (10+5*rowSize L e) c m = some (out,writeRow L e m) ∧
      out.pc = pc 1 ∧ Ready L reg out a z ∧ Frame reg c out := by
  let d := prepared (pc 22) reg c
  have pre := advance_prepare M pc reg exit rom c m start hc.unit
  have hr : Ready L reg d a z := hc.prepared _
  have fr : Frame reg c d := frame_prepare _ _ _
  let lo := max e.first L.chunkStart
  let hi := min e.stop L.chunkEnd
  have slots : rowSize L e = hi-lo := by simp [rowSize,Interval.covered,hg,hi,lo]
  obtain ⟨hlo,hhi,hdst,htag⟩ := prepared_fields (pc 22) reg c L a z e hc regs fit bounds
  change (d.reg (reg 11)).val = lo at hlo
  change (d.reg (reg 12)).val = hi at hhi
  change d.reg (reg 13) = (firstAddr L e : Word w) at hdst
  change d.reg (reg 14) = ((1+e.packed+(lo-e.first) : ℕ) : Word w) at htag
  by_cases hl : lo ≤ hi
  · have l1 : e.first ≤ lo := le_max_left ..
    have l2 : L.chunkStart ≤ lo := le_max_right ..
    have u1 : hi ≤ L.chunkEnd := min_le_right ..
    have room : firstAddr L e+(hi-lo) < 2^w := by
      change L.mapBase+(lo-L.chunkStart)+(hi-lo) < 2^w
      have := fit.map
      omega
    have haddr : (d.reg (reg 13)).val = firstAddr L e := by
      rw [hdst,Fin.val_cast_of_lt (by omega : firstAddr L e < 2^w)]
    have data (i : ℕ) (_hi : i < hi-lo) :
        payload L e ((d.reg (reg 13)).val+i) = d.reg (reg 14)+(i : Word w) := by
      rw [haddr,htag,← Nat.cast_add]
      unfold payload
      congr 1
      change 1+e.packed+(L.chunkStart+(L.mapBase+(lo-L.chunkStart)+i-L.mapBase)-e.first) =
        1+e.packed+(lo-e.first)+i
      omega
    obtain ⟨out,run,done,frame⟩ := advance_span M pc reg exit rom (hi-lo) d m (payload L e) rfl
      hr.unit (by rw [hlo,hhi]; omega) (by rw [haddr]; exact room) data
    refine ⟨out,?_,done,hr.of_fill frame,fr.trans frame.frame⟩
    rw [haddr] at run
    rw [writeRow,slots,show 10+5*(hi-lo) = 9+(1+5*(hi-lo)) by omega]
    exact advance_trans pre run
  · have count : rowSize L e = 0 := by rw [slots]; omega
    have done : ¬d.reg (reg 11) < d.reg (reg 12) := by
      change ¬ (d.reg (reg 11)).val < (d.reg (reg 12)).val
      omega
    refine ⟨{d with pc := pc 1},?_,rfl,hr.jump _,fr.jump _⟩
    simpa [writeRow,count] using advance_trans pre (advance_write_done M pc reg exit rom d m rfl done)

include rom in
theorem advance_row (L : Layout) (fit : L.Fits w) (e : Interval) (bounds : FitsRow e w)
    (a z : ℕ) (room : a+4 ≤ z) (limit : z < 2^w) (c : Config w p r) (m : Memory w)
    (start : c.pc = pc 1) (hc : Ready L reg c a z) (stored : StoresRow m a e) :
    ∃ out, advance M.program (rowSteps L e) c m = some (out,writeRow L e m) ∧
      out.pc = pc 1 ∧ Ready L reg out (a+4) z ∧ Frame reg c out := by
  let f := fetched (pc 10) reg m c
  have more : c.reg (reg 0) < c.reg (reg 1) := by
    rw [hc.cursor,hc.stop,Fin.lt_def,Fin.val_cast_of_lt (by omega),Fin.val_cast_of_lt limit]
    omega
  have read := advance_fetch M pc reg exit rom c m start more hc.unit
  have groupStep := advance_group M pc reg exit rom f m rfl
  obtain ⟨ready,rr⟩ := fetched_fields (pc 10) reg c m L a z e hc room limit stored
  have fr : Frame reg c f := frame_fetch ..
  change Ready L reg f (a+4) z at ready
  change RecordRegs reg f e at rr
  by_cases hg : e.group = L.group
  · have good : f.reg (reg 7) = f.reg (reg 5) := by rw [rr.group,ready.group,hg]
    rw [ite_eq_left good] at groupStep
    obtain ⟨out,run,done,hout,frame⟩ := advance_matching M pc reg exit rom L fit e bounds hg
      (a+4) z {f with pc := pc 11} m rfl (ready.jump _) (rr.jump _)
    refine ⟨out,?_,done,hout,(fr.jump _).trans frame⟩
    rw [show rowSteps L e = (9+1)+(10+5*rowSize L e) by simp only [rowSteps,ite_eq_left hg]; omega]
    exact advance_trans (advance_trans read groupStep) run
  · have bad : f.reg (reg 7) ≠ f.reg (reg 5) := by
      rw [rr.group,ready.group]
      intro eq
      exact hg (by simpa only [Fin.val_cast_of_lt bounds.1,Fin.val_cast_of_lt fit.group] using congrArg Fin.val eq)
    rw [ite_eq_right bad] at groupStep
    refine ⟨{f with pc := pc 1},?_,rfl,ready.jump _,fr.jump _⟩
    simpa [rowSteps,writeRow,rowSize,Interval.covered,hg] using advance_trans read groupStep

end ThreeFlat.RAM.TickIntervalCursor

end OAI
