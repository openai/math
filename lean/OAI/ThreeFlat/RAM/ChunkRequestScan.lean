import OAI.ThreeFlat.RAM.ChunkRequestBlock
import OAI.ThreeFlat.RAM.CursorScan

namespace OAI
/-! # A fixed native loop over one chunk's interval of prepared requests -/

namespace ThreeFlat.RAM.ChunkRequests

open Computability.VPVNP.BurstRAM PrivateRAM

variable {w p r k : ℕ}

def scan (D : Fin k → Word w) (R : Registers w k r) (L : Labels w k p) :=
  CursorScan.run (body D R L) (L.expr (rowTerm w k).first) L.exit

/-- The loop uses one final comparison and sixty-one instructions per request. -/
theorem mass_scan {F : Type*} [Semiring F] (field : FieldCode F w) (M : Machine w p r k)
    (R : Registers w k r) (L : Labels w k p) (rom : Installed M R L)
    (n fuel : ℕ) (c : Config w p r) (m : Memory w) (start : c.pc = L.guard)
    (stride : (c.reg (R.slot 5)).val = 4)
    (size : (c.reg (R.slot 0)).val + n*4 = (c.reg (R.slot 6)).val) :
    let out := scan M.publicData R L n c m
    mass field M.program (fuel+1+n*61) c m = mass field M.program fuel out.1 out.2 := by
  apply CursorScan.mass_scan field M L.guard (L.expr (rowTerm w k).first) L.exit (R.slot 0)
    (R.slot 6) 4 60 (by decide) rom.guard (body M.publicData R L)
    (fun cfg => (cfg.reg (R.slot 5)).val = 4) _ _ n fuel c m start stride size
  · intro f cfg mem hc
    exact mass_of_advance field _ (advance_body M R L rom cfg mem hc) f
  · intro cfg mem hstride hbound
    let c₀ : Config w p r := {cfg with pc := L.expr (rowTerm w k).first}
    change (body M.publicData R L c₀ mem).1.pc = L.guard ∧ _ ∧ _ ∧ _
    refine ⟨rfl, ?_, ?_, ?_⟩
    · rw [body_cursor, Fin.val_add]
      change ((cfg.reg (R.slot 0)).val + (cfg.reg (R.slot 5)).val) % (2^w) = _
      rw [hstride, Nat.mod_eq_of_lt (hbound.trans_lt (cfg.reg (R.slot 6)).isLt)]
    · exact body_reg _ _ _ c₀ mem 6 (by decide) (by decide)
    · exact (congrArg Fin.val (body_reg _ _ _ c₀ mem 5 (by decide) (by decide))).trans hstride

/-- Passing a zero flag through the scan keeps it zero. Passing a valid flag
keeps it precisely if every matching request succeeds. -/
def allRows (m : Memory w) (tag oldBase newBase stride : Word w) : ℕ → Word w → Prop
  | 0, _ => True
  | n+1, cursor => rowMatches m (readRow m cursor) tag oldBase newBase ∧
      allRows m tag oldBase newBase stride n (cursor+stride)

open scoped Classical in
theorem scan_flag (D : Fin k → Word w) (R : Registers w k r) (L : Labels w k p)
    (n : ℕ) (c : Config w p r) (m : Memory w) :
    (scan D R L n c m).1.reg (R.slot 4) =
      if allRows m (c.reg (R.slot 1)) (c.reg (R.slot 2)) (c.reg (R.slot 3))
        (c.reg (R.slot 5)) n (c.reg (R.slot 0)) then c.reg (R.slot 4) else 0 := by
  induction n generalizing c with
  | zero => simp [scan,CursorScan.run,allRows]
  | succ n ih =>
    let c₀ : Config w p r := {c with pc := L.expr (rowTerm w k).first}
    change (scan D R L n (body D R L c₀ m).1 m).1.reg (R.slot 4) = _
    rw [ih, body_flag, body_cursor, body_reg _ _ _ c₀ m 1 (by decide) (by decide),
      body_reg _ _ _ c₀ m 2 (by decide) (by decide), body_reg _ _ _ c₀ m 3 (by decide) (by decide),
      body_reg _ _ _ c₀ m 5 (by decide) (by decide)]
    dsimp only [c₀,allRows]
    split_ifs <;> simp_all

/-- Completion preserves both memories and persistent state and returns to the loop exit. -/
theorem scan_frame (D : Fin k → Word w) (R : Registers w k r) (L : Labels w k p)
    (n : ℕ) (c : Config w p r) (m : Memory w) :
    let out := scan D R L n c m
    out.1.pc = L.exit ∧ out.2 = m ∧ out.1.persistent = c.persistent ∧
      out.1.privateMem = c.privateMem := by
  induction n generalizing c with
  | zero => exact ⟨rfl,rfl,rfl,rfl⟩
  | succ n ih =>
    let c₀ : Config w p r := {c with pc := L.expr (rowTerm w k).first}
    obtain ⟨hp, hm, hs, hi⟩ := ih (body D R L c₀ m).1
    have frame := body_frame D R L c₀ m
    exact ⟨hp,hm,hs.trans frame.1,hi.trans frame.2⟩

end ThreeFlat.RAM.ChunkRequests

end OAI
