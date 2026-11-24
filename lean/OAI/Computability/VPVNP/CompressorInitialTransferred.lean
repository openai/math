import OAI.Computability.VPVNP.CompressorInitialPhysical
import OAI.Computability.VPVNP.LiveCompressedPairStartupRun

/-! # Exact startup memory of the physical pair at the cursor prefix -/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.InitialTransferred

open BurstRAM Compression DescriptorSpace BlockPlanner CursorBounds LiveProgram.CompressedPair
open scoped Fin.CommRing
open private startupStage from OAI.Computability.VPVNP.LiveCompressedPairCursorStartup

variable {w : ℕ}

private theorem after_ofFn {k : ℕ} (entry : Fin (k+1) → Memory w) (rs : Fin k → Report w)
    (step : ∀ i, after (entry i.castSucc) (rs i).events = entry i.succ) :
    after (entry 0) (eventLog (List.ofFn rs)) = entry (Fin.last k) := by
  induction k with
  | zero => simp [eventLog,after]
  | succ k ih =>
    have tail := ih (fun j ↦ entry j.succ) (fun i ↦ rs i.succ) (fun i ↦ step i.succ)
    rw [List.ofFn_succ]
    change after (entry 0) ((rs 0).events ++ eventLog (List.ofFn (fun i : Fin k ↦ rs i.succ))) = _
    have first := step (0 : Fin (k+1))
    change after (entry 0) (rs 0).events = entry (0 : Fin (k+1)).succ at first
    rw [show ∀ (m : Memory w) (es fs), after m (es++fs) = after (after m es) fs from fun _ _ _ ↦ List.foldl_append,first]
    exact tail

/-- The emitted outer-linker reports leave exactly the memory used by
the transferred-startup and initial-cursor theorems. -/
theorem startup_memory (boot : Bootstrap) (pub : Fin 11 → Word w) (B n base : ℕ) (m : Memory w)
    (initial phases d : ℕ) :
    after m (eventLog (cursorStartupLogs boot pub B n base m initial phases d)) =
      BlockHeaderStartup.post (bootstrapRows boot initial phases) d (startupLayout boot initial phases B n base)
        B n boot.degreeBits boot.lanesPerBlock boot.steps pub (LiveProgram.PairTag.address pub) m := by
  let D := bootstrapRows boot initial phases
  let L := startupLayout boot initial phases B n base
  let t := startupTrace boot pub B n base m initial phases d
  let tag := LiveProgram.PairTag.address pub
  change after (t.entry tag m 0) (eventLog (List.ofFn (startupReport boot pub B n base m initial phases d))) =
    t.entry tag m (Fin.last 8)
  apply after_ofFn
  intro i
  have step : next (startupStage i.castSucc) = some (startupStage i.succ) := by fin_cases i <;> rfl
  have closed := TransferredStartup.source_closed D d L B n boot.degreeBits boot.lanesPerBlock boot.steps
    pub tag m i
  change (t.source i).result = none at closed
  have eff := (report_effect pub (startupStage i.castSucc) (t.source i) (t.entry tag m i.castSucc)).2.2.2
  rw [closed,step] at eff
  exact eff.trans (t.transfer tag m i).symm

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

/-- Startup parameters for the compiled compressor, including the allocation shape, lane and
degree dimensions, and scale numerator and denominator. -/
noncomputable def bootstrap (p q : ℕ) : Bootstrap :=
  ⟨BlockProgram.allocationShape B,S.degreeExponent 0,S.laneBits,S.steps,p,q⟩

theorem arity : 11 ≤ (BlockProgram.allocationShape B).arity := by
  let A := BlockProgram.script B
  let i : Fin A.initial.length := ⟨2,by change 2 < 4; decide⟩
  have hc : A.catalog (i.castAdd A.block.length) = Schedule.cursorPass := by
    change (A.visit (i.castAdd A.block.length)).worker = _
    rw [A.initial_visit]; rfl
  have h := Schedule.params_le_arity A.catalog (i.castAdd A.block.length)
  rw [hc] at h
  exact h

theorem phases_pos : 0 < (BlockProgram.block B).length := by
  simp only [BlockProgram.block,BlockProgram.refresh,List.length_append,List.length_cons,List.length_nil]
  omega

/-- The native startup's computed row count selects precisely the concrete
block-program allocation for this input and its actual integer block count. -/
theorem allocation (p q Baddr n base : ℕ) :
    startupLayout (bootstrap B p q) (BlockProgram.initial B).length (BlockProgram.block B).length Baddr n base =
      BlockProgram.layout B base (initialPositions Baddr n) (roundedDown p q n) := by
  simp only [startupLayout,bootstrap,bootstrapRows,OnlineWorkspace.rowsSpec,CalendarRows.rows,cursorLayout,
    BlockProgram.layout,roundedDown_eq,Nat.mul_comm (BlockProgram.block B).length]

open CursorNetwork CursorRouting in
/-- Uniformly in the initial RAM contents, the post-memory of the eight
literal pair calls supplies the concrete four-visit cursor development.
The allocation and row count are those of the actual block program. -/
theorem eventually_resident (p q Baddr : ℕ) (hq : 0 < q) (hB : 1 ≤ Baddr)
    (hθ : (p : ℝ)/q ≤ 1) (hlanes : S.laneBits ≤ Baddr) {base : ℕ → ℕ} (hb : PolynomiallyBounded base) :
    let A := BlockProgram.script B
    let boot := bootstrap B p q
    let a := S.degreeExponent 0
    let pad := 2^a-2
    ∃ hd : 2+pad = 2^a, ∀ᶠ n : ℕ in Filter.atTop, ∀ (pub : Fin 11 → Word (wordBits Baddr n)),
      (pub 2).val = base n → (pub 6).val = n → (pub 7).val = addressBits Baddr n →
      (LiveProgram.PairTag.address pub).val < base n → ∀ m,
      let T := roundedDown p q n
      let l := T*S.laneBits
      let b := virtualBits Baddr n-l
      let L := BlockProgram.layout B (base n) (initialPositions Baddr n) T
      let mem := after m (eventLog (cursorStartupLogs boot pub Baddr n (base n) m A.initial.length A.block.length A.size))
      let bits : RAMSystem (virtualBits Baddr n) → ℕ := ramFieldBits (virtualBucket n) (wordBits Baddr n)
      ∃ hD : 1 < b+l, BlockStartupPrefix.Resident L a b l (initialWidth Baddr n) n (pub 2) mem
        (cursorState (cursorCoordinateLabels b l) hD hd bits) := by
  intro A boot a pad
  have hd : 2+pad = 2^a := by
    dsimp only [a,pad]
    rw [S.initial,pow_succ]
    have := Nat.two_pow_pos S.expanderExponent
    omega
  refine ⟨hd,?_⟩
  let D := bootstrapRows boot A.initial.length A.block.length
  have hph : 0 < D.phaseRows := phases_pos B
  have ha : 7 ≤ boot.shape.arity := (by decide : 7 ≤ 11).trans (arity B)
  have hs : 30 ≤ boot.shape.scalarFields := by change 30 ≤ 54; decide
  filter_upwards [BlockStartupPrefix.eventually_resident D A.size boot.shape Baddr a pad S.laneBits S.steps
    hd hB hq hph hθ hlanes ha hs hb] with n ready
  intro pub workspace len addr lower m T l b L mem bits
  have source := ready pub (LiveProgram.PairTag.address pub) workspace len addr lower m
  have hL : startupLayout boot A.initial.length A.block.length Baddr n (base n) = L :=
    allocation B p q Baddr n (base n)
  have hm := startup_memory boot pub Baddr n (base n) m A.initial.length A.block.length A.size
  change mem = _ at hm
  rw [← hL,hm]
  exact source

end CompressorRecords.InitialTransferred

end VPVNP
end Computability
end OAI
