import OAI.Computability.BorderVNP.TeamSiteChunkFrame

/-!
# Complete charged-block schedules for a finite signed RAM

A row begins on a live frame decoded from the shared predecessor, or propagates
an already accepted halt. A live row executes actual finite-PC charged events,
then tests the next opcode against its residual clock. Over a complete locally
accepting RAM path these row conditions are equivalent to the paper's greedy
partition together with its canonical word-sized handoff chain.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape BurstRAM RAMTape.PublicExprMachine TeamTapeHandoff TeamLocalClock

variable {w p r k a : ℕ}

/-- Initial local and global countdowns installed from a decoded elapsed timestamp. -/
def blockWindow (H limit elapsed cap : Word w) : Window w :=
  ⟨H, packed w (limit.val - elapsed.val), elapsed, cap⟩

theorem blockWindow_total (H limit elapsed cap : Word w) (ht : elapsed ≤ limit) :
    limit.val = (blockWindow H limit elapsed cap).elapsed.val + (blockWindow H limit elapsed cap).global.val := by
  change limit.val = elapsed.val + (packed w (limit.val - elapsed.val)).val
  have h : elapsed.val ≤ limit.val := ht
  rw [packed_val (lt_of_le_of_lt (Nat.sub_le _ _) limit.isLt)]; omega

private theorem blockWindow_safe (H limit elapsed cap : Word w) (ht : elapsed ≤ limit) :
    (blockWindow H limit elapsed cap).Safe := by
  unfold Window.Safe
  rw [← blockWindow_total H limit elapsed cap ht]
  exact limit.isLt

/-- A local row with its actual finite-PC run and observed end exit. The tail determines
which next opcode the greedy test must inspect. -/
def ChargedRow (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : TeamOpcode.Macros w a)
    (H limit cap : Word w) (input : Frame w r) (es tail : List (TeamRAM.Event w)) (output : Frame w r) : Prop :=
  match input with
  | .accepted elapsed => es = [] ∧ elapsed ≤ limit ∧ output = .accepted elapsed
  | .live word regs elapsed =>
    elapsed ≤ limit ∧ ∃ (pc : Fin p) (z : TeamOpcode.State w p r) (fin : Window w),
      word = packed w pc.val ∧
      Chunk (P.fetch pub lib) ⟨pc,regs⟩ (blockWindow H limit elapsed cap) es z fin ∧
      TeamLocalClock.Loop.result P pub z fin.block fin.global fin.elapsed fin.cap = (chunkExit tail z, fin.bank pub z) ∧
      output = Finish.frame (chunkMode tail z) z.reg fin.elapsed

/-- All rows of the actual native finite-PC schedule with one transmitted frame at each end. -/
def ChargedRows (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : TeamOpcode.Macros w a)
    (H limit cap : Word w) : Frame w r → List (List (TeamRAM.Event w)) → List (Frame w r) → Prop
  | _, [], fs => fs = []
  | _, _ :: _, [] => False
  | f, es::rows, next::fs => ChargedRow P pub lib H limit cap f es rows.flatten next ∧
    ChargedRows P pub lib H limit cap next rows fs

private theorem accept_of_exit (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (z : TeamOpcode.State w p r) (fin : Window w)
    (accept : (TeamLocalClock.Loop.result P pub z fin.block fin.global fin.elapsed fin.cap).1 = .accepted) :
    P.fetch pub lib z = .accept := by
  apply (accept_iff P pub lib z).mpr
  cases h : TeamLocalClock.Loop.kind P z.pc with
  | accept => rfl
  | reject => simp [TeamLocalClock.Loop.result, h] at accept
  | ordinary =>
    cases hd : decision fin.block.val fin.global.val 0 <;>
      simp [TeamLocalClock.Loop.result, h, TeamLocalClock.Loop.afterGuard, hd] at accept
  | burst j =>
    by_cases size : z.reg j ≤ fin.cap
    · cases hd : decision fin.block.val fin.global.val (z.reg j).val <;>
        simp [TeamLocalClock.Loop.result, h, size, TeamLocalClock.Loop.afterGuard, hd] at accept
    · simp [TeamLocalClock.Loop.result, h, size] at accept

/-- Propagating an accepted status forces every subsequent block to be empty. -/
theorem ChargedRows.empty_halted {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap elapsed : Word w}
    {rows : List (List (TeamRAM.Event w))} {frames : List (Frame w r)}
    (hs : ChargedRows P pub lib H limit cap (.accepted elapsed) rows frames) : rows.flatten = [] := by
  induction rows generalizing frames with
  | nil => rfl
  | cons es rest ih =>
    cases frames with
    | nil => exact False.elim hs
    | cons f fs =>
      obtain ⟨rfl,_,rfl⟩ := hs.1
      simpa only [List.flatten_cons, List.nil_append] using ih hs.2

/-- Physical rows recover the whole finite-PC local path by concatenating the actual
charged chunks across the shared PC/register frames. No row is given the validity
of a future native path. -/
theorem ChargedRows.local_live {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap elapsed : Word w} {s : TeamOpcode.State w p r}
    {rows : List (List (TeamRAM.Event w))} {frames : List (Frame w r)}
    (hs : ChargedRows P pub lib H limit cap (.live (packed w s.pc.val) s.reg elapsed) rows frames)
    (fits : p ≤ 2^w) (ne : rows ≠ []) : TeamRAM.Local (P.fetch pub lib) s rows.flatten := by
  induction rows generalizing s elapsed frames with
  | nil => contradiction
  | cons es rest ih =>
    cases frames with
    | nil => exact False.elim hs
    | cons next fs =>
      obtain ⟨entry,regs⟩ := s
      obtain ⟨_,pc,z,fin,hw,run,close,rfl⟩ := hs.1
      have eq : entry = pc := by
        apply Fin.ext
        simpa only [packed_val (entry.isLt.trans_le fits), packed_val (pc.isLt.trans_le fits)] using congrArg Fin.val hw
      subst pc
      apply run.append_local
      cases hh : rest.flatten with
      | nil =>
        have hc := congrArg Prod.fst close
        simp only [chunkExit, hh, List.isEmpty_nil, ite_true] at hc
        exact accept_of_exit P pub lib z fin hc
      | cons e xs =>
        have tail := hs.2
        simp only [chunkMode, hh, List.isEmpty_cons, Bool.false_eq_true, ite_false, Finish.frame] at tail
        have nrest : rest ≠ [] := by rintro rfl; simp at hh
        rw [← hh]
        exact ih tail nrest

/-- A checked row followed by the checked remainder is greedy and its actual serialized
result equals the word-PC successor. The lookahead comes from that shared successor's
physical rows, or from the current physical accept instruction at the end. -/
theorem ChargedRow.spec {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap : Word w} {f next : Frame w r} {es : List (TeamRAM.Event w)}
    {rest : List (List (TeamRAM.Event w))} {frames : List (Frame w r)}
    (h : ChargedRow P pub lib H limit cap f es rest.flatten next)
    (tail : ChargedRows P pub lib H limit cap next rest frames) (fit : p ≤ 2^w)
    (bound : ∀ e ∈ rest.flatten, e.action.extra ≤ cap.val) :
    Team.MaximalBlock (fun e => e.action.extra) H.val es rest.flatten ∧
      nextFrame (Model.wordFetch P pub lib) limit f es = some next := by
  cases f with
  | accepted t =>
    obtain ⟨rfl,ht,rfl⟩ := h
    simp [tail.empty_halted, Team.MaximalBlock, RAMBuckets.cost, nextFrame, ht]
  | live word regs elapsed =>
    obtain ⟨ht,pc,z,fin,rfl,run,hclose,rfl⟩ := h
    have safe := blockWindow_safe H limit elapsed cap ht
    have same := (run.clock safe).2.2.2.2.2.2
    have localPath : TeamRAM.Local (P.fetch pub lib) z rest.flatten := by
      cases hh : rest.flatten with
      | nil =>
        have hc := congrArg Prod.fst hclose
        simp only [chunkExit, hh, List.isEmpty_nil, ite_true] at hc
        exact accept_of_exit P pub lib z fin hc
      | cons e xs =>
        simp only [chunkMode, hh, List.isEmpty_cons, Bool.false_eq_true, ite_false, Finish.frame] at tail
        rw [← hh]
        exact tail.local_live fit (by rintro rfl; simp at hh)
    exact ⟨(run.close_iff_maximal localPath safe (fun e he => same ▸ bound e he)).mp hclose,
      run.nextFrame localPath fit limit (blockWindow_total H limit elapsed cap ht)⟩

/-- A checked schedule induces the greedy partition and the canonical shared frame chain. -/
theorem ChargedRows.spec {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : TeamOpcode.Macros w a} {H limit cap : Word w} {f : Frame w r} {rows : List (List (TeamRAM.Event w))}
    {fs : List (Frame w r)} (hs : ChargedRows P pub lib H limit cap f rows fs) (fit : p ≤ 2^w)
    (bound : ∀ e ∈ rows.flatten, e.action.extra ≤ cap.val) :
    Team.ValidBlocks (fun e => e.action.extra) H.val rows ∧ Chain (Model.wordFetch P pub lib) limit f rows fs := by
  induction rows generalizing f fs with
  | nil => exact ⟨trivial, hs⟩
  | cons es rest ih =>
    cases fs with
    | nil => exact False.elim hs
    | cons next tail =>
      have bb (e) (he : e ∈ rest.flatten) := bound e (List.mem_append_right es he)
      obtain ⟨hmax,hnext⟩ := hs.1.spec hs.2 fit bb
      obtain ⟨hblocks,hchain⟩ := ih hs.2 bb
      exact ⟨⟨hmax,hblocks⟩,hnext,hchain⟩

private theorem exists_rows (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (H limit cap : Word w)
    (s : TeamOpcode.State w p r) (elapsed : Word w) (input : Frame w r)
    (hin : input = .live (packed w s.pc.val) s.reg elapsed ∨ (P.fetch pub lib s = .accept ∧ input = .accepted elapsed))
    (rows : List (List (TeamRAM.Event w))) (path : TeamRAM.Local (P.fetch pub lib) s rows.flatten)
    (bounds : ∀ e ∈ rows.flatten, e.action.extra ≤ cap.val) (time : elapsed.val + cost rows.flatten ≤ limit.val)
    (greedy : Team.ValidBlocks (fun e => e.action.extra) H.val rows) :
    ∃ fs, ChargedRows P pub lib H limit cap input rows fs := by
  induction rows generalizing s elapsed input with
  | nil => exact ⟨[],rfl⟩
  | cons es rest ih =>
    change elapsed.val + cost (es ++ rest.flatten) ≤ limit.val at time
    rw [show cost (es ++ rest.flatten) = cost es + cost rest.flatten from RAMBuckets.cost_append ..] at time
    have ht : elapsed ≤ limit := show elapsed.val ≤ limit.val by omega
    have bb (e) (he : e ∈ rest.flatten) := bounds e (List.mem_append_right es he)
    rcases hin with rfl | ⟨ha,rfl⟩
    · let c := blockWindow H limit elapsed cap
      have hc := blockWindow_total H limit elapsed cap ht
      have safe := blockWindow_safe H limit elapsed cap ht
      obtain ⟨z,fin,run,valid⟩ := chunk_of_prefix (c := c) path
        (fun e he => bounds e (List.mem_append_left _ he)) greedy.1.1
        (by change cost es ≤ (packed w (limit.val-elapsed.val)).val; rw [packed_val (lt_of_le_of_lt (Nat.sub_le _ _) limit.isLt)]; omega) safe
      obtain ⟨_,_,_,_,_,clock,capEq⟩ := run.clock safe
      have localBurst (e) (he : e ∈ rest.flatten) : e.action.extra ≤ fin.cap.val := capEq ▸ bb e he
      have finish := (run.close_iff_maximal valid safe localBurst).mpr greedy.1
      let next := Finish.frame (chunkMode rest.flatten z) z.reg fin.elapsed
      have hrow : ChargedRow P pub lib H limit cap (.live (packed w s.pc.val) s.reg elapsed) es rest.flatten next :=
        ⟨ht,s.pc,z,fin,rfl,run,finish,rfl⟩
      have cont : next = .live (packed w z.pc.val) z.reg fin.elapsed ∨
          (P.fetch pub lib z = .accept ∧ next = .accepted fin.elapsed) := by
        cases hh : rest.flatten with
        | nil => exact Or.inr ⟨by rw [hh] at valid; exact valid, by simp [next, chunkMode, hh, Finish.frame]⟩
        | cons => exact Or.inl (by simp [next, chunkMode, hh, Finish.frame])
      obtain ⟨fs,hfs⟩ := ih z fin.elapsed next cont valid bb
        (by rw [clock]; change elapsed.val + cost es + cost rest.flatten ≤ limit.val; omega) greedy.2
      exact ⟨next::fs,hrow,hfs⟩
    · have empty : es ++ rest.flatten = [] := by
        cases he : es ++ rest.flatten with
        | nil => rfl
        | cons e xs =>
          change TeamRAM.Local (P.fetch pub lib) s (es ++ rest.flatten) at path
          rw [he] at path
          have h := path.1
          simp [ha, TeamRAM.Instr.action] at h
      obtain ⟨rfl,htail⟩ := List.append_eq_nil_iff.mp empty
      have cont : TeamRAM.Local (P.fetch pub lib) s rest.flatten := by rw [htail]; exact ha
      obtain ⟨fs,hfs⟩ := ih s elapsed (.accepted elapsed) (Or.inr ⟨ha,rfl⟩) cont bb
        (by simpa only [htail, cost, RAMBuckets.cost, Nat.add_zero] using (show elapsed.val ≤ limit.val from ht)) greedy.2
      exact ⟨.accepted elapsed::fs,⟨rfl,ht,rfl⟩,hfs⟩

/-- For any locally accepting, burst- and time-bounded complete path, every proposed
partition and proposed list of frames are accepted by the finite-PC charged rows exactly
when the partition is greedy and the full-word chain accepts those same frames. -/
theorem chargedRows_iff (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : TeamOpcode.Macros w a) (H limit cap : Word w) (fit : p ≤ 2^w)
    (s : TeamOpcode.State w p r) (rows : List (List (TeamRAM.Event w))) (fs : List (Frame w r))
    (path : TeamRAM.Local (P.fetch pub lib) s rows.flatten) (bounds : ∀ e ∈ rows.flatten, e.action.extra ≤ cap.val)
    (time : cost rows.flatten ≤ limit.val) :
    ChargedRows P pub lib H limit cap (initial (packed w s.pc.val) s.reg) rows fs ↔
      Team.ValidBlocks (fun e => e.action.extra) H.val rows ∧
      Chain (Model.wordFetch P pub lib) limit (initial (packed w s.pc.val) s.reg) rows fs := by
  refine ⟨fun h => h.spec fit bounds, ?_⟩
  rintro ⟨hg,hc⟩
  obtain ⟨fs',hs⟩ := exists_rows P pub lib H limit cap s 0 _ (Or.inl rfl) rows path bounds (by simpa using time) hg
  obtain rfl := chain_unique _ _ (hs.spec fit bounds).2 hc
  exact hs

end TeamSite

end BorderVNP
end Computability
end OAI
