import OAI.Computability.VPVNP.CompressorRefreshStageFrame

/-! # Read and write bounds for native report lists

The bounds compose when report lists are concatenated. A scan that writes
one cell at each ordinal accesses exactly its addressed column.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM SourceTransport
open scoped Fin.CommRing

variable {w : ℕ}

/-- Bounds on every address actually read or written, including repeated
writes to cells whose eventual values agree with the input. -/
abbrev LogAccess (rd wr : ℕ → Prop) (rs : List (Report w)) :=
  Reads rd (eventLog rs) ∧ Writes wr (eventLog rs)

theorem LogAccess.append {rd wr : ℕ → Prop} {rs ts : List (Report w)}
    (r : LogAccess rd wr rs) (t : LogAccess rd wr ts) : LogAccess rd wr (rs++ts) := by
  simp only [LogAccess,eventLog,List.flatMap_append]
  exact ⟨fun a v ha ↦ (List.mem_append.mp ha).elim (r.1 a v) (t.1 a v),
    fun a v ha ↦ (List.mem_append.mp ha).elim (r.2 a v) (t.2 a v)⟩

theorem LogAccess.mono {rd wr rd' wr' : ℕ → Prop} {rs : List (Report w)}
    (r : LogAccess rd wr rs) (reads : ∀ x, rd x → rd' x) (writes : ∀ x, wr x → wr' x) :
    LogAccess rd' wr' rs := ⟨fun a v h ↦ reads _ (r.1 a v h), fun a v h ↦ writes _ (r.2 a v h)⟩

/-- Event trace of one direct external write surrounded by specified numbers of tick events. -/
def directEvents (before ticks : ℕ) (addr v : Word w) : List (Event w) :=
  List.replicate before .tick ++ [.write addr v] ++ List.replicate ticks .tick

theorem direct_events (before ticks : ℕ) (a v : Word w) (wr : ℕ → Prop) (ha : wr a.val) :
    Reads (fun _ ↦ False) (directEvents before ticks a v) ∧ Writes wr (directEvents before ticks a v) := by
  constructor
  · intro q z hz; simp [directEvents] at hz
  · intro q z hz; simpa [directEvents] using (show wr q.val from by
      simp [directEvents] at hz
      exact hz.1 ▸ ha)

private theorem addr_val (base i : ℕ) (fit : base+i < 2^w) :
    ((base : Word w)+(i : Word w)).val = base+i := by
  rw [← Nat.cast_add]
  exact Nat.mod_eq_of_lt fit

/-- One external write per ordinal, with a fixed number of ticks on each side. -/
theorem direct_scan {Q : Type*} (P : BurstRAM.Program w Q) (fuel before ticks base n : ℕ)
    (value : Word w → Word w) (fit : base+n ≤ 2^w)
    (native : ∀ (m : Memory w) (i : Word w), execute P fuel (P.start i) m [] =
      some ⟨directEvents before ticks ((base : Word w)+i) (value i),some (i+1)⟩)
    (m : Memory w) (rs : List (Report w)) (hr : runSegment P fuel (some 0) m (List.replicate n []) = some rs) :
    LogAccess (fun _ ↦ False) (fun x ↦ base ≤ x ∧ x < base+n) rs := by
  let ev := fun (_ : Memory w) i ↦ directEvents before ticks ((base : Word w)+i) (value i)
  refine (StageFrame.scan P fuel 0 n (fun _ _ ↦ True) ev _ _ (fun _ _ _ m ↦ native m _) ?_
    (Nat.zero_le _) m rs trivial (by simpa only [Nat.sub_zero,Nat.cast_zero] using hr)).2.2
  intro j _ hj _ _
  refine ⟨trivial, direct_events before ticks _ _ _ ?_⟩
  rw [addr_val base j (by omega)]
  omega

end CompressorRecords

end VPVNP
end Computability
end OAI
