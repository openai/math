import OAI.Optimization.LinearProgramming.RAM.FrameClear

/-! Initialize the even-indexed address registers of an isolated feasibility call.
The caller keeps its dimensions in odd registers 9 and 11. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace RAM
namespace Call

open Block Tape

/-- Double a saved dimension using address-register copies, increments and counted branches. -/
def doubleHeaderEntry (dst src : Nat) : Block :=
  .seq (.op (.addrCopy dst src)) (.forRange 5 src (.op (.incr dst dst)))

/-- Odd registers 3, 5 and 7 supply zero, the clearing length and the clearing pointer.
The loop counter at 5 is reused by both dimension writes. -/
def callHeader : Block :=
  .seq (clearWindow false) (.seq (doubleHeaderEntry 0 9) (doubleHeaderEntry 2 11))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem doubleHeaderEntry_run (s : Memory K) (dst src : Nat) (hs : Good P s)
    (hd : dst ≠ 5) (hs5 : src ≠ 5) (hsd : src ≠ dst) :
    ∃ t, Eval (Good P) (doubleHeaderEntry dst src) s (4*s.index src+3) t ∧
      t.index dst = 2*s.index src ∧ t.index 5 = s.index src ∧
      (∀ i, i ≠ 5 → i ≠ dst → t.index i = s.index i) ∧ t.data = s.data := by
  let n := s.index src
  let a := s.putIndex dst n
  let I (j : Nat) (m : Memory K) := m.data = s.data ∧ m.index dst = n+j ∧ m.index 5 = j ∧
    ∀ i, i ≠ 5 → i ≠ dst → m.index i = s.index i
  have start : I 0 (a.putIndex 5 0) := by
    refine ⟨rfl, ?_, by simp, ?_⟩
    · simp [a, hd]
    · intro i hi hdst
      simp [a,hi,hdst]
  obtain ⟨t, run, endstate⟩ := Eval.forRange_invariant_exact
    (safe := Good P) (body := .op (.incr dst dst)) 5 src n 1 I a hs start
    (fun _ m h => ⟨fun i => h.1 ▸ hs i, h.2.2.1, h.2.2.2 src hs5 hsd⟩)
    (fun j _ m h => by
      let u := m.putIndex dst (m.index dst+1)
      have hm : Good P m := fun i => h.1 ▸ hs i
      have heval : Eval (Good P) (.op (.incr dst dst)) m 1 u := Eval.op_incr m dst dst hm hm
      refine ⟨u, heval, h.1, ?_, ?_, ?_⟩
      · simp [u,hd,h.2.1,Nat.add_assoc]
      · simp [u,hd.symm,h.2.2.1]
      · intro i hi hdst
        simpa [u,hi,hdst] using h.2.2.2 i hi hdst)
  have cp : Eval (Good P) (.op (.addrCopy dst src)) s 1 a := Eval.op_addrCopy s dst src hs hs
  refine ⟨t, ?_, ?_, endstate.2.2.1, endstate.2.2.2, endstate.1⟩
  · have total := cp.seq run
    convert total using 1 <;> first | rfl | (dsimp [n]; omega)
  · rw [endstate.2.1, two_mul]

/-- Initialize the subroutine's whole virtual address bank. Beyond the supplied finite
window the incoming virtual addresses must already be zero. The scalar bank is identical,
and all odd address slots outside the counter and pointer keep their initial values. -/
theorem callHeader_correct (s : Memory K) (B m d : Nat) (input : List K)
    (hs : Good P s) (hzero : s.index 3 = 0) (hB : s.index 5 = B) (hp : s.index 7 = 0)
    (hm : s.index 9 = m) (hd : s.index 11 = d)
    (htail : ∀ j, B ≤ j → s.index (2*j) = 0) :
    ∃ t, Eval (Good P) callHeader s (6*B+4*m+4*d+7) t ∧ t.data = s.data ∧
      (∀ j, t.index (2*j) = 2*(RAM.start [m,d] input).index j) ∧
      (∀ i, i%2=1 → i≠5 → i≠7 → t.index i = s.index i) ∧
      t.index 5 = d ∧ t.index 7 = 2*B := by
  obtain ⟨c, clear, ptr, _, ci, cd⟩ := clearWindow_correct false s 0 B hs hzero
    (fun h => by contradiction) (by simpa using hp) hB
  have cdata : c.data = s.data := funext fun i => by simpa using cd i
  have odd (i : Nat) (hi : i%2=1) (h5 : i≠5) (h7 : i≠7) : c.index i = s.index i := by
    rw [ci i h5 h7]; simp [inEvenWindow, hi]
  have z (j : Nat) : c.index (2*j) = 0 := by
    rw [ci _ (by omega) (by omega)]
    by_cases hj : j < B
    · simp [inEvenWindow, hj]
    · simp [htail j (by omega)]
  have c9 : c.index 9 = m := (odd 9 (by decide) (by decide) (by decide)).trans hm
  obtain ⟨u, left, u0, _, ui, ud⟩ := doubleHeaderEntry_run c 0 9 clear.safe_end
    (by decide) (by decide) (by decide)
  have u11 : u.index 11 = d := (ui 11 (by decide) (by decide)).trans
    ((odd 11 (by decide) (by decide) (by decide)).trans hd)
  obtain ⟨t, right, t2, t5, ti, td⟩ := doubleHeaderEntry_run u 2 11 left.safe_end
    (by decide) (by decide) (by decide)
  refine ⟨t, ?_, td.trans (ud.trans cdata), ?_, ?_, t5.trans u11, ?_⟩
  · have h := clear.seq (left.seq right)
    rw [c9,u11] at h
    convert h using 1 <;> first | rfl | omega
  · intro j
    match j with
    | 0 => simpa [RAM.start, c9] using (ti 0 (by decide) (by decide)).trans u0
    | 1 => simpa [RAM.start, u11] using t2
    | j+2 =>
      rw [ti _ (by omega) (by omega), ui _ (by omega) (by omega), z]
      simp [RAM.start]
  · intro i hi h5 h7
    rw [ti i h5 (by omega), ui i h5 (by omega)]
    exact odd i hi h5 h7
  · rw [ti 7 (by decide) (by decide), ui 7 (by decide) (by decide)]
    simpa using ptr

end Call
end RAM
end LinearProgramming
end Optimization
end OAI
