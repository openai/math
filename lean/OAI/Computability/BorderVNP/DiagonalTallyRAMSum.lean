import OAI.Computability.BorderVNP.DiagonalTallyRAMCompare

/-! # Summing a column of team subtotals

The verified broadcast is team-major. The values for one fixed coordinate
therefore lie at a regular stride. This fixed table reads exactly those words and
accumulates their sum in a single register, leaving every input array untouched.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyRAM

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

/-- One probe of the current team subtotal. Advance by one row's width. -/
def sumOne : Code := .block [.load 54 48, .binary .add 52 52 54,
  .binary .add 48 48 49, .binary .add 51 51 63]

/-- The column loop. Registers 48–52 carry the pointer, stride, team limit,
current team, and sum. Register 63 holds one. -/
def sumColumn : Code := .whileLt 51 50 sumOne

/-- Word sum of a finite strided sequence, read from the actual memory. -/
def stridedSum (m : Memory w) (stride : ℕ) (ptr : ℕ) : ℕ → Word w
  | 0 => 0
  | n+1 => m ptr + stridedSum m stride (ptr+stride) n

/-- The strided scan visits each broadcast subtotal exactly once. -/
theorem stridedSum_eq (m : Memory w) (stride ptr n : ℕ) :
    stridedSum m stride ptr n = ∑ i : Fin n, m (ptr+stride*i.val) := by
  induction n generalizing ptr with
  | zero => simp [stridedSum]
  | succ n ih =>
    rw [stridedSum, Fin.sum_univ_succ, ih]
    simp only [Fin.val_zero, Nat.mul_zero, Nat.add_zero, Fin.val_succ]
    congr 1
    apply Finset.sum_congr rfl
    intro i _
    rw [Nat.mul_succ]
    congr 1
    omega

/-- The registers outside the loop's four scratch destinations survive it. -/
def ColumnFrame (s t : Bank w) : Prop :=
  ∀ j : Reg, j ≠ 48 → j ≠ 51 → j ≠ 52 → j ≠ 54 → t j = s j

private theorem sumOne_effect (s : Bank w) (m : Memory w) :
    let e := effect false s m sumOne
    e.bank 48 = s 48+s 49 ∧ e.bank 51 = s 51+s 63 ∧
    e.bank 52 = s 52+m (s 48).val ∧ ColumnFrame s e.bank ∧
    e.mem = m ∧ TraceOK e.trace [] 4 := by
  simp [sumOne, Code.block, effect, BinaryOp.eval, TraceOK, tick, ColumnFrame, Function.update]
  intro j ha hb hc hd
  simp [ha, hb, hc, hd]

/-- Native evaluation of a whole column. Its full trace has five ticks per
word and a final loop test. All accumulation takes place at word width. -/
theorem sumColumn_runs (len i ptr stride : ℕ) (s : Bank w) (m : Memory w)
    (hptr : ptr + stride*len < 2^w) (hidx : i+len < 2^w)
    (h48 : s 48 = word w ptr) (h49 : s 49 = word w stride)
    (h50 : s 50 = word w (i+len)) (h51 : s 51 = word w i) (h63 : s 63 = 1) :
    ∃ es t, Runs pub macros sumColumn s m es t m ∧ TraceOK es [] (5*len+1) ∧
      t 48 = word w (ptr+stride*len) ∧ t 51 = word w (i+len) ∧
      t 52 = s 52 + stridedSum m stride ptr len ∧ ColumnFrame s t := by
  induction len generalizing i ptr s with
  | zero =>
    refine ⟨_,_, .whileDone (by rw [h51,h50]; simp), ?_, ?_⟩
    · simp [TraceOK, tick]
    · simp [h48,h51,stridedSum,ColumnFrame]
  | succ len ih =>
    have hg : s 51 < s 50 := by
      change (s 51).val < (s 50).val
      rw [h51,h50,word_val _ _ (by omega),word_val _ _ hidx]; omega
    let e := effect false s m sumOne
    obtain ⟨hp,hj,hs,hframe,hm,ht⟩ := sumOne_effect s m
    have body := effect_runs pub macros false s m sumOne (by decide)
    change Runs pub macros sumOne s m e.trace e.bank e.mem at body
    change e.mem = m at hm
    rw [hm] at body
    have hp' : e.bank 48 = word w (ptr+stride) := by rw [hp,h48,h49,word_add]
    have hj' : e.bank 51 = word w (i+1) := by rw [hj,h51,h63,word_add,word_one]
    have h49' := (hframe 49 (by decide) (by decide) (by decide) (by decide)).trans h49
    have h50' := (hframe 50 (by decide) (by decide) (by decide) (by decide)).trans h50
    have h63' := (hframe 63 (by decide) (by decide) (by decide) (by decide)).trans h63
    have ptrEq : ptr+stride+stride*len = ptr+stride*(len+1) := by ring
    obtain ⟨fs,t,loop,ft,ep,ej,et,ef⟩ :=
      ih (i+1) (ptr+stride) e.bank (ptrEq ▸ hptr) (by omega) hp' h49'
        (by rw [h50']; congr 1; omega) hj' h63'
    refine ⟨_,_, .whileStep hg body loop, ?_, ep.trans (congrArg _ ptrEq), ?_, ?_, ?_⟩
    · rw [show 5*(len+1)+1 = (4+(5*len+1))+1 by omega]
      exact (ht.append ft).cons_tick
    · rw [ej]; congr 1; omega
    · rw [et, hs, h48, word_val _ _ (by omega), stridedSum, add_assoc]
    · intro j ha hb hc hd
      exact (ef j ha hb hc hd).trans (hframe j ha hb hc hd)

/-- Each valid column scan has at most one trace. -/
theorem sumColumn_unique {s t u : Bank w} {m mt mu : Memory w} {es fs}
    (a : Runs pub macros sumColumn s m es t mt) (b : Runs pub macros sumColumn s m fs u mu) :
    es = fs ∧ t = u ∧ mt = mu := a.unique_of_deterministic (by decide) b

end DiagonalTallyRAM

end BorderVNP
end Computability
end OAI
