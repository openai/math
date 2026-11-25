import OAI.Computability.BorderVNP.RoutingISATableBounds

/-! # Reading the scheduled partner length with unsigned word instructions

The two conditional decrements count the omitted endpoints below the relay.
The quotient counts the residue positions of that relay among the pair's
transmissions. The division branch runs only when its numerator is nonnegative.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- A syntactic check that a named register is not written by a read-only fragment. -/
def Code.leaves (j : Reg) : Code → Bool
  | .constant d _ | .publicWord d _ | .copy d _ | .binary _ d _ _ | .load d _ => decide (j ≠ d)
  | .seq a b | .ifLt _ _ a b | .ifEq _ _ a b => a.leaves j && b.leaves j
  | _ => true

/-- Natural evaluation preserves every syntactically untouched register. -/
theorem Code.evalNat_leaves (c : Code) (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (j : Reg) (h : c.leaves j = true) : c.evalNat pub mem s j = s j := by
  induction c generalizing s with
  | seq a b ih₁ ih₂ =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    exact (ih₂ _ hb).trans (ih₁ _ ha)
  | ifLt x y a b ih₁ ih₂ | ifEq x y a b ih₁ ih₂ =>
    obtain ⟨ha,hb⟩ := Bool.and_eq_true_iff.mp h
    simp only [Code.evalNat]
    split
    · exact ih₁ _ ha
    · exact ih₂ _ hb
  | constant d _ | publicWord d _ | copy d _ | binary _ d _ _ | load d _ =>
    exact Function.update_of_ne (of_decide_eq_true h) ..
  | _ => rfl

/-- The word-level rank obtained by the two conditional decrements. -/
private def rankWord (a b v : ℕ) : ℕ :=
  let z := if a < v then v-1 else v
  if b < v then z-1 else z

private theorem rankWord_eq {a b v : ℕ} (hab : a < b) :
    rankWord a b v = Routing.unskip a (Routing.unskip b v) := by
  simp only [rankWord, Routing.unskip]
  split_ifs <;> omega

private def quotientWord : Code := .block [
  .binary .sub 28 18 1, .binary .sub 28 28 29, .binary .div 28 28 5, .binary .add 28 28 1]

private def rankTail : Code := .block [
  .copy 29 22, .ifLt 26 22 (.binary .sub 29 29 1) .nop,
  .ifLt 27 22 (.binary .sub 29 29 1) .nop, .ifLt 29 18 quotientWord .nop]

private theorem rankTail_spec {w : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (a b v W period : ℕ) (hab : a < b) (hper : 0 < period) (hW : W < 2^w)
    (h1 : s 1 = 1) (h5 : s 5 = period) (h18 : s 18 = W) (h22 : s 22 = v)
    (h26 : s 26 = a) (h27 : s 27 = b) (h28 : s 28 = 0) :
    rankTail.safeReadOnly w pub mem s ∧
      rankTail.evalNat pub mem s 28 = Routing.strideCount period (rankWord a b v) W := by
  have bound (k : ℕ) (hk : k < W) : (W-1-k)/period+1 < 2^w := by
    have := Nat.div_le_self (W-1-k) period
    omega
  by_cases h₁ : a < v <;> by_cases h₂ : b < v <;> by_cases h₃ : rankWord a b v < W
  all_goals
    simp only [rankWord,h₁,h₂,↓reduceIte] at h₃
    simp (config := {decide := true}) [rankTail, quotientWord, Code.block, Code.evalNat,
      Code.safeReadOnly, addressOp, addressOpFits, Routing.strideCount, rankWord,
      h1,h5,h18,h22,h26,h27,h28,h₁,h₂,h₃,not_le_of_gt,hper, bound] <;> omega

private def sortedLength : Code := .block [
  orderPair 21 23 26 27, pairAddress 19 26 27 3 8, .load 18 19, rankTail]

private theorem sorted_spec {w : ℕ} (pub : Arg → ℕ) (mem : ℕ → ℕ) (s : Reg → ℕ)
    (R base u v j W : ℕ) (hR : 2 < R) (hu : u ≠ j)
    (haddr : min u j*R+max u j+base < 2^w) (hW : W < 2^w)
    (hread : mem (min u j*R+max u j+base) = W)
    (h1 : s 1 = 1) (h3 : s 3 = R) (h5 : s 5 = R-2) (h8 : s 8 = base)
    (h21 : s 21 = u) (h22 : s 22 = v) (h23 : s 23 = j) (h28 : s 28 = 0) :
    sortedLength.safeReadOnly w pub mem s ∧ sortedLength.evalNat pub mem s 28 =
      Routing.strideCount (R-2) (rankWord (min u j) (max u j) v) W := by
  let a := min u j
  let b := max u j
  let o := (orderPair 21 23 26 27).evalNat pub mem s
  let p := (pairAddress 19 26 27 3 8).evalNat pub mem o
  let t := Function.update p (18 : Reg) (mem (p 19))
  have ho : o = Function.update (Function.update s 26 a) 27 b := by
    rcases lt_or_gt_of_ne hu with hij | hji
    · simp (config := {decide := true}) [o,a,b,orderPair,Code.evalNat,Code.block,h21,h23,hij,
        min_eq_left hij.le,max_eq_right hij.le]
    · simp (config := {decide := true}) [o,a,b,orderPair,Code.evalNat,Code.block,h21,h23,hji.not_gt,
        min_eq_right hji.le,max_eq_left hji.le]
  have hp : p = Function.update o 19 (a*R+b+base) := by
    simp (config := {decide := true}) [p,pairAddress,Code.block,Code.evalNat,addressOp,ho,h3,h8]
  have ht : t = Function.update p 18 W := by
    simp [t,hp,a,b,hread]
  have hab : a < b := by dsimp [a,b]; omega
  have tail := rankTail_spec pub mem t a b v W (R-2) hab (by omega) hW
    (by simp (config := {decide := true}) [ht,hp,ho,h1])
    (by simp (config := {decide := true}) [ht,hp,ho,h5])
    (by simp [ht])
    (by simp (config := {decide := true}) [ht,hp,ho,h22])
    (by simp (config := {decide := true}) [ht,hp,ho])
    (by simp (config := {decide := true}) [ht,hp,ho])
    (by simp (config := {decide := true}) [ht,hp,ho,h28])
  constructor
  · change (orderPair 21 23 26 27).safeReadOnly w pub mem s ∧
      (pairAddress 19 26 27 3 8).safeReadOnly w pub mem o ∧ True ∧ rankTail.safeReadOnly w pub mem t
    refine ⟨?_,?_, trivial,tail.1⟩
    · simp [orderPair,Code.block,Code.safeReadOnly]
    · simp (config := {decide := true}) [pairAddress, Code.block, Code.safeReadOnly, Code.evalNat,
        addressOpFits,addressOp,ho,h3,h8,a,b]
      omega
  · exact tail.2

/-- The scheduled length fragment is safe and reads exactly the partner's scheduled length. -/
theorem scheduledLengthWord_spec {w : ℕ} {l : TableLayout} (row : ℕ → TableRow)
    (pub : Arg → ℕ) (s : NatState) (al : l.Allocated w) (fit : l.RowsFit w row)
    (hr : l.ready s) {u v j : ℕ} (hu : u < l.teams) (hv : v < l.teams) (hj : j < l.teams)
    (h21 : s.reg 21 = u) (h22 : s.reg 22 = v) (h23 : s.reg 23 = j)
    (hw : ∀ i < l.teams^2, s.mem (l.widths+i) = l.pairWidth row l.count i) :
    scheduledLengthWord.safeReadOnly w pub s.mem s.reg ∧
      scheduledLengthWord.evalNat pub s.mem s.reg 28 = l.partnerLength row u v j := by
  let t := Function.update s.reg (28 : Reg) (s.reg 0)
  have h0 : s.reg 0 = 0 := hr 0 (by decide)
  have regs (i : Reg) (hi : i ≠ 28) : t i = s.reg i := Function.update_of_ne hi ..
  have h21' := (regs 21 (by decide)).trans h21
  have h22' := (regs 22 (by decide)).trans h22
  have h23' := (regs 23 (by decide)).trans h23
  have h28' : t 28 = 0 := (Function.update_self ..).trans h0
  have he : l.partnerLength row u v j =
      if u ≠ j ∧ v ≠ u ∧ v ≠ j then
        Routing.strideCount (l.teams-2) (Routing.unskip (min u j) (Routing.unskip (max u j) v))
          (l.pairWidth row l.count (l.pairKey u j)) else 0 := by
    simp only [TableLayout.partnerLength, hu,hv,hj,true_and,↓reduceDIte,Routing.scheduledLength_formula,
      ne_eq, Fin.mk.injEq, Fin.coe_min, Fin.coe_max]
  let guard := Code.ifEq 21 22 .nop (.ifEq 21 23 .nop (.ifEq 22 23 .nop sortedLength))
  change (True ∧ guard.safeReadOnly w pub s.mem t) ∧ guard.evalNat pub s.mem t 28 = _
  rw [he]
  by_cases h₁ : u = v
  · simp [guard,Code.safeReadOnly,Code.evalNat,h21',h22',h₁,h28']
  by_cases h₂ : u = j
  · simp [guard,Code.safeReadOnly,Code.evalNat,h21',h22',h23',h₂,h28']
  by_cases h₃ : v = j
  · simp [guard,Code.safeReadOnly,Code.evalNat,h21',h22',h23',h₂,h₃,h28']
  have hread := hw _ (l.pairKey_lt hu hj)
  have Wfit := (l.pairWidth_le_sum row (i := l.count) le_rfl (l.pairKey u j)).trans_lt fit.widths
  have addr := al.address (l.contains_offset (a := .widths) (l.pairKey_lt hu hj))
  have hs := sorted_spec pub s.mem t l.teams l.widths u v j _ al.teamCount h₂
    (by simpa [TableLayout.base,TableLayout.pairKey,Nat.add_comm l.widths] using addr) Wfit
    (by simpa [TableLayout.pairKey,Nat.add_comm l.widths] using hread)
    ((regs 1 (by decide)).trans (hr 1 (by decide))) ((regs 3 (by decide)).trans (hr 3 (by decide)))
    ((regs 5 (by decide)).trans (hr 5 (by decide))) ((regs 8 (by decide)).trans (hr 8 (by decide)))
    h21' h22' h23' h28'
  rw [ite_eq_left (show u ≠ j ∧ v ≠ u ∧ v ≠ j from ⟨h₂,Ne.symm h₁,h₃⟩)]
  simpa only [guard,Code.safeReadOnly,Code.evalNat,h21',h22',h23',h₁,h₂,h₃,↓reduceIte,
    true_and, rankWord_eq (show min u j < max u j by omega)] using hs

/-- Actual native scheduled-length execution, preserving the physical memory and every
register outside the instruction fragment's scratch destinations. -/
theorem scheduledLengthWord_run {w : ℕ} (l : TableLayout) (row : ℕ → TableRow)
    (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (al : l.Allocated w) (fit : l.RowsFit w row) (hr : l.ready (.ofWords s m))
    {u v j : ℕ} (hu : u < l.teams) (hv : v < l.teams) (hj : j < l.teams)
    (h21 : readings s 21 = u) (h22 : readings s 22 = v) (h23 : readings s 23 = j)
    (hw : ∀ i < l.teams^2, readings m (l.widths+i) = l.pairWidth row l.count i) :
    ∃ es t, Runs pub macros scheduledLengthWord s m es t m ∧ traceCost es ≤ scheduledLengthWord.slots ∧
      l.ready (.ofWords t m) ∧ readings t 28 = l.partnerLength row u v j ∧
      ∀ i : Reg, scheduledLengthWord.leaves i = true → readings t i = readings s i := by
  obtain ⟨safe, eval⟩ := scheduledLengthWord_spec row (readings pub) (.ofWords s m) al fit hr
    hu hv hj h21 h22 h23 hw
  obtain ⟨es,t,r,cost,he⟩ := scheduledLengthWord.runReadOnly (w := w) pub macros m s safe
  refine ⟨es,t,r,cost,?_,(congrFun he 28).trans eval,fun i hi => (congrFun he i).trans
    (scheduledLengthWord.evalNat_leaves _ _ _ i hi)⟩
  intro i hi
  exact (congrFun he i).trans ((scheduledLengthWord.evalNat_protected _ _ _
    (lo := 13) (by decide) i (by omega)).trans (hr i hi))

end RoutingISA

end BorderVNP
end Computability
end OAI
