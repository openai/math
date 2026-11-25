import OAI.Computability.BorderVNP.RoutingISATableIntervalPass
import Mathlib.Data.Nat.Choose.Basic

/-! # Shared routing intervals for distinct symbol groups

Each unordered distinct pair of symbols gets one descriptor, with a separate
ordered address at each endpoint. The two addresses remain distinct when
both groups belong to the same team. Previously emitted data rows stay at
the beginning of the same seven-word buffer.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.SharedRows

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Layout supplied by the public declaration, group-assignment and data passes. -/
structure Layout where
  /-- Common frame address. -/
  frame : ℕ
  /-- Alphabet size at the chosen coordinate. -/
  groups : ℕ
  /-- Number of cube coordinates. -/
  axes : ℕ
  /-- The chosen coordinate. -/
  axis : ℕ
  /-- Header of the declaration block. -/
  header : ℕ
  /-- Address of the declared crossing widths. -/
  lengths : ℕ
  /-- Fixed selector width of each distinct group pair. -/
  selectors : ℕ
  /-- Address of the symbol-to-team array. -/
  owners : ℕ
  /-- Base of the ordered endpoint buffers. -/
  banks : ℕ
  /-- Fixed spacing between successive endpoint buffers. -/
  stride : ℕ
  /-- The seven-word transmission array. -/
  records : ℕ
  /-- Count of data records at the beginning of the array. -/
  dataCount : ℕ

/-- Public, ordered endpoint view of the shared list. -/
def Layout.view (l : Layout) (s t : ℕ) := l.banks + l.stride*(s*l.groups+t)

/-- The crossing width read from the declared row at the chosen coordinate. -/
def Layout.crossWidth (l : Layout) (m : ℕ → ℕ) (s t : ℕ) :=
  m (l.lengths+(s*l.groups+t)*l.axes+l.axis)

/-- All seven words in the actual shared record. Its kind and source-base fields are zero. -/
def Layout.row (l : Layout) (m : ℕ → ℕ) (s t : ℕ) : Fin 7 → ℕ :=
  ![0,m (l.owners+s),m (l.owners+t),l.selectors+l.crossWidth m s t,0,l.view s t,l.view t s]

/-- Count of completed rows before visiting ordered inner index `s` in outer group `t`. -/
def Layout.rowIndex (l : Layout) (s t : ℕ) := l.dataCount + t.choose 2 + s

/-- Base word address of an output record. -/
def Layout.address (l : Layout) (i : ℕ) := l.records+7*i

/-- Seven actual scalar word stores for a descriptor. -/
def writeRow (m : ℕ → ℕ) (a : ℕ) (f : Fin 7 → ℕ) : ℕ → ℕ :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update m a (f 0)) (a+1) (f 1)) (a+2) (f 2)) (a+3) (f 3))
    (a+4) (f 4)) (a+5) (f 5)) (a+6) (f 6)

/-- Read back any of the seven words after the native store sequence. -/
theorem writeRow_inside (m : ℕ → ℕ) (a : ℕ) (f : Fin 7 → ℕ) (j : Fin 7) :
    writeRow m a f (a+j.val) = f j := by
  fin_cases j <;> simp [writeRow]

/-- The store sequence changes no memory outside its single output record. -/
theorem writeRow_outside (m : ℕ → ℕ) (a : ℕ) (f : Fin 7 → ℕ) (x : ℕ) (h : x < a ∨ a+7 ≤ x) :
    writeRow m a f x = m x := by
  unfold writeRow
  repeat rw [Function.update_of_ne (by omega)]

/-- Persistent frame registers throughout emission. -/
def Layout.regValue (l : Layout) : ℕ → ℕ
  | 0 => 0 | 1 => 1 | 2 => 7 | 3 => l.groups | 4 => l.axes | 5 => l.axis | 6 => l.owners
  | 7 => l.lengths | 8 => l.selectors | 9 => l.banks | 10 => l.stride | 11 => l.records
  | 12 => l.dataCount | _ => 0

/-- Public setup fields are resident in registers zero through twelve. -/
def Layout.Ready (l : Layout) (z : NatState) : Prop :=
  ∀ j : Reg, j.val ≤ 12 → z.reg j = l.regValue j.val

/-- Scratch-only row operations preserve the loaded frame. -/
theorem Layout.Ready.fixed {l : Layout} {z : NatState} (h : l.Ready z)
    {c : Code} (hc : c.protects 13 = true) (pub : Arg → ℕ) : l.Ready (c.fixedEval pub z) :=
  fun j hj => (c.fixedEval_protected pub z hc j (by omega)).trans (h j hj)

/-- Square addresses and the extent of the compact descriptor array fit the word size.
Input words are outside the output region. The view stride covers every declared list. -/
structure Layout.Fits (l : Layout) (w : ℕ) (before : ℕ → ℕ) : Prop where
  /-- Frame and the secondary declaration header are addressable. -/
  headers : l.frame+86 < 2^w ∧ l.header+6 < 2^w
  /-- Group count fits the outer loop counter. -/
  groupFit : l.groups < 2^w
  /-- The chosen axis is a legal coordinate. -/
  axisFit : l.axis < l.axes
  /-- Numeric pair indices fit. -/
  square : l.groups^2 < 2^w
  /-- The entire declared width matrix is addressable. -/
  lengthsFit : l.lengths+l.groups^2*l.axes ≤ 2^w
  /-- The group-owner map is addressable. -/
  ownersFit : l.owners+l.groups ≤ 2^w
  /-- The width of one shared list fits and does not exceed its reserved stride. -/
  widthFit : ∀ t < l.groups, ∀ s < t, l.selectors + l.crossWidth before s t ≤ l.stride
  /-- Each possible ordered endpoint buffer is addressable. -/
  viewsFit : l.banks+l.stride*l.groups^2 ≤ 2^w
  /-- Output record count and byte extent. -/
  countFit : l.dataCount+l.groups.choose 2 < 2^w
  /-- Seven consecutive words are reserved for every data and shared row. -/
  recordsFit : l.address (l.dataCount+l.groups.choose 2) ≤ 2^w
  /-- All width, owner and frame words needed during emission are outside the output records. -/
  separate : ∀ t < l.groups, ∀ s < t, ∀ x ∈ [l.owners+s,l.owners+t,l.lengths+(s*l.groups+t)*l.axes+l.axis,l.frame+13],
    x < l.address l.dataCount ∨ l.address (l.dataCount+l.groups.choose 2) ≤ x

/-- Every completed output row is correct and addresses outside the completed prefix
retain their original values, including the input data records. -/
structure Layout.Image (l : Layout) (before : ℕ → ℕ) (next : ℕ) (mem : ℕ → ℕ) : Prop where
  /-- The seven actual fields of each completed pair. -/
  rows : ∀ t < l.groups, ∀ s < t, l.rowIndex s t < next → ∀ j : Fin 7,
    mem (l.address (l.rowIndex s t)+j.val) = l.row before s t j
  /-- All words outside the completed interval. -/
  outside : ∀ x, x < l.address l.dataCount ∨ l.address next ≤ x → mem x = before x

/-- Triangular numbering reserves precisely the distinct symbol pairs before each outer group. -/
theorem choose_succ_two (t : ℕ) : (t+1).choose 2 = t.choose 2 + t := by
  rw [Nat.choose_succ_succ, Nat.choose_one_right, Nat.add_comm]

/-- Distinct oriented pairs occupy distinct compact descriptor indices. -/
theorem Layout.rowIndex_inj {l : Layout} {s t s' t' : ℕ} (hs : s < t) (hs' : s' < t')
    (he : l.rowIndex s t = l.rowIndex s' t') : s = s' ∧ t = t' := by
  dsimp [rowIndex] at he
  have ht : t = t' := by
    rcases lt_trichotomy t t' with h | h | h
    · have hh := Nat.choose_le_choose 2 h
      rw [choose_succ_two] at hh
      omega
    · exact h
    · have hh := Nat.choose_le_choose 2 h
      rw [choose_succ_two] at hh
      omega
  subst t'
  exact ⟨by omega,rfl⟩

/-- Completed rows and outside words remain exact after emitting the next pair. -/
theorem Layout.Image.step {l : Layout} {before mem : ℕ → ℕ} {s t : ℕ} (ht : t < l.groups) (hs : s < t)
    (h : l.Image before (l.rowIndex s t) mem) :
    l.Image before (l.rowIndex s t+1) (writeRow mem (l.address (l.rowIndex s t)) (l.row before s t)) := by
  constructor
  · intro t' _ s' hs' hnext j
    by_cases he : l.rowIndex s' t' = l.rowIndex s t
    · obtain ⟨rfl,rfl⟩ := l.rowIndex_inj hs' hs he
      exact writeRow_inside ..
    · rw [writeRow_outside]
      · exact h.rows t' (by assumption) s' hs' (by omega) j
      · left
        dsimp [Layout.address]
        have := j.isLt
        omega
  · intro x hx
    have hge : l.dataCount ≤ l.rowIndex s t := by dsimp [Layout.rowIndex]; omega
    rw [writeRow_outside]
    · apply h.outside
      dsimp [Layout.address] at *
      omega
    · dsimp [Layout.address] at *
      omega

end Cube.SharedRows

end BorderVNP
end Computability
end OAI
