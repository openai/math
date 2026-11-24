import OAI.Computability.VPVNP.ChoiceWitness

/-!
# Finite tape windows for the coefficient verifier

For a run of at most `r` steps, keep `2*r+1` cells of each tape centered at its
current head. A move shifts this array by one, reading a blank at the outside
edge. The cells with distance at most the remaining running time continue to
agree with the unbounded two-way tapes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace UniversalMachine

/-- A cell of the finite tape window of radius `r`, numbered from the left edge. -/
abbrev WindowCell (r : ℕ) := Fin (2 * r + 1)
/-- The symbol stored at each cell of a finite head-centered tape window. -/
abbrev WindowTape (r : ℕ) := WindowCell r → Symbol

/-- The cell scanned by the head in a radius-`r` window. -/
def windowCenter (r : ℕ) : WindowCell r := ⟨r, by omega⟩

/-- The old cell which moves into a given position after a head motion. -/
def shiftSource {r : ℕ} (move : Fin 3) (i : WindowCell r) : Option (WindowCell r) :=
  match move.val with
  | 0 => some i
  | 1 => if i.val = 0 then none else some ⟨i.val - 1, by have := i.isLt; omega⟩
  | _ => if h : i.val + 1 < 2 * r + 1 then some ⟨i.val + 1, h⟩ else none

/-- Write the head cell, then move the head and shift the whole window. -/
def windowUpdate {r : ℕ} (old : WindowTape r) (write move : Fin 3) (i : WindowCell r) : Symbol :=
  match shiftSource move i with
  | none => 0
  | some j => if j = windowCenter r then write else old j

/-- A machine configuration restricted to the two tape windows used by the bounded verifier. -/
structure WindowConfig (extra r : ℕ) where
  /-- Current running or halting state in the window simulation. -/
  state : Fin (extra + 2)
  /-- The head-centered window of the input tape. -/
  firstTape : WindowTape r
  /-- The head-centered window of the work tape. -/
  secondTape : WindowTape r

/-- State bits, followed by the symbol bits of the two finite tape windows. -/
abbrev WindowRegister (n r : ℕ) := Fin (n + 2) ⊕ (Bool × WindowCell r × Symbol)

/-- Boolean tests for the current state at each candidate state index and for each candidate
symbol at every represented cell of either tape. -/
def registerEncoding {n e r : ℕ} (c : WindowConfig e r) : WindowRegister n r → Bool
  | .inl q => decide (c.state.val = q.val)
  | .inr (false, i, s) => decide (c.firstTape i = s)
  | .inr (true, i, s) => decide (c.secondTape i = s)

/-- Look up the literal transition row using the current state and the symbols at both window
centers. -/
def windowBranches {r : ℕ} (p : Program) (c : WindowConfig p.extra r) : Branches p.extra :=
  p.rows[(c.state.val - 2) * 9 + (c.firstTape (windowCenter r)).val * 3 +
    (c.secondTape (windowCenter r)).val]?.getD .stop

/-- Select a branch using the path bit. A deterministic row accepts only the false choice bit. -/
def chosenInstruction {extra : ℕ} (row : Branches extra) (bit : Bool) :
    Option (Instruction extra) :=
  match row with
  | .stop => none
  | .one a => if bit then none else some a
  | .two a b => some (if bit then b else a)

/-- Select the next instruction of a running configuration from the literal table and path bit. -/
def windowInstruction {r : ℕ} (p : Program) (c : WindowConfig p.extra r) (bit : Bool) :
    Option (Instruction p.extra) :=
  if 2 ≤ c.state.val then chosenInstruction (windowBranches p c) bit else none

/-- Apply one instruction, updating the state and recentering both finite tape windows after
their head moves. -/
def windowAdvance {extra r : ℕ} (c : WindowConfig extra r) (a : Instruction extra) :
    WindowConfig extra r where
  state := a.target
  firstTape := windowUpdate c.firstTape a.firstSymbol a.firstMove
  secondTape := windowUpdate c.secondTape a.secondSymbol a.secondMove

/-- One deterministic step, including rejection of invalid choices and nonzero padding. -/
def windowStep {r : ℕ} (p : Program) (c : WindowConfig p.extra r) (bit : Bool) :
    WindowConfig p.extra r :=
  match windowInstruction p c bit with
  | some a => windowAdvance c a
  | none => { c with state := if c.state.val = 1 ∧ bit = false then 1 else 0 }

/-- Signed displacement of a window cell from the head. -/
def windowOffset {r : ℕ} (i : WindowCell r) : ℤ := (i.val : ℤ) - r

/-- Agreement on all cells reachable in the remaining `t` transitions. -/
def TapeAgrees {r : ℕ} (t : ℕ) (w : WindowTape r) (c : Turing.Tape Symbol) : Prop :=
  ∀ i, -(t : ℤ) ≤ windowOffset i → windowOffset i ≤ t → w i = c.nth (windowOffset i)

/-- The finite and unbounded configurations have the same state, and their two tapes agree at
every represented offset between minus t and t, inclusive. -/
structure WindowAgrees {extra r : ℕ} (t : ℕ) (w : WindowConfig extra r) (c : Config extra) :
    Prop where
  state : w.state = c.state
  first : TapeAgrees t w.firstTape c.firstTape
  second : TapeAgrees t w.secondTape c.secondTape

private theorem TapeAgrees.head {r t : ℕ} {w : WindowTape r} {c : Turing.Tape Symbol}
    (h : TapeAgrees t w c) : w (windowCenter r) = c.head := by
  simpa [windowOffset, windowCenter] using h (windowCenter r) (by simp [windowOffset, windowCenter])
    (by simp [windowOffset, windowCenter])

private theorem TapeAgrees.mono {r t : ℕ} {w : WindowTape r} {c : Turing.Tape Symbol}
    (h : TapeAgrees (t + 1) w c) : TapeAgrees t w c :=
  fun i hlo hhi => h i (by omega) (by omega)

private theorem shiftSource_inside {r t : ℕ} (hr : t + 1 ≤ r) (m : Fin 3) (i : WindowCell r)
    (hlo : -(t : ℤ) ≤ windowOffset i) (hhi : windowOffset i ≤ t) :
    ∃ j, shiftSource m i = some j ∧
      windowOffset j = windowOffset i + (if m.val = 0 then 0 else if m.val = 1 then -1 else 1) := by
  unfold windowOffset at *
  have hi := i.isLt
  rcases m with ⟨m, hm⟩
  match m with
  | 0 => exact ⟨i, rfl, by simp⟩
  | 1 =>
    have hpos : i.val ≠ 0 := by omega
    exact ⟨⟨i.val - 1, by omega⟩, by simp [shiftSource, hpos], by simp; omega⟩
  | m + 2 =>
    have hlt : i.val + 1 < 2 * r + 1 := by omega
    exact ⟨⟨i.val + 1, hlt⟩, by simp [shiftSource, hlt], by simp; omega⟩

private theorem windowBranches_eq {r t : ℕ} (p : Program) {w : WindowConfig p.extra r}
    {c : Config p.extra} (h : WindowAgrees t w c) : windowBranches p w = branches p c := by
  simp [windowBranches, branches, h.state, h.first.head, h.second.head]


private theorem updateTape_nth (c : Turing.Tape Symbol) (b m : Fin 3) (i : ℤ) :
    (updateTape c b m).nth i =
      (c.write b).nth (i + (if m.val = 0 then 0 else if m.val = 1 then -1 else 1)) := by
  rcases m with ⟨m, hm⟩
  match m with
  | 0 => simp [updateTape]
  | 1 => simp [updateTape, sub_eq_add_neg]
  | m + 2 => simp [updateTape]

private theorem TapeAgrees.update {r t : ℕ} {w : WindowTape r} {c : Turing.Tape Symbol}
    (h : TapeAgrees (t + 1) w c) (hr : t + 1 ≤ r) (b m : Fin 3) :
    TapeAgrees t (windowUpdate w b m) (updateTape c b m) := by
  intro i hlo hhi
  obtain ⟨j, hj, hoff⟩ := shiftSource_inside hr m i hlo hhi
  have hlo' : -(↑(t + 1 : ℕ) : ℤ) ≤ windowOffset j := by
    rw [hoff]
    split_ifs <;> omega
  have hhi' : windowOffset j ≤ (t + 1 : ℕ) := by
    rw [hoff]
    split_ifs <;> omega
  have hc : j = windowCenter r ↔ windowOffset j = 0 := by
    rw [Fin.ext_iff]
    simp only [windowCenter, windowOffset]
    omega
  rw [updateTape_nth, ← hoff, Turing.Tape.write_nth]
  simp only [windowUpdate, hj, hc, h j hlo' hhi']

private theorem WindowAgrees.advance {r t extra : ℕ}
    {w : WindowConfig extra r} {c : Config extra}
    (h : WindowAgrees (t + 1) w c) (hr : t + 1 ≤ r) (a : Instruction extra) :
    WindowAgrees t (windowAdvance w a) (advance c a) :=
  ⟨rfl, h.first.update hr _ _, h.second.update hr _ _⟩

/-- One tick preserves agreement on the portion of the tape reachable by future ticks. -/
theorem windowStep_agrees {r t : ℕ} (p : Program) {w : WindowConfig p.extra r}
    {c : Config p.extra} (h : WindowAgrees (t + 1) w c) (hr : t + 1 ≤ r) (bit : Bool) :
    WindowAgrees t (windowStep p w bit) (choiceStep p c bit) := by
  have hw := windowBranches_eq p h
  by_cases ha : c.state.val = 1
  · cases bit <;> simp [windowStep, windowInstruction, choiceStep, h.state, ha] <;>
      exact ⟨by apply Fin.ext; simp [reject, ha], h.first.mono, h.second.mono⟩
  by_cases hz : c.state.val = 0
  · simp [windowStep, windowInstruction, choiceStep, h.state, hz]
    exact ⟨by apply Fin.ext; simp [hz], h.first.mono, h.second.mono⟩
  have hrun : 2 ≤ c.state.val := by omega
  simp only [windowStep, windowInstruction, choiceStep, h.state, hw, hrun, ha, hz, ite_true,
    ite_false, false_and]
  cases hb : branches p c with
  | stop => exact ⟨rfl, h.first.mono, h.second.mono⟩
  | one a =>
    cases bit
    · exact h.advance hr a
    · exact ⟨rfl, h.first.mono, h.second.mono⟩
  | two a b => exact h.advance hr _

/-- Run the machine on a finite window, consuming one bit per step. -/
def windowRun {r : ℕ} (p : Program) (c : WindowConfig p.extra r) (bits : List Bool) :
    WindowConfig p.extra r :=
  bits.foldl (windowStep p) c

theorem windowRun_agrees {r : ℕ} (p : Program) (bits : List Bool) (hr : bits.length ≤ r)
    (w : WindowConfig p.extra r) (c : Config p.extra) (h : WindowAgrees bits.length w c) :
    WindowAgrees 0 (windowRun p w bits) (bits.foldl (choiceStep p) c) := by
  induction bits generalizing w c with
  | nil => exact h
  | cons b bs ih =>
    exact ih (by simp at hr; omega) _ _ (windowStep_agrees p h hr b)

/-- Load input bits on and to the right of the first tape head. -/
def windowInitial {n : ℕ} (p : Program) (r : ℕ) (x : Fin n → Bool) :
    WindowConfig p.extra r where
  state := if h : p.extra = 0 then ⟨1, by omega⟩ else ⟨2, by omega⟩
  firstTape := fun i =>
    if h : r ≤ i.val ∧ i.val - r < n then if x ⟨i.val - r, h.2⟩ then 2 else 1 else 0
  secondTape := fun _ => 0

private theorem tape_nth_mk₁ (xs : List Symbol) (i : ℤ) :
    (Turing.Tape.mk₁ xs).nth i = if 0 ≤ i then xs[i.toNat]?.getD 0 else 0 := by
  cases i with
  | ofNat k =>
    change (Turing.Tape.mk' (Turing.ListBlank.mk []) (Turing.ListBlank.mk xs)).nth (k : ℤ) = _
    simp [Turing.ListBlank.nth_mk]
    rw [← List.getD_default_eq_getI, List.getD_eq_getElem?_getD]
    rfl
  | negSucc k =>
    change (Turing.ListBlank.mk ([] : List Symbol)).nth k = _
    simp [Turing.ListBlank.nth_mk]

theorem windowInitial_agrees {n : ℕ} (p : Program) (r t : ℕ) (x : Fin n → Bool) :
    WindowAgrees t (windowInitial p r x) (initial p (List.ofFn x)) := by
  refine ⟨rfl, ?_, ?_⟩
  · intro i _ _
    change (if h : r ≤ i.val ∧ i.val - r < n then if x ⟨i.val - r, h.2⟩ then 2 else 1 else 0)
      = (Turing.Tape.mk₁ ((List.ofFn x).map fun b => if b then (2 : Symbol) else 1)).nth (windowOffset i)
    rw [tape_nth_mk₁]
    have hto : (windowOffset i).toNat = i.val - r := by unfold windowOffset; omega
    have hnonneg : 0 ≤ windowOffset i ↔ r ≤ i.val := by unfold windowOffset; omega
    simp only [hto, hnonneg]
    by_cases hlo : r ≤ i.val
    · by_cases hhi : i.val - r < n
      · simp [hlo, hhi]
      · simp [hlo, hhi]
    · simp [hlo]
  · intro i _ _
    change 0 = (Turing.Tape.mk₁ []).nth (windowOffset i)
    simp [tape_nth_mk₁]

/-- The bounded register machine computes the canonical witness predicate for the actual
two-way-tape program, including both halting states and all branch counts. -/
theorem windowRun_acceptsChoices {n : ℕ} (p : Program) (t r : ℕ) (ht : t ≤ r)
    (x : Fin n → Bool) (w : Fin t → Bool) :
    decide ((windowRun p (windowInitial p r x) (List.ofFn w)).state.val = 1) =
      acceptsChoices p t (initial p (List.ofFn x)) w := by
  rw [acceptsChoices_eq_foldl]
  have h := windowRun_agrees p (List.ofFn w) (by simpa using ht) _ _
    (windowInitial_agrees p r (List.ofFn w).length x)
  rw [h.state]

end UniversalMachine

end VPVNP
end Computability
end OAI
