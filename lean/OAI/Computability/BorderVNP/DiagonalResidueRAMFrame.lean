import OAI.Computability.BorderVNP.DiagonalResidueRAMSteps

/-! # Register and memory effects of the fixed residue-reader loop bodies -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA

variable {w : ℕ}

/-- All recorded signs are positive, with exactly the given sequence of
binary choices and the given number of ticks. -/
def TraceOK (es : List (TeamRAM.Event w)) (bits : List Bool) (ticks : ℕ) : Prop :=
  es.length = ticks ∧ es.flatMap TeamRAM.Event.choices = bits ∧ ∀ e ∈ es, e.sign = .plus

/-- Combining two fragments concatenates choices and adds ticks. -/
theorem TraceOK.append {es fs : List (TeamRAM.Event w)} {bs cs : List Bool} {k l : ℕ}
    (h : TraceOK es bs k) (j : TraceOK fs cs l) : TraceOK (es ++ fs) (bs ++ cs) (k+l) := by
  rcases h with ⟨he,hb,hs⟩
  rcases j with ⟨je,jb,js⟩
  exact ⟨by simp [he,je], by simp [hb,jb], fun e h => (List.mem_append.mp h).elim (hs e) (js e)⟩

/-- An ordinary branch test contributes one tick and no guess. -/
theorem TraceOK.cons_tick {es : List (TeamRAM.Event w)} {bs : List Bool} {k : ℕ}
    (h : TraceOK es bs k) : TraceOK (tick w :: es) bs (k+1) := by
  rcases h with ⟨he,hb,hs⟩
  exact ⟨by simp [he], by simp [tick, hb], by simp [tick]; exact hs⟩

/-- Embed a natural address or counter into the current machine width. -/
def word (w n : ℕ) : Word w := Fin.ofNat _ n

@[simp] theorem word_zero (w : ℕ) : word w 0 = 0 := rfl

@[simp] theorem word_one (w : ℕ) : word w 1 = 1 := rfl

@[simp] theorem word_two (w : ℕ) : word w 2 = 2 := rfl

@[simp] theorem word_add (w i j : ℕ) : word w (i+j) = word w i + word w j := Fin.ext (Nat.add_mod ..)

theorem word_val (w n : ℕ) (h : n < 2^w) : (word w n).val = n := Nat.mod_eq_of_lt h

/-- The six externally supplied registers of the reader. -/
structure Frame where
  /-- Number of Boolean gates. -/
  gates : ℕ
  /-- Number of private binary guesses. -/
  guesses : ℕ
  /-- Address of the first three-word gate record. -/
  advice : ℕ
  /-- Address of the constant zero, at the start of the valuation bank. -/
  base : ℕ
  /-- Absolute address selected as output. -/
  output : ℕ
  /-- Number of query bits before the private guesses. -/
  query : ℕ

/-- The input frame is installed in the agreed register bank. -/
def Frame.loaded (d : Frame) (s : Bank w) : Prop :=
  s 32 = word w d.gates ∧ s 33 = word w d.guesses ∧ s 34 = word w d.advice ∧ s 35 = word w d.base ∧ s 36 = word w d.output ∧
    s 37 = word w d.query

/-- The invariant common to both loops: operand registers and scratch constants. -/
def Frame.stable (d : Frame) (s : Bank w) : Prop := d.loaded s ∧ s 38 = 1 ∧ s 39 = 0

/-- The valuation bank precedes the advice bank, and the end sentinel for the
last three-word record fits in a word. -/
def Frame.fits (d : Frame) (w : ℕ) : Prop :=
  gateBase d.base d.query d.guesses + d.gates ≤ d.advice ∧ d.advice + 3 * d.gates < 2^w

/-- The six setup instructions put the first guess address and the zero
counter into their live registers. -/
theorem setup_effect (d : Frame) (s : Bank w) (m : Memory w) (hs : d.loaded s) :
    let e := effect false s m setup
    d.stable e.bank ∧ e.bank 40 = word w (d.base + 2 + d.query) ∧ e.bank 41 = 0 ∧
      e.mem = m ∧ TraceOK e.trace [] 6 := by
  rcases hs with ⟨h₀,h₁,h₂,h₃,h₄,h₅⟩
  simp [setup, Code.block, effect, Frame.stable, Frame.loaded, Function.update, BinaryOp.eval,
    TraceOK, tick, h₀,h₁,h₂,h₃,h₄,h₅]; rfl

/-- Guess body writes one raw bit at the current cursor and increments both
counters. Its branch takes five ticks for either bit value. -/
theorem guess_effect (d : Frame) (s : Bank w) (m : Memory w) (b : Bool) (hs : d.stable s)
    (cursor i : ℕ) (hc : s 40 = word w cursor) (hi : s 41 = word w i) (hfit : cursor < 2^w) :
    let e := effect b s m guessBody
    d.stable e.bank ∧ e.bank 40 = word w (cursor + 1) ∧ e.bank 41 = word w (i + 1) ∧
      e.mem = Function.update m cursor (wordBit w b) ∧ TraceOK e.trace [b] 5 := by
  rcases hs with ⟨⟨h₀,h₁,h₂,h₃,h₄,h₅⟩, h₆, h₇⟩
  cases b <;>
    simp [guessBody, Code.block, effect, Frame.stable, Frame.loaded, Function.update, BinaryOp.eval,
      TraceOK, tick, choiceTick, wordBit, h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇,hc,hi, word_val _ _ hfit]; rfl

/-- The three actual shared words at a gate's instruction pointer. -/
def Row.atAddress (r : Row) (m : Memory w) (ip : ℕ) : Prop :=
  m ip = word w r.left ∧ m (ip + 1) = word w r.right ∧ m (ip + 2) = wordBit w r.invert

/-- Word-level implementation of a row using its three advised operands and
the two indirectly addressed values. -/
theorem gate_effect (d : Frame) (s : Bank w) (m : Memory w) (hs : d.stable s)
    (cursor i ip : ℕ) (hc : s 40 = word w cursor) (hi : s 41 = word w i) (hp : s 42 = word w ip)
    (r : Row) (hr : r.atAddress m ip) (hl : r.left < 2^w) (hright : r.right < 2^w)
    (hfit : cursor < 2^w) (hip : ip + 2 < 2^w) :
    let e := effect false s m gateBody
    d.stable e.bank ∧ e.bank 40 = word w (cursor + 1) ∧ e.bank 41 = word w (i + 1) ∧
      e.bank 42 = word w (ip + 3) ∧ e.mem = Function.update m cursor (r.value m) ∧
      TraceOK e.trace [] 13 := by
  rcases hs with ⟨⟨h₀,h₁,h₂,h₃,h₄,h₅⟩, h₆, h₇⟩
  rcases hr with ⟨hr₀,hr₁,hr₂⟩
  have ip₀ : ip < 2^w := by omega
  have ip₁ : ip+1 < 2^w := by omega
  have hstep (j : ℕ) : word w j + 1 = word w (j+1) := (word_add w j 1).symm
  simp only [gateBody, Code.block, effect]
  simp [Frame.stable, Frame.loaded, Function.update, BinaryOp.eval,
    TraceOK, tick, Row.value, h₀,h₁,h₂,h₃,h₄,h₅,h₆,h₇,hc,hi,hp,
    hstep, -word_add, word_val _ _ hfit, word_val _ _ hip, word_val _ _ ip₀, word_val _ _ ip₁,
    word_val _ _ hl, word_val _ _ hright, hr₀,hr₁,hr₂, Nat.add_assoc]

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
