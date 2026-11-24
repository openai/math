import OAI.Computability.BinPacking.CookLevin.ConfigIndex
import OAI.Computability.VPVNP.BooleanTranscript

/-!
# Boolean circuits for the gate-transcript verifier

The Cook–Levin compiler uses numbered wires and the AND/OR/NOT basis.
Translate its output to the AND/NOT basis of the VNP transcript construction,
with a bound of four gates per original gate and arbitrary input pinning.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CookCircuit

open BinPackingGames.Foundations.Complexity

variable {σ : Type*}

/-- The translated program and the current translation of each source wire. -/
private structure Builder (σ : Type*) where
  size : ℕ
  program : BooleanTranscript.Program σ size
  wire : ℕ → Ref Bool σ size

private def Builder.read (b : Builder σ) (x : σ → Bool) (i : ℕ) : Bool :=
  (b.wire i).read id x (b.program.run x)

private theorem read_ref (b : Builder σ) (x : σ → Bool) (i : ℕ) :
    (b.wire i).read id x (b.program.run x) = b.read x i := rfl

private def weaken {n : ℕ} : Ref Bool σ n → Ref Bool σ (n + 1)
  | .const v => .const v
  | .var i => .var i
  | .gate i => .gate i.castSucc

private theorem read_weaken {n : ℕ} (r : Ref Bool σ n) (x : σ → Bool)
    (v : Fin n → Bool) (w : Bool) :
    (weaken r).read id x (Fin.snoc v w) = r.read id x v := by
  cases r <;> simp [weaken, Ref.read]

/-- Write one translated gate at the specified source-wire address. -/
private def emit (b : Builder σ) (i : ℕ) (g : BooleanTranscript.Gate σ b.size) :
    Builder σ where
  size := b.size + 1
  program := b.program.snoc g
  wire := Function.update (fun j => weaken (b.wire j)) i (.gate (Fin.last b.size))

private theorem emit_read_self (b : Builder σ) (i : ℕ) (g : BooleanTranscript.Gate σ b.size)
    (x : σ → Bool) : (emit b i g).read x i = g.eval x (b.program.run x) := by
  simp [emit, Builder.read, Ref.read, BooleanTranscript.Program.run]

private theorem emit_read_other (b : Builder σ) (i j : ℕ) (h : j ≠ i)
    (g : BooleanTranscript.Gate σ b.size) (x : σ → Bool) :
    (emit b i g).read x j = b.read x j := by
  simp [emit, Builder.read, Function.update_of_ne h, BooleanTranscript.Program.run, read_weaken]

/-- Temporary wires of the De Morgan expansion lie above every live source wire. -/
private def next (b : Builder σ) (i : ℕ) : CookLevin.Gate → Builder σ
  | .const v => { b with wire := Function.update b.wire i (.const v) }
  | .not a => emit b i (.not (b.wire a))
  | .and a c => emit b i (.and (b.wire a) (b.wire c))
  | .or a c =>
    let p := emit b (i + 1) (.not (b.wire a))
    let q := emit p (i + 2) (.not (p.wire c))
    let r := emit q (i + 3) (.and (q.wire (i + 1)) (q.wire (i + 2)))
    emit r i (.not (r.wire (i + 3)))

private theorem next_read_other (b : Builder σ) (g : CookLevin.Gate) (x : σ → Bool)
    {i j : ℕ} (hj : j < i) : (next b i g).read x j = b.read x j := by
  have h0 : j ≠ i := Nat.ne_of_lt hj
  have h1 : j ≠ i + 1 := by omega
  have h2 : j ≠ i + 2 := by omega
  have h3 : j ≠ i + 3 := by omega
  cases g with
  | const v => simp [next, Builder.read, Function.update_of_ne h0]
  | not a | and a c | or a c =>
    simp only [next, emit_read_other _ _ _ h0, emit_read_other _ _ _ h1,
      emit_read_other _ _ _ h2, emit_read_other _ _ _ h3]

private theorem next_read_self (b : Builder σ) (g : CookLevin.Gate) (x : σ → Bool)
    (i : ℕ) (hg : g.Bounded i) : (next b i g).read x i = g.eval (b.read x) := by
  cases g with
  | const v => simp [next, Builder.read, Ref.read, CookLevin.Gate.eval]
  | not a | and a c =>
    rw [next, emit_read_self]
    rfl
  | or a c =>
    have hc : c < i := hg.2
    have h1 : c ≠ i + 1 := by omega
    have h2 : i + 1 ≠ i + 2 := by omega
    simp only [next, emit_read_self, BooleanTranscript.Gate.eval, CookLevin.Gate.eval,
      read_ref, emit_read_other _ _ _ h2, emit_read_other _ _ _ h1]
    cases b.read x a <;> cases b.read x c <;> rfl

private theorem next_size_le (b : Builder σ) (i : ℕ) (g : CookLevin.Gate) :
    (next b i g).size ≤ b.size + 4 := by
  cases g <;> simp only [next, emit] <;> omega

private def compile (start : ℕ) (b : Builder σ) : List CookLevin.Gate → Builder σ
  | [] => b
  | g :: gs => compile (start + 1) (next b start g) gs

private theorem compile_size_le (gs : List CookLevin.Gate) (start : ℕ) (b : Builder σ) :
    (compile start b gs).size ≤ b.size + 4 * gs.length := by
  induction gs generalizing start b with
  | nil => simp [compile]
  | cons g gs ih =>
    have h := ih (start + 1) (next b start g)
    have h' := next_size_le b start g
    simp only [compile, List.length_cons]
    omega

private theorem compile_correct (gs : List CookLevin.Gate) (start : ℕ) (b : Builder σ)
    (h : CookLevin.Ordered start gs) (x : σ → Bool) (A : ℕ → Bool)
    (ha : ∀ j < start, b.read x j = A j) :
    ∀ j < start + gs.length, (compile start b gs).read x j = CookLevin.run start gs A j := by
  induction gs generalizing start b A with
  | nil => simpa [compile, CookLevin.run] using ha
  | cons g gs ih =>
    obtain ⟨hg, hgs⟩ := (CookLevin.ordered_cons _ _ _).mp h
    apply fun j hj => ih (start + 1) (next b start g) hgs
      (Function.update A start (g.eval A)) ?_ j (by simp only [List.length_cons] at hj; omega)
    intro j hj
    by_cases he : j = start
    · subst j
      rw [Function.update_self, next_read_self _ _ _ _ hg]
      exact CookLevin.Gate.eval_congr _ hg _ _ ha
    · rw [Function.update_of_ne he, next_read_other _ _ _ (by omega)]
      exact ha _ (by omega)

/-- Each primary source input can be either an input variable or a Boolean constant. -/
private def initial {n : ℕ} (pins : Fin n → σ ⊕ Bool) : Builder σ where
  size := 0
  program := .nil
  wire j := if hj : j < n then (pins ⟨j, hj⟩).elim .var .const else .const false

/-- Size of the compiled AND/NOT verifier circuit. -/
def transcriptSize (C : CookLevin.Circuit) : ℕ :=
  (compile C.inputs (initial (fun i : Fin C.inputs => Sum.inl i)) C.gates).size

private theorem compile_size_eq {τ : Type*} (gs : List CookLevin.Gate) (start : ℕ)
    (b : Builder σ) (c : Builder τ) (h : b.size = c.size) :
    (compile start b gs).size = (compile start c gs).size := by
  induction gs generalizing start b c with
  | nil => exact h
  | cons g gs ih =>
    apply ih
    cases g <;> simp only [next, emit, h]

/-- Compile an ordered Boolean circuit while substituting inputs or constants. -/
def toTranscriptWith (C : CookLevin.Circuit) (pins : Fin C.inputs → σ ⊕ Bool) :
    BooleanTranscript.Circuit σ (transcriptSize C) :=
  let b := compile C.inputs (initial pins) C.gates
  let he : b.size = transcriptSize C := compile_size_eq C.gates _ _ _ rfl
  he ▸ (⟨b.program, b.wire C.output⟩ : BooleanTranscript.Circuit σ b.size)

private theorem eval_cast {n m : ℕ} (h : n = m) (c : BooleanTranscript.Circuit σ n)
    (x : σ → Bool) : ((h ▸ c : BooleanTranscript.Circuit σ m).eval x) = c.eval x := by
  cases h
  rfl

/-- Input pinning and gate translation agree with ordinary Boolean evaluation on every input. -/
theorem toTranscriptWith_eval (C : CookLevin.Circuit) (pins : Fin C.inputs → σ ⊕ Bool)
    (x : σ → Bool) :
    (toTranscriptWith C pins).eval x = C.eval (fun i => (pins i).elim x id) := by
  have hc := compile_correct C.gates C.inputs (initial pins) C.ordered x
    (CookLevin.inputEnv (fun i => (pins i).elim x id)) (by
      intro j hj
      cases hh : pins ⟨j, hj⟩ <;> simp [initial, Builder.read, CookLevin.inputEnv, hj, hh, Ref.read])
    C.output C.output.isLt
  exact (eval_cast _ _ x).trans hc

/-- Translate with all primary inputs free. -/
def toTranscript (C : CookLevin.Circuit) : BooleanTranscript.Circuit (Fin C.inputs) (transcriptSize C) :=
  toTranscriptWith C Sum.inl

theorem toTranscript_eval (C : CookLevin.Circuit) (x : Fin C.inputs → Bool) :
    (toTranscript C).eval x = C.eval x := toTranscriptWith_eval C Sum.inl x

theorem toTranscript_size_le (C : CookLevin.Circuit) : transcriptSize C ≤ 4 * C.gates.length := by
  simpa [transcriptSize, initial] using
    compile_size_le C.gates C.inputs (initial (fun i : Fin C.inputs => Sum.inl i))

end CookCircuit

end VPVNP
end Computability
end OAI
