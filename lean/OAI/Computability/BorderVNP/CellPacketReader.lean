import OAI.Computability.BorderVNP.CellDirectoryWire
import OAI.Computability.QuantumFactoring.BitStackConstants

/-! # Finite-stack readers of literal cell-packet prefixes

Each reader consumes its own prefix and appends its canonical output in reverse order on an
independent stack. Three counter stacks suffice for the nested length-prefixed lists in the
packet. The running-time bound charges only the consumed prefix. An enclosing reader can keep
its loop count live across every child call.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Native

open ExactQuantumFactoring.BitStackProgram
open RationalHitting.StackLanguage (codeWord)

/-- Public input, reverse output, three word-processing registers, and bounded nesting slots. -/
inductive Register where
  | input | output | control | digits | scratch | counter (k : Fin 3)
  deriving DecidableEq, Fintype

/-- Canonical state at a reader boundary. The caller owns the unused counter stacks. -/
def bank (src out : List Bool) (ct : Fin 3 → List Bool) : Store Register
  | .input => src
  | .output => out
  | .counter k => ct k
  | _ => []

/-- Actual per-field bit serialization, preserving the marker and binary terminator. -/
def wire (ns : List ℕ) := CellMacro.Generator.records (ns.map Nat.bits)

@[simp] theorem wire_nil : wire [] = [] := rfl

@[simp] theorem wire_cons (n : ℕ) (ns : List ℕ) :
    wire (n::ns) = true :: (codeWord n.bits ++ wire ns) := rfl

@[simp] theorem wire_append (ns ms : List ℕ) : wire (ns++ms) = wire ns ++ wire ms := by
  induction ns with
  | nil => rfl
  | cons n ns ih => simp [ih, List.append_assoc]

/-- A program on fixed finite stacks; the declared counter slots are its only additional
clean-register requirements. The output accumulator and unread suffix may have any length. -/
structure Reader {α : Type} (src dst : α → List Bool) (clean : Finset (Fin 3)) where
  /-- Static finite program. -/
  program : Program Register
  /-- Absolute factor in its quadratic prefix-length clock. -/
  scale : ℕ
  /-- Exact operational behavior on any correctly serialized prefix. -/
  runs (a : α) (rest out : List Bool) (ct : Fin 3 → List Bool) (h : ∀ k ∈ clean, ct k = []) :
    ∃ c ≤ scale * ((src a).length+1)^2,
      Runs program (bank (src a ++ rest) out ct) (bank rest ((dst a).reverse ++ out) ct) c

namespace Reader

variable {α β : Type} {src dst src' dst' : α → List Bool} {K L : Finset (Fin 3)}

/-- Transport both physical encodings by pointwise equality. -/
def castCode (p : Reader src dst K) (hs : ∀ a, src a = src' a) (hd : ∀ a, dst a = dst' a) :
    Reader src' dst' K :=
  ⟨p.program,p.scale,fun a rest out ct h => by simpa only [← hs a, ← hd a] using p.runs a rest out ct h⟩

/-- Use a verified physical routine on a component of a structured payload. -/
def on (p : Reader src dst K) (f : β → α) : Reader (src ∘ f) (dst ∘ f) K :=
  ⟨p.program,p.scale,fun b => p.runs (f b)⟩

/-- Two consecutive prefix readers emit their outputs in chronological order. -/
def followed (p : Reader src dst K) (q : Reader src' dst' L) :
    Reader (fun a => src a ++ src' a) (fun a => dst a ++ dst' a) (K ∪ L) where
  program := .seq p.program q.program
  scale := p.scale+q.scale
  runs a rest out ct h := by
    obtain ⟨u,hu,ru⟩ := p.runs a (src' a ++ rest) out ct (fun k hk => h k (Finset.mem_union_left _ hk))
    obtain ⟨v,hv,rv⟩ := q.runs a rest ((dst a).reverse ++ out) ct (fun k hk => h k (Finset.mem_union_right _ hk))
    refine ⟨v+u,?_,?_⟩
    · simp only [List.length_append, Nat.add_mul]
      have hp := Nat.mul_le_mul_left p.scale (Nat.pow_le_pow_left (show (src a).length+1 ≤ (src a).length+(src' a).length+1 by omega) 2)
      have hq := Nat.mul_le_mul_left q.scale (Nat.pow_le_pow_left (show (src' a).length+1 ≤ (src a).length+(src' a).length+1 by omega) 2)
      omega
    · simpa only [List.append_assoc, List.reverse_append] using Runs.seq ru rv

/-- Emit a finite constant while leaving the input untouched. -/
def literal (w : List Bool) : Reader (fun _ : α => []) (fun _ => w) ∅ where
  program := pushWord .output w.reverse
  scale := w.length+1
  runs a rest out ct _ := by
    refine ⟨w.length+1,by simp,?_⟩
    have hr := pushWord_runs Register.output w.reverse (bank rest out ct)
    have he : Function.update (bank rest out ct) Register.output (w.reverse ++ out) = bank rest (w.reverse ++ out) ct := by
      funext k; cases k <;> rfl
    simpa only [List.nil_append, List.length_reverse, he, bank] using hr

/-- Strengthening the clean-counter precondition reuses the identical program and clock. -/
def reserve (p : Reader src dst K) (h : K ⊆ L) : Reader src dst L :=
  ⟨p.program,p.scale,fun a rest out ct hc => p.runs a rest out ct (fun k hk => hc k (h hk))⟩

end Reader

/-- A static expansion of each output symbol; a product or list frame adds one quote layer. -/
abbrev Emit := Bool → List Bool

/-- Push one CQF quote layer inside the current output-bit expansion. -/
def underQuote (emit : Emit) (b : Bool) : List Bool := emit true ++ emit b

/-- Translate the first component of a CQF pair and its delimiter at the parent quote depth. -/
theorem flatMap_quote (emit : Emit) (w : List Bool) :
    (quoteBits w).flatMap emit = w.flatMap (underQuote emit) ++ emit false := by
  induction w with
  | nil => simp
  | cons b bs ih => simp [ih, underQuote, List.append_assoc]

/-- Complete records as a list of nonempty prefixes have at least one bit per element. -/
theorem length_le_flat {α : Type} (src : α → List Bool) (xs : List α)
    (hp : ∀ x, 0 < (src x).length) : xs.length ≤ (xs.flatMap src).length := by
  induction xs with
  | nil => rfl
  | cons a as ih =>
    simp only [List.length_cons, List.flatMap_cons, List.length_append]
    have := hp a
    omega

end CellSparse.Packet.Native

end BorderVNP
end Computability
end OAI
