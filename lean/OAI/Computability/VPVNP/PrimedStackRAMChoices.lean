import OAI.Computability.VPVNP.PrimedStackRAMBinaryVisit

/-!
# Complete word choices at a parser node

The private RAM consumes one word at a terminal and three at an internal node.
A call cannot accept with unused choices. Separating this exact-length check
from the range checks identifies the same choice streams as the mathematical
token decoder, including truncated and overlong streams.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM PrimedCounter
open scoped Fin.CommRing

variable {w n m H : ℕ}

/-- Words guessed at one parser node before checking their bounds. A leaf carries a position,
and a binary node carries a split and two child states. -/
inductive RawChoice (w : ℕ)
  | leaf (v : Word w)
  | binary (b i j : Word w)

/-- Decode the entire branch tape as one width-`w` position word for a leaf or three width-`w`
words for a binary node. Return `none` for a truncated tape or leftover bits. -/
def exactChoice (w : ℕ) (leaf : Bool) (bits : List Bool) : Option (RawChoice w) := do
  let (b,tail) ← takeWord w bits
  if leaf then
    if tail.isEmpty then return .leaf b else none
  else
    let (i,tail) ← takeWord w tail
    let (j,tail) ← takeWord w tail
    if tail.isEmpty then return .binary b i j else none

/-- Convert a raw choice to a grammar token by checking the leaf position against `m` or the
binary split against `d` and both child states against `H`. -/
def RawChoice.token (d m H : ℕ) : RawChoice w → Option (Token m (Fin H))
  | .leaf j => if h : j.val < m then some (.terminal ⟨j.val,h⟩) else none
  | .binary b i j => if b.val < d then
      if hi : i.val < H then if hj : j.val < H then some (.binary b.val ⟨i.val,hi⟩ ⟨j.val,hj⟩) else none
      else none
    else none

theorem readToken_eq_choice (d : ℕ) (bits : List Bool) :
    readToken w m H d bits =
      (exactChoice w (decide (d = 0)) bits).bind (RawChoice.token d m H) := by
  cases h₀ : takeWord w bits with
  | none => by_cases h : d = 0 <;> simp [readToken, exactChoice, takeBounded, h, h₀]
  | some a =>
    obtain ⟨b,t₀⟩ := a
    by_cases hd : d = 0
    · by_cases hb : b.val < m <;> cases t₀ <;>
        simp [readToken, exactChoice, RawChoice.token, takeBounded, h₀, hd, hb]
    · cases h₁ : takeWord w t₀ with
      | none => by_cases hb : b.val < d <;> simp [readToken, exactChoice, takeBounded, hd, hb, h₀, h₁]
      | some a =>
        obtain ⟨i,t₁⟩ := a
        cases h₂ : takeWord w t₁ with
        | none =>
          by_cases hb : b.val < d <;> by_cases hi : i.val < H <;>
            simp [readToken, exactChoice, takeBounded, hd, hb, hi, h₀, h₁, h₂]
        | some a =>
          obtain ⟨j,t₂⟩ := a
          by_cases hb : b.val < d <;> by_cases hi : i.val < H <;> by_cases hj : j.val < H <;>
            cases t₂ <;> simp [readToken, exactChoice, RawChoice.token, takeBounded, hd, hb, hi, hj, h₀, h₁, h₂]

/-- Test whether the raw node choice consists of a single leaf-position word. -/
def RawChoice.isLeaf : RawChoice w → Bool
  | .leaf _ => true
  | .binary .. => false

theorem exactChoice_kind (w : ℕ) (leaf : Bool) (bits : List Bool) (c : RawChoice w)
    (h : exactChoice w leaf bits = some c) : c.isLeaf = leaf := by
  cases leaf with
  | true =>
    simp only [exactChoice, bind, Option.bind_eq_some_iff, ite_true] at h
    obtain ⟨⟨v,t⟩,_,h⟩ := h
    cases t <;> simp_all [RawChoice.isLeaf]
    subst c
    rfl
  | false =>
    simp only [exactChoice, bind, Option.bind_eq_some_iff, Bool.false_eq_true, ite_false] at h
    obtain ⟨⟨b,t⟩,_,⟨i,u⟩,_,⟨j,z⟩,_,h⟩ := h
    cases z <;> simp_all [RawChoice.isLeaf]
    subst c
    rfl

/-- The outgoing call state, requiring the branch tape to be consumed exactly. -/
def completeNode (pub : Fin 11 → Word w) (state : Word w) (regs : Regs w 16)
    (mem : Memory w) (bits : List Bool) : Option (Output w 16) :=
  (nodeKernel pub state regs mem bits).filter fun o => o.bits.isEmpty

/-- Store the guessed word in the first register of the supplied embedding and clear the other
two registers used by the word reader. -/
def setGuess (reg : Fin 3 ↪ Fin 16) (rs : Regs w 16) (v : Word w) := GuessWord.resultRegs reg rs v

/-- Register file after the node guesses. Register 2 holds the leaf position or split, and
binary nodes also place the left and right states in registers 3 and 4. -/
def choiceRegs (rs : Regs w 16) : RawChoice w → Regs w 16
  | .leaf j => setGuess (guessRegs 2 (by decide) (by decide)) rs j
  | .binary b i j =>
    let rs := setGuess (guessRegs 2 (by decide) (by decide)) rs b
    let rs := setGuess (guessRegs 3 (by decide) (by decide)) rs i
    setGuess (guessRegs 4 (by decide) (by decide)) rs j

/-- Select the leaf or binary instruction block that processes the guessed words after the
stack pop. -/
def RawChoice.lines : RawChoice w → List Line
  | .leaf _ => leafLines
  | .binary .. => binaryLines

/-- Private word-reader trace for the leaf position or, at a binary node, the concatenated
traces for the split, left state, and right state. -/
def RawChoice.events : RawChoice w → List (Event w)
  | .leaf v => GuessWord.trace v
  | .binary b i j => GuessWord.trace b ++ (GuessWord.trace i ++ GuessWord.trace j)

private theorem guess_no_probes (v : Word w) : countProbes (GuessWord.trace v) = 0 := by
  have aux (bits : List Bool) : countProbes (GuessWord.events (w := w) bits) = 0 := by
    induction bits with
    | nil => rfl
    | cons b bits ih => simpa [GuessWord.events, countProbes] using ih
  simpa [GuessWord.trace, countProbes] using aux (wordBits v)

theorem RawChoice.no_probes (c : RawChoice w) : countProbes c.events = 0 := by
  cases c <;> simp [RawChoice.events, probes_append, guess_no_probes]

/-- After the initial pop, the complete native node accepts exactly the decoded
raw choice and then executes the corresponding leaf or internal block. -/
theorem completeNode_pop (pub : Fin 11 → Word w) (st : Word w) (rs r₀ : Regs w 16)
    (mem m₀ : Memory w) (es₀ : List (Event w)) (bits : List Bool)
    (hp : trace pub st pop rs mem = some (es₀,r₀,m₀)) :
    completeNode pub st rs mem bits =
      (exactChoice w (decide (r₀ 0 = r₀ 12)) bits).bind fun c =>
        (trace pub st c.lines (choiceRegs r₀ c) m₀).map fun (es,rs',m') =>
          ⟨es₀ ++ (.tick :: (c.events ++ es)),rs',m',[]⟩ := by
  cases h₀ : takeWord w bits with
  | none =>
    by_cases h : r₀ 0 = r₀ 12 <;>
      simp [completeNode,nodeKernel,seqKernel,lineKernel,eqKernel,leafKernel,binaryKernel,
        guessKernel,exactChoice,hp,h,h₀]
  | some a =>
    obtain ⟨b,t₀⟩ := a
    by_cases h : r₀ 0 = r₀ 12
    · let t := trace pub st leafLines (choiceRegs r₀ (.leaf b)) m₀
      cases ht : t with
      | none =>
        cases t₀ <;> simp [completeNode,nodeKernel,seqKernel,lineKernel,eqKernel,leafKernel,guessKernel,
          exactChoice,hp,h,h₀,RawChoice.lines,choiceRegs,setGuess,t] at ht ⊢ <;> simp [ht]
      | some a =>
        obtain ⟨es,r₁,m₁⟩ := a
        cases t₀ <;> simp [completeNode,nodeKernel,seqKernel,lineKernel,eqKernel,leafKernel,guessKernel,
          exactChoice,hp,h,h₀,RawChoice.lines,RawChoice.events,Output.prepend,choiceRegs,setGuess,t] at ht ⊢ <;>
          simp [ht, Output.prepend]
    · cases h₁ : takeWord w t₀ with
      | none => simp [completeNode,nodeKernel,seqKernel,lineKernel,eqKernel,binaryKernel,guessKernel,exactChoice,
          hp,h,h₀,h₁]
      | some a =>
        obtain ⟨i,t₁⟩ := a
        cases h₂ : takeWord w t₁ with
        | none => simp [completeNode,nodeKernel,seqKernel,lineKernel,eqKernel,binaryKernel,guessKernel,exactChoice,
            hp,h,h₀,h₁,h₂]
        | some a =>
          obtain ⟨j,t₂⟩ := a
          let t := trace pub st binaryLines (choiceRegs r₀ (.binary b i j)) m₀
          cases ht : t with
          | none =>
            cases t₂ <;> simp [completeNode,nodeKernel,seqKernel,lineKernel,eqKernel,binaryKernel,guessKernel,
              exactChoice,hp,h,h₀,h₁,h₂,RawChoice.lines,choiceRegs,setGuess,t] at ht ⊢ <;> simp [ht]
          | some a =>
            obtain ⟨es,r₁,m₁⟩ := a
            cases t₂ <;> simp [completeNode,nodeKernel,seqKernel,lineKernel,eqKernel,binaryKernel,guessKernel,
              exactChoice,hp,h,h₀,h₁,h₂,RawChoice.lines,RawChoice.events,Output.prepend,choiceRegs,setGuess,t] at ht ⊢ <;>
              simp [ht,Output.prepend]

end PrimedStackRAM

end VPVNP
end Computability
end OAI
