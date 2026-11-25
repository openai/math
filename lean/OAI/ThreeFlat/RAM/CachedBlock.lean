import OAI.ThreeFlat.RAM.ContinuationLink
import OAI.ThreeFlat.RAM.DeterministicBlock

namespace OAI
/-! # Reading immutable operands from a disjoint cached register bank -/

namespace ThreeFlat.RAM.CachedBlock
open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
variable {w p r k P R K : ℕ}

def mapInstr (pc : Fin p→Fin P) (reg : Fin r→Fin R) (pub : Fin k→Fin K) :
    Instr w p r k→Instr w P R K
  | .constant a v n => .constant (reg a) v (pc n)
  | .publicWord a b n => .publicWord (reg a) (pub b) (pc n)
  | .stateWord a n => .stateWord (reg a) (pc n)
  | .copy a b n => .copy (reg a) (reg b) (pc n)
  | .binary op a b c n => .binary op (reg a) (reg b) (reg c) (pc n)
  | .loadPrivate a b n => .loadPrivate (reg a) (reg b) (pc n)
  | .storePrivate a b n => .storePrivate (reg a) (reg b) (pc n)
  | .jumpEq a b l n => .jumpEq (reg a) (reg b) (pc l) (pc n)
  | .jumpLt a b l n => .jumpLt (reg a) (reg b) (pc l) (pc n)
  | .choose l n => .choose (pc l) (pc n)
  | .readExternal a b n => .readExternal (reg a) (reg b) (pc n)
  | .writeExternal a b n => .writeExternal (reg a) (reg b) (pc n)
  | .returnState a => .returnState (reg a)
  | .accept => .accept
  | .reject => .reject

theorem mapInstr_comp {p' r' k' : ℕ} (f : Fin p→Fin P) (g : Fin r→Fin R)
    (h : Fin k→Fin K) (f' : Fin P→Fin p') (g' : Fin R→Fin r') (h' : Fin K→Fin k')
    (i : Instr w p r k) :
    mapInstr f' g' h' (mapInstr f g h i)=mapInstr (f' ∘ f) (g' ∘ g) (h' ∘ h) i := by
  cases i <;> rfl

def canonicalRow (b : Block w p r k) (i : Fin p) :=
  b.emit (Fin.castAddEmb 1) (Function.Embedding.refl _) id (Fin.natAdd p 0) i

def targets (pc : Fin p ↪ Fin P) (exit : Fin P) : Fin (p+1)→Fin P :=
  Fin.addCases pc (fun _ : Fin 1 => exit)

def Natural (b : Block w p r k) : Prop :=
  ∀ {P R K} (pc : Fin p ↪ Fin P) (reg : Fin r ↪ Fin R) (pub : Fin k→Fin K) (exit : Fin P) (i : Fin p),
    b.emit pc reg pub exit i=mapInstr (targets pc exit) reg pub (canonicalRow b i)

/-- There is no instruction referring to the host machine's public word bank.
A compiled public-word fetch copies the corresponding cached word. -/
def cachedInstr (pc : Fin p→Fin P) (reg : Fin r→Fin R) (cache : Fin k→Fin R) :
    Instr w p r k→Instr w P R K
  | .constant a v n => .constant (reg a) v (pc n)
  | .publicWord a b n => .copy (reg a) (cache b) (pc n)
  | .stateWord a n => .stateWord (reg a) (pc n)
  | .copy a b n => .copy (reg a) (reg b) (pc n)
  | .binary op a b c n => .binary op (reg a) (reg b) (reg c) (pc n)
  | .loadPrivate a b n => .loadPrivate (reg a) (reg b) (pc n)
  | .storePrivate a b n => .storePrivate (reg a) (reg b) (pc n)
  | .jumpEq a b l n => .jumpEq (reg a) (reg b) (pc l) (pc n)
  | .jumpLt a b l n => .jumpLt (reg a) (reg b) (pc l) (pc n)
  | .choose l n => .choose (pc l) (pc n)
  | .readExternal a b n => .readExternal (reg a) (reg b) (pc n)
  | .writeExternal a b n => .writeExternal (reg a) (reg b) (pc n)
  | .returnState a => .returnState (reg a)
  | .accept => .accept
  | .reject => .reject

theorem mapInstr_wordWork (pc : Fin p→Fin P) (reg : Fin r→Fin R) (pub : Fin k→Fin K)
    (i : Instr w p r k) : (mapInstr pc reg pub i).wordWork=i.wordWork := by
  cases i <;> rfl

theorem cachedInstr_wordWork (pc : Fin p→Fin P) (reg : Fin r→Fin R) (cache : Fin k→Fin R)
    (i : Instr w p r k) : (cachedInstr (K:=K) pc reg cache i).wordWork=i.wordWork := by
  cases i <;> rfl

def body (b : Block w p r k) : Block w p (r+k) 0 where
  first := b.first
  emit pc reg _ exit j := cachedInstr (targets pc exit)
    (reg ∘ Fin.castAdd k) (reg ∘ Fin.natAdd r) (canonicalRow b j)

end ThreeFlat.RAM.CachedBlock

end OAI
