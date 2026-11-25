import OAI.ThreeFlat.RAM.Weighted
import Mathlib.Data.Fin.Tuple.Basic

namespace OAI
/-! # Returning a weighted evaluator to native RAM code

The caller and callee have disjoint program-counter, register and public-word
banks. They share private and external memory. A normal return copies its
encoded scalar to a caller register and resumes at a designated label.
The continuation receives the remaining fuel on each individual branch.
-/

namespace ThreeFlat.RAM.Subroutine

open Computability.VPVNP.BurstRAM PrivateRAM

variable {w p q r s k l : ℕ} {F C D : Type*}

/-- Relocate every operand of a callee opcode. The state-word instruction reads
the caller's argument register. Returning and accepting both transfer control. -/
def relocate (arg result : Fin s) (resume : Fin q) (unitWord : Word w) :
    Instr w p r k → Instr w (p + q) (r + s) (k + l)
  | .constant a v n => .constant (a.castAdd s) v (n.castAdd q)
  | .publicWord a j n => .publicWord (a.castAdd s) (j.castAdd l) (n.castAdd q)
  | .stateWord a n => .copy (a.castAdd s) (Fin.natAdd r arg) (n.castAdd q)
  | .copy a b n => .copy (a.castAdd s) (b.castAdd s) (n.castAdd q)
  | .binary op a b d n => .binary op (a.castAdd s) (b.castAdd s) (d.castAdd s) (n.castAdd q)
  | .loadPrivate a b n => .loadPrivate (a.castAdd s) (b.castAdd s) (n.castAdd q)
  | .storePrivate a b n => .storePrivate (a.castAdd s) (b.castAdd s) (n.castAdd q)
  | .jumpEq a b n m => .jumpEq (a.castAdd s) (b.castAdd s) (n.castAdd q) (m.castAdd q)
  | .jumpLt a b n m => .jumpLt (a.castAdd s) (b.castAdd s) (n.castAdd q) (m.castAdd q)
  | .choose n m => .choose (n.castAdd q) (m.castAdd q)
  | .readExternal a b n => .readExternal (a.castAdd s) (b.castAdd s) (n.castAdd q)
  | .writeExternal a b n => .writeExternal (a.castAdd s) (b.castAdd s) (n.castAdd q)
  | .returnState b => .copy (Fin.natAdd r result) (b.castAdd s) (Fin.natAdd p resume)
  | .accept => .constant (Fin.natAdd r result) unitWord (Fin.natAdd p resume)
  | .reject => .reject

/-- A native caller can jump to the callee's first label any number of times. -/
def link (child : Machine w p r k) (caller : Fin q → Instr w (p+q) (r+s) (k+l))
    (parentData : Fin l → Word w) (entry resume : Fin q) (arg result : Fin s)
    (unitWord : Word w) : Machine w (p+q) (r+s) (k+l) where
  entry := Fin.natAdd p entry
  code := Fin.addCases (fun j => relocate arg result resume unitWord (child.code j)) caller
  publicData := Fin.addCases child.publicData parentData

/-- Embed a live call, preserving the caller's own persistent word and registers.
The caller supplied its argument in the designated register. -/
def embed (q : ℕ) (arg : Fin s) (persistent : Word w) (frame : Fin s → Word w)
    (c : Config w p r) : Config w (p+q) (r+s) where
  pc := c.pc.castAdd q
  persistent := persistent
  reg := Fin.addCases c.reg (Function.update frame arg c.persistent)
  privateMem := c.privateMem

/-- The register and memory state when control reaches the caller's next label. -/
def returned (resume : Fin q) (arg result : Fin s) (persistent unitWord : Word w)
    (frame : Fin s → Word w) (c : Config w p r) (v : Option (Word w)) :
    Config w (p+q) (r+s) :=
  (embed q arg persistent frame c).put (Fin.natAdd p resume) (Fin.natAdd r result)
    (v.getD unitWord)

@[simp] theorem link_code_caller (child : Machine w p r k)
    (caller : Fin q → Instr w (p+q) (r+s) (k+l)) (data : Fin l → Word w)
    (entry resume : Fin q) (arg result : Fin s) (unitWord : Word w) (i : Fin q) :
    (link child caller data entry resume arg result unitWord).code (Fin.natAdd p i) = caller i := by
  simp [link]

@[simp] theorem returned_result (resume : Fin q) (arg result : Fin s) (persistent unitWord : Word w)
    (frame : Fin s → Word w) (c : Config w p r) (v : Option (Word w)) :
    (returned resume arg result persistent unitWord frame c v).reg (Fin.natAdd r result) =
      v.getD unitWord := by
  simp [returned]

/-- The value in the caller's result register, including a unit-valued accepting
halt, decodes to precisely the scalar used by the child's path sum. -/
theorem decoded_return [One F] (code : FieldCode F w) (resume : Fin q) (arg result : Fin s)
    (persistent : Word w) (frame : Fin s → Word w) (c : Config w p r) (v : Option (Word w)) :
    code.decode ((returned resume arg result persistent (code.encode 1) frame c v).reg
      (Fin.natAdd r result)) = code.terminal v := by
  cases v <;> simp [FieldCode.terminal, code.decode_encode]

private theorem put_embed (arg : Fin s) (persistent : Word w) (frame : Fin s → Word w)
    (c : Config w p r) (n : Fin p) (d : Fin r) (v : Word w) :
    (embed q arg persistent frame c).put (n.castAdd q) (d.castAdd s) v =
      embed q arg persistent frame (c.put n d v) := by
  unfold Config.put embed
  congr 1
  funext i
  induction i using Fin.addCases with
  | left i =>
    by_cases h : i = d
    · subst i
      simp
    · have h' : i.castAdd s ≠ d.castAdd s := fun he => h (Fin.ext (congrArg (fun z : Fin (r+s) => z.val) he))
      simp [Function.update_of_ne h, Function.update_of_ne h']
  | right i =>
    have h : Fin.natAdd r i ≠ d.castAdd s := by
      intro he
      have hh := congrArg Fin.val he
      simp at hh
      omega
    simp [Function.update_of_ne h]

/-- A lifted step sends halts to the caller while rejection ends the path. -/
private def resumeAction (up : C → D) (ret : Option (Word w) → D) :
    CallAction w C → CallAction w D
  | .localStep c => .localStep (up c)
  | .branch f => .branch (fun b => up (f b))
  | .read a f => .read a (fun x => up (f x))
  | .write a v c => .write a v (up c)
  | .finish v => .localStep (ret v)
  | .reject => .reject

private theorem step_link (child : Machine w p r k)
    (caller : Fin q → Instr w (p+q) (r+s) (k+l)) (data : Fin l → Word w)
    (entry resume : Fin q) (arg result : Fin s) (persistent unitWord : Word w)
    (frame : Fin s → Word w) (c : Config w p r) :
    (link child caller data entry resume arg result unitWord).program.step
      (embed q arg persistent frame c) =
    resumeAction (embed q arg persistent frame)
      (returned resume arg result persistent unitWord frame c) (child.program.step c) := by
  change ((link child caller data entry resume arg result unitWord).code (c.pc.castAdd q)).run
    (Fin.addCases child.publicData data) (embed q arg persistent frame c) =
    resumeAction _ _ ((child.code c.pc).run child.publicData c)
  simp only [link, Fin.addCases_left]
  cases child.code c.pc <;>
    simp [relocate, Instr.run, resumeAction, returned, embed, Fin.addCases_left, Fin.addCases_right,
      Config.store, apply_ite] <;> try rfl
  all_goals first | exact put_embed arg persistent frame c _ _ _ |
                      exact funext fun v => put_embed arg persistent frame c _ _ v

/-- Weighted execution with a callback at every normal return, carrying
residual fuel, the live callee registers, external memory and returned word. -/
def massThen [AddZeroClass F] (P : Program w C)
    (ret : ℕ → C → Memory w → Option (Word w) → F) : ℕ → C → Memory w → F
  | 0, _, _ => 0
  | f + 1, c, m =>
    match P.step c with
    | .localStep next => massThen P ret f next m
    | .branch next => massThen P ret f (next false) m + massThen P ret f (next true) m
    | .read a next => massThen P ret f (next (m a.val)) m
    | .write a v next => massThen P ret f next (writeMemory m a v)
    | .finish v => ret f c m v
    | .reject => 0

/-- Every path through the embedded native code invokes the caller continuation once
at its own remaining fuel. The callback observes any memory effects of that path. -/
theorem mass_link [Semiring F] (code : FieldCode F w) (child : Machine w p r k)
    (caller : Fin q → Instr w (p+q) (r+s) (k+l)) (data : Fin l → Word w)
    (entry resume : Fin q) (arg result : Fin s) (persistent : Word w)
    (frame : Fin s → Word w) (fuel : ℕ) (c : Config w p r) (mem : Memory w) :
    let unitWord := code.encode 1
    let P := (link child caller data entry resume arg result unitWord).program
    mass code P fuel (embed q arg persistent frame c) mem =
      massThen child.program (fun f c' m v =>
        mass code P f (returned resume arg result persistent unitWord frame c' v) m) fuel c mem := by
  dsimp only
  induction fuel generalizing c mem with
  | zero => rfl
  | succ fuel ih =>
    rw [mass, step_link, massThen]
    cases child.program.step c <;> simp [resumeAction, ih]

/-- A continuation multiplying each returned scalar by a fixed accumulator
multiplies the total evaluator mass by that accumulator. -/
theorem massThen_mul [Semiring F] (code : FieldCode F w) (P : Program w C)
    (a : F) (fuel : ℕ) (c : C) (mem : Memory w) :
    massThen P (fun _ _ _ v => a * code.terminal v) fuel c mem = a * mass code P fuel c mem := by
  induction fuel generalizing c mem with
  | zero => simp [mass, massThen]
  | succ fuel ih =>
    rw [massThen, mass]
    cases P.step c <;> simp [ih, mul_add]

/-- All paths halt by the given budget. A normal return additionally satisfies the
postcondition, including its exact remaining budget. -/
def returnsBy (P : Program w C) (post : ℕ → C → Memory w → Option (Word w) → Prop) :
    ℕ → C → Memory w → Prop
  | 0, _, _ => False
  | f+1, c, m =>
    match P.step c with
    | .localStep next => returnsBy P post f next m
    | .branch next => returnsBy P post f (next false) m ∧ returnsBy P post f (next true) m
    | .read a next => returnsBy P post f (next (m a.val)) m
    | .write a v next => returnsBy P post f next (writeMemory m a v)
    | .finish v => post f c m v
    | .reject => True

/-- Reserve additional fuel for a caller. If the caller's mass multiplies the
returned scalar on each reachable return, then the joint execution computes
the product with the bounded callee's value. -/
theorem massThen_mul_of_returnsBy [Semiring F] (code : FieldCode F w) (P : Program w C)
    (ret : ℕ → C → Memory w → Option (Word w) → F) (a : F) (budget reserve : ℕ)
    (c : C) (mem : Memory w)
    (h : returnsBy P (fun f c' m v => ret (f+reserve) c' m v = a * code.terminal v)
      budget c mem) :
    massThen P ret (budget+reserve) c mem = a * mass code P budget c mem := by
  induction budget generalizing c mem with
  | zero => exact False.elim h
  | succ budget ih =>
    rw [Nat.succ_add, massThen, mass]
    unfold returnsBy at h
    cases e : P.step c with
    | localStep next | read _ next | write _ _ next =>
      rw [e] at h
      exact ih _ _ h
    | branch next =>
      rw [e] at h
      simpa [mul_add] using congrArg₂ (· + ·) (ih _ _ h.1) (ih _ _ h.2)
    | finish v =>
      rw [e] at h
      exact h
    | reject => simp

end ThreeFlat.RAM.Subroutine

end OAI
