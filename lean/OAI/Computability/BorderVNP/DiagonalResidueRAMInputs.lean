import OAI.Computability.BorderVNP.DiagonalResidueRAMCount
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Loading the residue reader from actual words and splitting its numbered inputs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalResidueRAM

open VPVNP VPVNP.BurstRAM VPVNP.BooleanTranscript RoutingISA

variable {w u v k : ℕ} {σ τ : Type*}

private def renameRef (f : σ → τ) (a : Ref Bool σ k) : Ref Bool τ k := a.subst (Sum.inl ∘ f) id

private def renameGate (f : σ → τ) : Gate σ k → Gate τ k
  | .and a b => .and (renameRef f a) (renameRef f b)
  | .not a => .not (renameRef f a)

private def renameProgram (f : σ → τ) : {k : ℕ} → Program σ k → Program τ k
  | _, .nil => .nil
  | _, .snoc p g => .snoc (renameProgram f p) (renameGate f g)

private theorem rename_read (f : σ → τ) (x : τ → Bool) (g : Fin k → Bool) (a : Ref Bool σ k) :
    (renameRef f a).read id x g = a.read id (x ∘ f) g := by cases a <;> rfl

private theorem rename_run (f : σ → τ) (x : τ → Bool) (p : Program σ k) :
    (renameProgram f p).run x = p.run (x ∘ f) := by
  induction p with
  | nil => rfl
  | snoc p g ih =>
    cases g <;> simp [renameProgram, renameGate, BooleanTranscript.Program.run, BooleanTranscript.Gate.eval, ih, rename_read]

/-- Relabel arbitrary input pins without changing any shared gate. -/
def relabelCircuit (f : σ → τ) (c : Circuit σ k) : Circuit τ k :=
  ⟨renameProgram f c.program, renameRef f c.output⟩

/-- Evaluating a relabeled DAG pulls the Boolean assignment back along its pin map. -/
theorem relabelCircuit_eval (f : σ → τ) (c : Circuit σ k) (z : τ → Bool) :
    (relabelCircuit f c).eval z = c.eval (z ∘ f) := by
  simp only [relabelCircuit, BooleanTranscript.Circuit.eval, rename_run, rename_read]

/-- Split the numbered Boolean circuit's input tape into query and guess
words. Every operation, shared-gate address and output bit is preserved. -/
def separateInputs (c : Circuit (Fin (u+v)) k) : Circuit (Fin u ⊕ Fin v) k :=
  relabelCircuit finSumFinEquiv.symm c

/-- Tape concatenation in the numbered circuit is exactly the sum-type input
assignment used by the fixed RAM. -/
theorem separateInputs_eval (c : Circuit (Fin (u+v)) k) (x : Fin u → Bool) (y : Fin v → Bool) :
    (separateInputs c).eval (Sum.elim x y) = c.eval (Fin.append x y) := by
  rw [separateInputs, relabelCircuit_eval]
  have h : Sum.elim x y ∘ finSumFinEquiv.symm = Fin.append x y := by
    funext i
    refine Fin.addCases (fun a => ?_) (fun b => ?_) i <;> simp
  rw [h]

/-- Install a word array in a consecutive interval of existing memory. -/
def install (m : Memory w) (start : ℕ) (data : List (Word w)) (j : ℕ) : Word w :=
  if h : start ≤ j ∧ j-start < data.length then data[j-start] else m j

private theorem install_get (m : Memory w) (a : ℕ) (data : List (Word w)) (i : Fin data.length) :
    install m a data (a+i.val) = data[i.val] := by simp [install]

private theorem install_before (m : Memory w) (a : ℕ) (data : List (Word w)) (j : ℕ) (h : j < a) :
    install m a data j = m j := by simp [install, Nat.not_le.mpr h]

/-- Initial valuation words contain false, true and the query bits. -/
def queryData (w : ℕ) (x : Fin u → Bool) : List (Word w) :=
  wordBit w false :: wordBit w true :: List.ofFn (wordBit w ∘ x)

/-- Lay down the query and gate advice, preserving all other memory. -/
def initialMemory (m : Memory w) (base advice : ℕ) (c : Circuit (Fin u ⊕ Fin v) k)
    (x : Fin u → Bool) : Memory w :=
  install (install m base (queryData w x)) advice (adviceData (List.ofFn (rows base c.program)))

/-- The RAM operand bank is initialized from the six explicit scalar words. -/
def initialBank (s : Bank w) (d : Frame) : Bank w :=
  fun j => if j = 32 then word w d.gates else if j = 33 then word w d.guesses
    else if j = 34 then word w d.advice else if j = 35 then word w d.base
    else if j = 36 then word w d.output else if j = 37 then word w d.query else s j

/-- The concrete operand installation satisfies the reader's full frame contract. -/
theorem initialBank_loaded (s : Bank w) (d : Frame) : d.loaded (initialBank s d) := by
  simp [initialBank, Frame.loaded]

/-- Every serialized gate word is present in the advised memory. -/
theorem initialMemory_advice (m : Memory w) (base advice : ℕ) (c : Circuit (Fin u ⊕ Fin v) k)
    (x : Fin u → Bool) : hasAdvice (initialMemory m base advice c x) base advice c :=
  fun i => install_get _ _ _ i

/-- The constant and query words preceding the advice are preserved. -/
theorem initialMemory_query (m : Memory w) (base advice : ℕ) (c : Circuit (Fin u ⊕ Fin v) k)
    (x : Fin u → Bool) (h : base+2+u ≤ advice) : queryLoaded (initialMemory m base advice c x) base x := by
  constructor
  · intro b
    have hb : base+b.toNat < advice := by cases b <;> simp <;> omega
    rw [initialMemory, install_before _ _ _ _ hb]
    have hi : b.toNat < (queryData w x).length := by cases b <;> simp [queryData]
    rw [install_get _ _ _ ⟨b.toNat,hi⟩]
    cases b <;> rfl
  · intro i
    have hj : base+2+i.val < advice := by omega
    rw [initialMemory, install_before _ _ _ _ hj, Nat.add_assoc]
    have hi : 2+i.val < (queryData w x).length := by simp [queryData]; omega
    rw [install_get _ _ _ ⟨2+i.val,hi⟩]
    simp [queryData, Nat.add_comm 2]

/-- A real compiled, numbered verifier in concrete RAM memory has exactly the
integer Boolean witness count. Every scratch register and unrelated initial
memory word may be arbitrary. -/
theorem numbered_count (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (base advice : ℕ) (c : Circuit (Fin (u+v)) k) (x : Fin u → Bool) (s : Bank w) (m : Memory w)
    (hfit : gateBase base u v + k ≤ advice ∧ advice + 3*k < 2^w) :
    (Nat.card (Paths pub macros (initialBank s (frame base advice (separateInputs c)))
      (initialMemory m base advice (separateInputs c) x)) : ℤ) =
      ∑ y : Fin v → Bool, if c.eval (Fin.append x y) then (1 : ℤ) else 0 := by
  rw [native_count pub macros base advice (separateInputs c) x _ _ hfit (initialBank_loaded ..)
    (initialMemory_query m base advice (separateInputs c) x (by unfold gateBase at hfit; omega))
    (initialMemory_advice m base advice (separateInputs c) x)]
  simp [separateInputs_eval]

end DiagonalResidueRAM

end BorderVNP
end Computability
end OAI
