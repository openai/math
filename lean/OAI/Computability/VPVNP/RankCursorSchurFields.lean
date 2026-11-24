import OAI.Computability.VPVNP.RankCursorPorts
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-!
# Loading the six Schur root fields from the rank cursor

The product root consists of its zero tag, balanced-product depth, zero
block start, matrix row count and the two cursor indices. The loader copies
these six words from the cursor bank into the live query frame, preserving
all input registers. The matrix dimensions and both degrees are stack data.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Cursor

open RAMTape BurstRAM Dispatch UniversalCountStack

variable {K : Type}

private def reg (i : Fin 8) : ScanPort K := .cursor (.isa (.reg (Registers.arg i)))

private def source : Fin 6 → ScanPort K :=
  ![reg 4, .depth, reg 4, .rows, reg 1, reg 2]

private def dest (i : Fin 6) : ScanPort K := .engine (.frame (.inl (Fin.castAdd 3 i).succ))

private theorem dest_inj : Function.Injective (@dest K) := by
  intro i j h
  have he := Sum.inl.inj (Engine.Port.frame.inj (ScanPort.engine.inj h))
  exact Fin.ext (Nat.succ.inj (congrArg Fin.val he))

private theorem src_ne_dest (i j : Fin 6) : source i ≠ dest (K := K) j := by
  fin_cases i <;> intro h <;> cases h

private theorem src_ne_tmp (i : Fin 6) : source i ≠ (ScanPort.scratch : ScanPort K) := by
  fin_cases i <;> intro h <;> cases h

private def copies : List (Fin 6) → FiniteRoutine (ScanPort K)
  | [] => .ret
  | i :: rest => (SuccessorFields.prependCopy (source i) (dest i) .scratch).followedBy (copies rest)

/-- Copy the product tag, depth, block start, row count, and two scan indices into the six
fields of the Schur root request. -/
def loadRoot : FiniteRoutine (ScanPort K) := copies (List.finRange 6)

/-- Step bound for the six copies of w-bit words that initialize a Schur root request. -/
def loadClock (w : ℕ) := 6*(5*w+2)+1

private noncomputable def staged (s : Stacks (ScanPort K)) (todo : List (Fin 6)) :=
  installStacks dest s (fun i => if i ∈ todo then [] else s (source i))

variable [DecidableEq K]

private theorem copies_runs (s : Stacks (ScanPort K)) (todo : List (Fin 6)) (hn : todo.Nodup)
    (w : ℕ) (hw : ∀ i, (s (source i)).length = w) (ht : s .scratch = []) :
    (copies todo).Runs (todo.length*(5*w+2)+1) (staged s todo) (staged s []) := by
  induction todo with
  | nil => simpa only [copies, FiniteRoutine.ret, FiniteRoutine.ofRoutine, FiniteRoutine.Runs, List.length_nil, Nat.zero_mul, Nat.zero_add] using Routine.runs_ret (staged s [])
  | cons i rest ih =>
    have hin := (List.nodup_cons.mp hn).1
    have hsource : staged s (i :: rest) (source i) = s (source i) :=
      installStacks_outside _ _ (fun j => (src_ne_dest i j).symm)
    have htmp : staged s (i :: rest) .scratch = [] :=
      (installStacks_outside s _ (fun j (h : dest j = .scratch) => by cases h)).trans ht
    have hdest : staged s (i :: rest) (dest i) = [] := by
      simp [staged, installStacks_at dest_inj]
    have hwrite : Function.update (staged s (i :: rest)) (dest i) (s (source i)) = staged s rest := by
      rw [staged, installStacks_update dest_inj]
      apply congrArg (installStacks dest s)
      funext j
      by_cases h : j = i
      · subst j; simp [hin]
      · simp [h]
    have h := SuccessorFields.prependCopy_runs (source i) (dest i) .scratch (src_ne_dest i i)
      (src_ne_tmp i) (by intro he; cases he) (staged s (i :: rest)) htmp
    rw [hsource, hw, hdest, List.append_nil, hwrite] at h
    have hrun := h.followedBy (ih (List.nodup_cons.mp hn).2)
    rw [show (i::rest).length*(5*w+2)+1 = (5*w+2) + (rest.length*(5*w+2)+1) by
      simp only [List.length_cons, Nat.succ_mul]; omega]
    exact hrun

private theorem wordBits_digits {w : ℕ} (r : Word w) : wordBits r = digits w r.val :=
  congrArg wordBits (Fin.ext (Nat.mod_eq_of_lt r.isLt).symm)

omit [DecidableEq K] in
private theorem source_word {n U Z w : ℕ} (persistent : Word w) (rs : Regs Registers.R w)
    (u : Limit U) (z : Limit Z) (hregs : Registers.Stores rs Z u.val z.val) (aux : Stacks K)
    (i : Fin 6) :
    scanBank n persistent rs [] (idle aux) [] (source i) =
      digits w ((SchurKey.root (n := n) u z).words i) := by
  have h0 : (rs (Registers.arg 4)).val = 0 := hregs 4 (by decide)
  have hu : (rs (Registers.arg 1)).val = u.val := hregs 1 (by decide)
  have hz : (rs (Registers.arg 2)).val = z.val := hregs 2 (by decide)
  fin_cases i <;> first
    | rfl
    | exact (wordBits_digits _).trans (congrArg (digits w) h0)
    | exact (wordBits_digits _).trans (congrArg (digits w) hu)
    | exact (wordBits_digits _).trans (congrArg (digits w) hz)

/-- Normal return puts the engine directly at its typed root-entry bank, with
the input registers, descriptor bank and empty scratch preserved. -/
theorem loadRoot_runs {n U Z w v p e : ℕ} {c : SliceArithmetic.Vector p e}
    (persistent : Word w) (rs : Regs Registers.R w) (u : Limit U) (z : Limit Z)
    (hregs : Registers.Stores rs Z u.val z.val) (aux : Stacks K) :
    loadRoot.Runs (loadClock w) (scanBank n persistent rs [] (idle aux))
      (scanBank n persistent rs [] (Engine.atControl w v
        (.enter (SchurKey.root (n := n) u z)) ([] : List (Engine.F n U Z c)) aux)) := by
  let s := scanBank n persistent rs [] (idle aux)
  have src := source_word persistent rs u z hregs aux (n := n)
  have hw (i : Fin 6) : (s (source i)).length = w := by simp only [s, src, length_digits]
  have h := copies_runs s (List.finRange 6) (List.nodup_finRange 6) w hw rfl
  have start : staged s (List.finRange 6) = s := by
    apply installStacks_eq dest_inj
    intro i; simp [s, dest, scanBank, idle, Engine.store]
  have finish : staged s [] = scanBank n persistent rs [] (Engine.atControl w v
      (.enter (SchurKey.root (n := n) u z)) ([] : List (Engine.F n U Z c)) aux) := by
    apply installStacks_frame dest_inj
    · intro i
      change (Engine.fields w [] (SchurKey.root (n := n) u z) [] [] [] (Fin.castAdd 3 i).succ) =
        (if i ∈ ([] : List (Fin 6)) then [] else s (source i))
      simp only [Engine.fields, Fin.cons_succ, Fin.append_left, List.not_mem_nil, ↓reduceIte]
      exact (src i).symm
    · intro k hout
      cases k with
      | cursor | rows | depth | scratch => rfl
      | engine k => cases k with
        | result | condition | aux => rfl
        | frame f => cases f with
          | inr j => rfl
          | inl j =>
            fin_cases j <;> first
              | rfl
              | exact (hout 0 rfl).elim
              | exact (hout 1 rfl).elim
              | exact (hout 2 rfl).elim
              | exact (hout 3 rfl).elim
              | exact (hout 4 rfl).elim
              | exact (hout 5 rfl).elim
  rw [start, finish, List.length_finRange] at h
  exact h

end RankQuery.Stack.Cursor

end VPVNP
end Computability
end OAI
