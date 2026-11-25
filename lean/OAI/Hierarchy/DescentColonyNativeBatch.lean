import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Consecutive immutable native output arenas -/

namespace Hierarchy.DescentColonies.NativeBatch
open ProtocolRAM Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

structure Code (w : ℕ) where
  text : Procedure w
  after : Memory w→Memory w
  ticks : ℕ

namespace Code
variable {w N : ℕ}

def exec (P : Code w) := ∀m,(P.text).Exec m (P.after m) P.ticks

def empty (w : ℕ) : Code w := ⟨ProtocolRAM.program w [],id,4⟩

def thenDo (a b : Code w) : Code w := ⟨a.text.seq b.text,b.after ∘ a.after,a.ticks+b.ticks⟩

theorem exec_empty : (empty w).exec := fun m => program_exec [] m (by simp)

theorem exec_seq {a b : Code w} (x : a.exec) (y : b.exec) : (a.thenDo b).exec := by
  intro m labels registers slots machine
  exact Procedure.Exec.then (x m) (y (a.after m)) machine

def seq (steps : Fin N → Code w) : (n : ℕ) → n≤N → Code w
  | 0,_ => empty w
  | n+1,hn => (seq steps n (by omega)).thenDo (steps ⟨n,hn⟩)

theorem exec_seqAll (steps : Fin N → Code w) (ok : ∀i,(steps i).exec) (n : ℕ) (hn : n≤N) :
    (seq steps n hn).exec := by
  induction n with
  | zero => exact exec_empty
  | succ n ih => exact exec_seq (ih _) (ok _)

theorem clock_seq (steps : Fin N → Code w) (b : ℕ) (bound : ∀i,(steps i).ticks≤b) (n : ℕ) (hn : n≤N) :
    (seq steps n hn).ticks≤4+n*b := by
  induction n with
  | zero => simp [seq,empty]
  | succ n ih =>
    change (seq steps n _).ticks+(steps ⟨n,hn⟩).ticks≤_
    have a := ih (show n≤N by omega)
    have c := bound ⟨n,hn⟩
    rw [Nat.succ_mul]
    omega

/-- Read-only input addresses survive the entire prefix of the schedule. -/
theorem frame_seq (steps : Fin N → Code w) (a : ℕ)
    (away : ∀i m,(steps i).after m a=m a) (m : Memory w) (n : ℕ) (hn : n≤N) :
    (seq steps n hn).after m a=m a := by
  induction n with
  | zero => rfl
  | succ n ih => exact (away _ _).trans (ih _)

/-- A condition on input storage is sufficient to establish the result left by
each stage, provided later stages preserve that earlier result. -/
theorem read_seq (steps : Fin N → Code w) (Init : Memory w→Prop) (Stable : ∀i m,Init m→Init ((steps i).after m))
    (Claim : Fin N→Memory w→Prop) (now : ∀i m,Init m→Claim i ((steps i).after m))
    (later : ∀i j : Fin N,i<j→∀m, Claim i m→Claim i ((steps j).after m))
    (m : Memory w) (hi : Init m) (n : ℕ) (hn : n≤N) :
    Init ((seq steps n hn).after m) ∧ ∀i : Fin N,i.val<n→Claim i ((seq steps n hn).after m) := by
  induction n with
  | zero => exact ⟨hi,fun _ h=>by omega⟩
  | succ n ih =>
    let j : Fin N := ⟨n,hn⟩
    obtain ⟨valid,old⟩ := ih (show n≤N by omega)
    refine ⟨Stable j _ valid,?_⟩
    intro i lt
    by_cases eq : i=j
    · subst i
      exact now j _ valid
    · have ne : i.val≠n := fun h=>eq (Fin.ext h)
      have prev : i.val<n := by omega
      exact later i j prev _ (old i prev)

end Code
end Hierarchy.DescentColonies.NativeBatch

end OAI
