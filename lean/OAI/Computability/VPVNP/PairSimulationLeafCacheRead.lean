import OAI.Computability.VPVNP.PairSimulationLeafSourceLoad

/-!
# Reading the auxiliary leaf's cached operands in private RAM

The pair call computes the constant-sized scalar array in private memory.
A leaf loads its words in consecutive address order. The only extra register
written is the cache cursor. Every load and increment is a private tick.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSourceLoad

open BurstRAM PrivateRAM LeafRegisterBank PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {k w p r pubs : ℕ}

/-- Load a scalar from the private cache at the current cursor. -/
def readInstr (ports : Source k ↪ Fin r) (cursor : Fin r) (next : Fin p) (i : Static k) : Instr w p r pubs :=
  .loadPrivate (ports i.dest) cursor next

/-- Advance the private cache cursor by one word. -/
def incInstr (cursor unit : Fin r) (next : Fin p) : Instr w p r pubs :=
  .binary .add cursor cursor unit next

private theorem fold_cursor (ports : Source k ↪ Fin r) (vals : Static k → Word w)
    (cursor : Fin r) (hc : ∀ i : Static k, cursor ≠ ports i.dest) (ls : List (Static k))
    (bank : Fin r → Word w) (a : Word w) :
    ls.foldl (setStatic ports vals) (Function.update bank cursor a) =
      Function.update (ls.foldl (setStatic ports vals) bank) cursor a := by
  induction ls generalizing bank with
  | nil => rfl
  | cons i ls ih =>
    simp only [List.foldl_cons]
    unfold setStatic
    rw [Function.update_comm (hc i)]
    exact ih _

theorem cached_rows (M : Machine w p r pubs) (ports : Source k ↪ Fin r) (cursor unit : Fin r)
    (hcursor : ∀ i : Static k, cursor ≠ ports i.dest) (hunit : ∀ i : Static k, unit ≠ ports i.dest)
    (hu : unit ≠ cursor) (vals : Static k → Word w)
    (ls : List (Static k)) (pc : Fin (ls.length+1) → Fin p) (inc : Fin ls.length → Fin p)
    (read : ∀ i : Fin ls.length, M.code (pc i.castSucc) = readInstr ports cursor (inc i) ls[i])
    (advance : ∀ i : Fin ls.length, M.code (inc i) = incInstr cursor unit (pc i.succ))
    (base : ℕ) (c : Config w p r) (entry : c.pc = pc 0)
    (hc : c.reg cursor = (base : Word w)) (hone : c.reg unit = 1)
    (cache : ∀ i : Fin ls.length, c.privateMem ((base+i.val : ℕ) : Word w) = vals ls[i]) :
    Prefix M c (List.replicate (2*ls.length) .tick)
      {c with
        pc := pc (Fin.last ls.length)
        reg := Function.update (ls.foldl (setStatic ports vals) c.reg) cursor ((base+ls.length : ℕ) : Word w)} := by
  induction ls generalizing c base with
  | nil =>
    simp only [List.length_nil, List.foldl_nil, Nat.mul_zero, List.replicate_zero, Nat.add_zero,
      ← hc, Function.update_eq_self]
    rw [show Fin.last 0 = 0 from rfl, ← entry]
    exact .nil c
  | cons i ls ih =>
    let t := c.put (inc 0) (ports i.dest) (vals i)
    let u := t.put (pc (Fin.succ 0)) cursor ((base+1 : ℕ) : Word w)
    have hread := read 0
    change M.code (pc 0) = readInstr ports cursor (inc 0) i at hread
    have hval := cache 0
    change c.privateMem ((base+0 : ℕ) : Word w) = vals i at hval
    rw [Nat.add_zero] at hval
    have h₁ : M.program.step c = .localStep t := by
      change (M.code c.pc).run M.publicData c = _
      rw [entry,hread]
      simp only [readInstr,Instr.run,hc,hval,t]
    have hadd := advance 0
    have h₂ : M.program.step t = .localStep u := by
      change (M.code (inc 0)).run M.publicData t = _
      rw [hadd]
      simp only [incInstr,Instr.run,BinaryOp.eval,u,t,Config.put,Function.update_of_ne (hcursor i),
        Function.update_of_ne (hunit i),hc,hone,Nat.cast_add,Nat.cast_one]
    have tail := ih (fun j => pc j.succ) (fun j => inc j.succ) (fun j => read j.succ)
      (fun j => advance j.succ) (base+1) u rfl (Function.update_self ..)
      (by change (Function.update (Function.update c.reg _ _) cursor _) unit = 1
          rw [Function.update_of_ne hu, Function.update_of_ne (hunit i), hone])
      (fun j => by
        have h := cache j.succ
        change c.privateMem ((base+(j.val+1) : ℕ) : Word w) = vals ls[j] at h
        change c.privateMem ((base+1+j.val : ℕ) : Word w) = vals ls[j]
        simpa only [Nat.add_assoc, Nat.add_comm 1] using h)
    change Prefix M u _ {c with
      pc := pc (Fin.last ls.length).succ
      reg := Function.update (ls.foldl (setStatic ports vals) (Function.update (setStatic ports vals c.reg i) cursor ((base+1 : ℕ) : Word w)))
        cursor ((base+1+ls.length : ℕ) : Word w)} at tail
    rw [fold_cursor ports vals cursor hcursor, Function.update_idem,
      show base+1+ls.length = base+(ls.length+1) by omega] at tail
    rw [show 2*(i::ls).length = (2*ls.length+1)+1 by simp; omega, List.replicate_succ,List.replicate_succ]
    exact .tick h₁ (.tick h₂ tail)

end PairSimulation.LeafSourceLoad

end VPVNP
end Computability
end OAI
