import OAI.Computability.VPVNP.PairSimulationLeafCacheRead

/-!
# Storing the coefficient counter's scalar cache once per pair call

Each register produced by the operand evaluator is written into its
prescribed private cache cell. The two-instruction store and increment
sequence has no external actions and preserves the source registers.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSourceLoad

open BurstRAM PrivateRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {k w p r pubs : ℕ}

/-- Store one computed operand at the private cache cursor. -/
def storeInstr (src : Static k → Fin r) (cursor : Fin r) (next : Fin p) (i : Static k) : Instr w p r pubs :=
  .storePrivate cursor (src i) next

/-- The exact consecutive output words, final cursor and unchanged surrounding private state. -/
structure Stored (c out : Config w p r) (cursor : Fin r) (base : ℕ) (xs : List (Word w)) : Prop where
  persistent : out.persistent = c.persistent
  cursor_end : out.reg cursor = ((base+xs.length : ℕ) : Word w)
  frame : ∀ j, j ≠ cursor → out.reg j = c.reg j
  values : ∀ i : Fin xs.length, out.privateMem ((base+i.val : ℕ) : Word w) = xs[i]
  outside : ∀ a : Word w, a.val < base ∨ base+xs.length ≤ a.val → out.privateMem a = c.privateMem a

theorem write_rows (M : Machine w p r pubs) (src : Static k → Fin r) (cursor unit : Fin r)
    (hs : ∀ j, src j ≠ cursor) (hu : unit ≠ cursor) (ls : List (Static k)) (vals : Static k → Word w)
    (pc : Fin (ls.length+1) → Fin p) (inc : Fin ls.length → Fin p)
    (store : ∀ i : Fin ls.length, M.code (pc i.castSucc) = storeInstr src cursor (inc i) ls[i])
    (advance : ∀ i : Fin ls.length, M.code (inc i) = incInstr cursor unit (pc i.succ))
    (base : ℕ) (c : Config w p r) (entry : c.pc = pc 0)
    (hc : c.reg cursor = (base : Word w)) (hone : c.reg unit = 1)
    (ready : ∀ j, c.reg (src j) = vals j) (fit : base+ls.length ≤ 2^w) :
    ∃ out, Prefix M c (List.replicate (2*ls.length) .tick) out ∧
      out.pc = pc (Fin.last ls.length) ∧ Stored c out cursor base (ls.map vals) := by
  induction ls generalizing c base with
  | nil =>
    exact ⟨c, .nil c, entry, rfl, hc, fun _ _ => rfl, fun i => Fin.elim0 i, fun _ _ => rfl⟩
  | cons j ls ih =>
    let t := c.store (inc 0) (base : Word w) (vals j)
    let u := t.put (pc (Fin.succ 0)) cursor ((base+1 : ℕ) : Word w)
    have hstore := store 0
    change M.code (pc 0) = storeInstr src cursor (inc 0) j at hstore
    have h₁ : M.program.step c = .localStep t := by
      change (M.code c.pc).run M.publicData c = _
      rw [entry,hstore]
      simp only [storeInstr,Instr.run,hc,ready,t]
    have h₂ : M.program.step t = .localStep u := by
      change (M.code (inc 0)).run M.publicData t = _
      rw [advance 0]
      simp only [incInstr,Instr.run,BinaryOp.eval,t,u,Config.store,hc,hone,Nat.cast_add,Nat.cast_one]
    have hlen : base+1+ls.length ≤ 2^w := by simp only [List.length_cons] at fit; omega
    obtain ⟨out,tail,done,stored⟩ := ih (fun i => pc i.succ) (fun i => inc i.succ)
      (fun i => store i.succ) (fun i => advance i.succ) (base+1) u rfl (Function.update_self ..)
      (by change Function.update c.reg cursor _ unit = 1; rw [Function.update_of_ne hu,hone])
      (fun i => by change Function.update c.reg cursor _ (src i) = _; rw [Function.update_of_ne (hs i),ready]) hlen
    have run := Prefix.tick h₁ (Prefix.tick h₂ tail)
    have ticks : 2*(j::ls).length = (2*ls.length+1)+1 := by simp; omega
    rw [ticks,List.replicate_succ,List.replicate_succ]
    refine ⟨out,run,done,stored.persistent,?_,?_,?_,?_⟩
    · simpa only [List.length_map,List.length_cons,Nat.add_assoc,Nat.add_comm 1] using stored.cursor_end
    · intro i hi
      exact (stored.frame i hi).trans (Function.update_of_ne hi ..)
    · intro i
      have hb : base < 2^w := by omega
      induction i using Fin.cases with
      | zero =>
        have keep := stored.outside (base : Word w) (.inl (by change base % _ < _; rw [Nat.mod_eq_of_lt hb]; omega))
        change out.privateMem ((base+0 : ℕ) : Word w) = vals j
        rw [Nat.add_zero,keep]
        exact Function.update_self ..
      | succ i =>
        have h := stored.values i
        change out.privateMem ((base+(i.val+1) : ℕ) : Word w) = (ls.map vals)[i]
        simpa only [Nat.add_assoc,Nat.add_comm 1] using h
    · intro a ha
      have hx : a.val < base+1 ∨ base+1+(ls.map vals).length ≤ a.val := by
        simp only [List.length_map,List.length_cons] at ha ⊢; omega
      rw [stored.outside a hx]
      apply Function.update_of_ne
      intro he
      have hb : base < 2^w := by omega
      have hv : a.val = base := (congrArg Fin.val he).trans (Nat.mod_eq_of_lt hb)
      simp only [List.length_map,List.length_cons] at ha
      omega

end PairSimulation.LeafSourceLoad

end VPVNP
end Computability
end OAI
