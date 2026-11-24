import OAI.Computability.VPVNP.PairNativeFrameTable
import OAI.Computability.VPVNP.PairSimulationLeafCacheWrite

/-! # Installing the terminal geometry in actual private memory

A vertex's call stores its frame pointer in private cell n and the twelve
header operands at consecutive addresses starting at G. The cursor is the
only register changed. The source register for field six also supplies n.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeFrame

open BurstRAM PrivateRAM PrimedInputRAM PrimedCounter.GuessWord LeafSourceLoad
open scoped Fin.CommRing

variable {w p r : ℕ}

/-- Private geometry pointer and twelve header fields after the store loop. -/
structure Installed (c out : Config w p r) (reg : Fin 24 ↪ Fin r) (n G : ℕ) : Prop where
  persistent : out.persistent = c.persistent
  cursor : out.reg (reg 18) = ((G+12 : ℕ) : Word w)
  registers : ∀ j, j ≠ reg 18 → out.reg j = c.reg j
  pointer : out.privateMem (n : Word w) = (G : Word w)
  fields : ∀ i : Fin 12, out.privateMem ((G+i.val : ℕ) : Word w) = c.reg (reg (fieldReg i))
  outside : ∀ a : Word w, a.val ≠ n → a.val < G ∨ G+12 ≤ a.val → out.privateMem a = c.privateMem a

private def ids := (List.finRange 12).map (Static.operand (k := 12))
private theorem ids_get (i : Fin ids.length) : ids[i] = .operand (i.cast (by simp [ids])) := by
  have get (j : Fin 12) :
      ((List.finRange 12).map (Static.operand (k := 12)))[j.val]'(by simp) = .operand j := by
    rw [List.getElem_map, List.getElem_finRange]
    rfl
  exact get (i.cast (by simp [ids]))

private def port (reg : Fin 24 ↪ Fin r) : Static 12 → Fin r
  | .operand i => reg (fieldReg i)
  | _ => reg 3

/-- Prefix of the literal fixed table from the pointer store up to the
histogram handoff. All twenty-five events are private ticks. -/
theorem store_run (flow : Flow r 11) (reg : Fin 24 ↪ Fin r) (savedHist cacheDst : Fin r)
    (emb : Fin (Table.size flow) → Fin p) (finish : Instr 2 p r 11) (M : Machine w p r 11)
    (rows : ∀ j, M.code (emb j) = (Table.row flow reg savedHist cacheDst emb finish j).resize w)
    (n G : ℕ) (before : n < G) (fit : G+12 ≤ 2^w) (c : Config w p r)
    (entry : c.pc = emb (Table.tail flow 0)) (hn : c.reg (reg 9) = (n : Word w))
    (hg : c.reg (reg 2) = (G : Word w)) (hc : c.reg (reg 18) = (G : Word w))
    (one : c.reg (reg 15) = 1) :
    ∃ out, Prefix M c (List.replicate 25 .tick) out ∧
      out.pc = emb (Table.store flow (Fin.last 12)) ∧ Installed c out reg n G := by
  let b := c.store (emb (Table.store flow 0)) (n : Word w) (G : Word w)
  have first : M.program.step c = .localStep b := by
    change (M.code c.pc).run M.publicData c = _
    rw [entry, rows, Table.at_pointer]
    simp only [Instr.resize, Instr.run, hn, hg, b]
  have len : ids.length = 12 := by simp [ids]
  have hs (j : Static 12) : port reg j ≠ reg 18 := by
    cases j <;> apply reg.injective.ne
    all_goals first | decide | (intro he; have hh := congrArg Fin.val he; change 3 + _ = 18 at hh; omega)
  let pc (j : Fin (ids.length+1)) := emb (Table.store flow (j.cast (by omega)))
  let inc (j : Fin ids.length) := emb (Table.advance flow (j.cast len))
  have storeRow (i : Fin ids.length) :
      M.code (pc i.castSucc) = storeInstr (port reg) (reg 18) (inc i) ids[i] := by
    rw [ids_get]
    change M.code (emb (Table.store flow (i.cast len).castSucc)) = _
    rw [rows, Table.at_store]
    rfl
  have incRow (i : Fin ids.length) :
      M.code (inc i) = incInstr (reg 18) (reg 15) (pc i.succ) := by
    dsimp only [inc]
    rw [rows, Table.at_advance]
    rfl
  obtain ⟨out, run, done, S⟩ := write_rows M (port reg) (reg 18) (reg 15) hs
    (reg.injective.ne (by decide)) ids (c.reg ∘ port reg) pc inc storeRow incRow G b rfl hc one
    (fun _ => rfl) (by simpa only [len] using fit)
  have memLen : (ids.map (c.reg ∘ port reg)).length = 12 := by simpa only [List.length_map] using len
  refine ⟨out,?_,done,S.persistent,memLen ▸ S.cursor_end,S.frame,?_,?_,?_⟩
  · change Prefix M c (.tick :: List.replicate 24 .tick) out
    exact .tick first (by simpa only [len] using run)
  · rw [S.outside _ (.inl (by change n % _ < G; rw [Nat.mod_eq_of_lt (by omega)]; exact before))]
    exact Function.update_self ..
  · intro i
    have hi := S.values (i.cast memLen.symm)
    change out.privateMem ((G+i.val : ℕ) : Word w) = (ids.map (c.reg ∘ port reg))[i.val]'_ at hi
    rw [List.getElem_map] at hi
    have eqn : ids[i.val]'(by omega) = .operand i := ids_get (i.cast len.symm)
    rw [eqn] at hi
    exact hi
  · intro a hn ha
    rw [S.outside _ (by simpa only [memLen] using ha)]
    apply Function.update_of_ne
    exact fun eqn => hn ((congrArg Fin.val eqn).trans (Nat.mod_eq_of_lt (by omega)))

end PairSimulation.NativeFrame

end VPVNP
end Computability
end OAI
