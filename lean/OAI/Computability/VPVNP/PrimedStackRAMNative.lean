import OAI.Computability.VPVNP.PrimedStackRAMVisit

/-!
# Acceptance of the native preorder-node program

At ordinary burst-call entry the private workspace is zero. The program
loads the row offset from the persistent word and executes the finite node
table. Its accepting choice streams agree exactly with the grammar visit,
including the end-of-call test for unused bits.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedCounter
open scoped Fin.CommRing

variable {w n m R H base : ℕ}

/-- Private register file after loading the persistent input-row offset into register 5 of the
initially zero workspace. -/
def entryRegs (row : Word w) : Regs w 16 := Function.update (fun _ => 0) 5 row

theorem execute_nodeTemplate (pub : Fin 11 → Word w) (row : Word w) (mem : Memory w) (bits : List Bool) :
    let M := nodeTemplate.instantiate w pub
    BurstRAM.execute M.program (12*w+92) (M.program.start row) mem bits =
      (completeNode pub row (entryRegs row) mem bits).map fun o =>
        ⟨.tick :: o.events, some (o.regs 5)⟩ := by
  let a : Flow 16 11 := .seq (.line (.stateWord 5)) nodeFlow
  let M := (a.template (some 5)).instantiate w pub
  let lab : nodeFlow.Label → Fin (a.length+2) := fun i => a.pc (.inr i)
  have hl := Flow.template_linked (w := w) a (some 5) pub
  have hb : M.code a.rejectPC = .reject := by
    change ((a.template (some 5)).code a.rejectPC).resize w = _
    rw [Flow.template_reject]
    rfl
  have hret : M.code a.exitPC = .returnState 5 := by
    change ((a.template (some 5)).code a.exitPC).resize w = _
    rw [Flow.template_exit]
    rfl
  have hs : M.program.step (M.program.start row) =
      .localStep ⟨lab nodeFlow.entry,row,entryRegs row,fun _ => 0⟩ := by
    change (M.code (a.pc (.inl ()))).run pub _ = _
    rw [hl.atLabel (.inl ())]
    rfl
  have he := node_refines.execute hl.seqRight hb row (entryRegs row) (fun _ => 0) mem bits
    (12*w+91) (by omega)
  change BurstRAM.execute M.program (12*w+92) (M.program.start row) mem bits = _
  rw [show 12*w+92 = (12*w+91)+1 by omega, BurstRAM.execute, hs]
  change (BurstRAM.execute M.program (12*w+91) ⟨lab nodeFlow.entry,row,entryRegs row,fun _ => 0⟩ mem bits).map _ = _
  apply (congrArg (Option.map (Report.prepend .tick)) he).trans
  change ((nodeKernel pub row (entryRegs row) mem bits).bind _).map _ = _
  cases hh : nodeKernel pub row (entryRegs row) mem bits with
  | none => simp [completeNode, hh]
  | some o =>
    have hlen := node_refines.bounded hh
    obtain ⟨f,hf⟩ : ∃ f, 12*w+91-o.events.length = f+1 := ⟨12*w+90-o.events.length, by omega⟩
    have hd : M.program.step ⟨a.exitPC,row,o.regs,fun _ => 0⟩ = .finish (some (o.regs 5)) := by
      change (M.code a.exitPC).run pub _ = _
      rw [hret]
      rfl
    simp only [Option.bind_some]
    change ((BurstRAM.execute M.program (12*w+91-o.events.length)
      ⟨a.exitPC,row,o.regs,fun _ => 0⟩ o.mem o.bits).map _).map _ = _
    rw [hf, BurstRAM.execute, hd]
    cases hbits : o.bits <;> simp [completeNode, hh, hbits]
    change Report.mk (.tick :: o.events) _ = Report.mk (.tick :: (o.events ++ [])) _
    simp
    rfl

theorem Agreement.isSome_eq {x : Fin 2 → Fin R → Fin m → Bool} {a : Option (VisitState n m H)}
    {o : Option (Output w 16)} (h : Agreement base x a o) : o.isSome = a.isSome := by cases h <;> rfl

/-- Native accepting paths for this call, with no per-input changes to the instruction table. -/
theorem nodeTemplate_accepts_iff {x : Fin 2 → Fin R → Fin m → Bool} {st : VisitState n m H}
    {mem : Memory w} (hr : Holds base x st mem) (g : Fin 2) (s : Fin R) (bits : List Bool)
    (hf : base + size R n m (labelCount n m H) ≤ 2^w) (hH : H < 2^w) (hw : 2 < 2^w)
    (hprod : n*n ≤ 2^w) (hmass : leafMass st.pending ≤ n) (hcounts : ∀ a, st.counts a + 1 < 2^w) :
    let M := nodeTemplate.instantiate w (publicData w base R n m H)
    let row : Word w := ↑((g.val*R+s.val)*m)
    (BurstRAM.execute M.program (12*w+92) (M.program.start row) mem bits).isSome ↔
      (visit w (x g s) st bits).isSome := by
  dsimp only
  rw [execute_nodeTemplate, Option.isSome_map]
  let row : Word w := ↑((g.val*R+s.val)*m)
  have h := completeNode_visit hr g s row (entryRegs row) bits (by simp [entryRegs,row])
    hf hH hw hprod hmass hcounts
  rw [h.isSome_eq]

end PrimedStackRAM

end VPVNP
end Computability
end OAI
