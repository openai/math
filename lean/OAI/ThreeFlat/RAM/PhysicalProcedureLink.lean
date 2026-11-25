import OAI.ThreeFlat.RAM.PhysicalProcedure
import OAI.ThreeFlat.RAM.TickClearLink

namespace OAI
/-! # A preparatory procedure followed by an actual external-memory native machine -/

namespace ThreeFlat.RAM.PhysicalProcedure

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
variable {F : Type*} [Semiring F] {w p r k : ℕ}

private def prologue (A : Procedure w) (r k : ℕ) :
    Block w (A.labels+(r+1)) (A.registers+(r+1)) (A.slots+k) :=
  (A.block.reindex (Fin.castAddEmb (r+1)) (Fin.castAdd k)).seq
    ((TickClearFrame.block w (r+1) 0).reindex (Fin.natAddEmb A.registers) Fin.elim0)

private def nativeRegs (A : Procedure w) (r : ℕ) : Fin r ↪ Fin (A.registers+(r+1)) :=
  (Fin.castAddEmb 1).trans (Fin.natAddEmb A.registers)

/-- The prefix writes its output memory, then clears the callee's frame and jumps
to the actual relocated entry. The one extra scratch word permits zero-register callees. -/
def Procedure.link (A : Procedure w) (native : Machine w p r k) :
    Machine w ((A.labels+(r+1))+p) (A.registers+(r+1)) (A.slots+k) :=
  close (prologue A r k) native.entry
    (fun pc i => NativeRelocate.relocate pc (nativeRegs A r) (Fin.natAdd A.slots) (native.code i))
    (Fin.addCases A.publicData native.publicData)

/-- One deterministic prefix produces the memory for all subsequent callee fuel levels. -/
theorem Procedure.Spec.link_value {A : Procedure w} {pre : Memory w → Prop}
    {post : Memory w → Memory w → Prop} {budget : ℕ} (spec : A.Spec pre post budget)
    (native : Machine w p r k) (allowed : ∀ i, NativeRelocate.ExternalOnly (native.code i))
    (code : FieldCode F w) (state : Word w) (m : Memory w) (ok : pre m) :
    ∃ t, t ≤ budget ∧ ∃ out, post m out ∧ ∀ fuel,
      value code (A.link native) (fuel+(r+1)+t) state m = value code native fuel state out := by
  let M := A.link native
  let prefixPC : Fin (A.labels+(r+1)) ↪ Fin ((A.labels+(r+1))+p) := Fin.castAddEmb p
  let callee : Fin p ↪ Fin ((A.labels+(r+1))+p) := Fin.natAddEmb (A.labels+(r+1))
  let apc := (Fin.castAddEmb (r+1)).trans prefixPC
  let cpc := (Fin.natAddEmb A.labels).trans prefixPC
  let creg : Fin (r+1) ↪ Fin (A.registers+(r+1)) := Fin.natAddEmb A.registers
  let exit := callee native.entry
  let c := M.program.start state
  have installed : (prologue A r k).Installed M prefixPC (Function.Embedding.refl _) id exit :=
    close_installed _ _ _ _
  obtain ⟨ia,ic⟩ := (Block.seq_installed _ _ M prefixPC (Function.Embedding.refl _) id exit).mp installed
  have da (i : Fin A.slots) : M.publicData (i.castAdd k) = A.publicData i := by
    simp [M,Procedure.link,close]
  obtain ⟨t,ht,c',out,adv,hpc,hpost⟩ := spec M apc (Fin.castAddEmb (r+1))
    (Fin.castAdd k) (cpc 0) ia da c m rfl ok
  have clearRun : advance M.program (r+1) c' out = some (TickClearFrame.cleared creg exit c',out) := by
    simpa only [TickClearFrame.locations_last] using TickClearFrame.advance_clear M
      (TickClearFrame.locations cpc exit) creg
      (TickClearFrame.block_rows M cpc creg (Fin.elim0 : Fin 0 → Fin (A.slots+k)) exit ic)
      c' out (by simpa only [TickClearFrame.locations_zero] using hpc)
  refine ⟨t,ht,out,hpost,fun fuel => ?_⟩
  change mass code M.program (fuel+(r+1)+t) c m = _
  rw [mass_of_advance code _ adv (fuel+(r+1)), mass_of_advance code _ clearRun fuel]
  apply NativeRelocate.mass_eq_value callee (nativeRegs A r) (Fin.natAdd A.slots)
    native M allowed
  · intro i
    exact close_tail _ _ _ _ i
  · intro i
    simp [M,Procedure.link,close]
  · rfl
  · intro i
    exact TickClearFrame.cleared_target creg exit c' (i.castAdd 1)

/-- At one fixed total budget the unused preparation steps remain available to the callee. -/
theorem Procedure.Spec.link_fixed {A : Procedure w} {pre : Memory w → Prop}
    {post : Memory w → Memory w → Prop} {budget : ℕ} (spec : A.Spec pre post budget)
    (native : Machine w p r k) (allowed : ∀ i, NativeRelocate.ExternalOnly (native.code i))
    (code : FieldCode F w) (state : Word w) (m : Memory w) (ok : pre m) (fuel : ℕ) :
    ∃ out, post m out ∧ ∃ remaining, fuel ≤ remaining ∧ remaining ≤ fuel+budget ∧
      value code (A.link native) (fuel+(r+1)+budget) state m =
        value code native remaining state out := by
  obtain ⟨t,ht,out,hout,h⟩ := spec.link_value native allowed code state m ok
  refine ⟨out,hout,fuel+(budget-t),by omega,by omega,?_⟩
  rw [show fuel+(r+1)+budget = (fuel+(budget-t))+(r+1)+t by omega]
  exact h (fuel+(budget-t))

end ThreeFlat.RAM.PhysicalProcedure

end OAI
