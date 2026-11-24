import OAI.Computability.VPVNP.PairSimulationLeafRole

/-! # Exact leaf calls after loading the private geometry record -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRole

open BurstRAM PrivateRAM RegisterOperands PrimedCounter.GuessWord DFS
open scoped Classical Fin.CommRing

variable {p r w endAddr : ℕ} (pc : Label → Fin p) (dfs : Fin 9 ↪ Fin r) (priv : Private ↪ Fin r)
  (apart : Apart dfs priv) (ret : Fin p) (A : Machine w p r 11) (data : Fin 10 → Word w)

private theorem public_ok (i : Fin 11) : publicData A data (Fin.natAdd 10 i) = A.publicData i :=
  Fin.addCases_right ..

/-- No verifier body instruction writes to any of the ten registers containing the loaded
geometry operands. -/
def PreservesOperands : Prop :=
  ∀ j : LeafImage.Label, ∀ i : Fin 10, destination (body pc dfs priv apart ret j) ≠ some (values priv i)

private theorem frame (inj : Function.Injective pc) (keep : PreservesOperands pc dfs priv apart ret)
    (q : Fin p) (inside' : inside pc q) (n : Fin (10+11)) (a : Fin r)
    (eqn : operands priv n = .register a) :
    destination (text (w := w) pc dfs priv apart ret q) ≠ some a := by
  rcases inside' with ⟨j,rfl⟩
  rw [text_at pc dfs priv apart ret inj j,destination_resize]
  revert eqn
  refine Fin.addCases (fun i => ?_) (fun i => ?_) n
  · simp only [operands,Fin.addCases_left,Operand.register.injEq]
    rintro rfl; exact keep j i
  · simp [operands]

theorem execute_body (inj : Function.Injective pc) (h : Contains pc dfs priv apart ret A)
    (keep : PreservesOperands pc dfs priv apart ret) (c : Config w p r)
    (ready : ∀ i, c.reg (values priv i) = data i) (fuel : ℕ) (m : Memory w) (bits : List Bool) :
    execute (verification pc dfs priv apart ret A data).program fuel (enterConfig c) m bits =
      execute A.program fuel c m bits :=
  execute_enter A (inside pc) (text pc dfs priv apart ret) (publicData A data) (Fin.natAdd 10)
    (public_ok A data) (operands priv) (physical_rows pc dfs priv apart ret A inj h)
    (frame pc dfs priv apart ret inj keep) c (agreement priv A data c ready) fuel m bits

theorem execute_return {c : Config w (p+p) r} (hr : c.pc = caller ret)
    (fuel : ℕ) (m : Memory w) (bits : List Bool) :
    execute (verification pc dfs priv apart ret A data).program fuel c m bits =
      execute A.program fuel (project c) m bits :=
  execute_caller_of_pc A (inside pc) (text pc dfs priv apart ret) (publicData A data) (Fin.natAdd 10)
    (public_ok A data) c hr fuel m bits

private def ticks (w : ℕ) := List.replicate 21 (.tick : Event w)

private theorem ticks_bits : choiceBits (ticks w) = [] := rfl

/-- Include the reload's twenty-one ticks in the actual visit. The read job is
enabled at the scratch image from which it was decoded. -/
def withReload (P : HookParser w endAddr) : HookParser w endAddr where
  read node saved bits := (P.read node saved bits).map fun (job,tail) =>
    (⟨job.node,ticks w ++ job.trace,fun s => s = saved ∧ job.enabled s,job.update⟩,tail)

private theorem reload {c : Config w p r} (h : Contains pc dfs priv apart ret A)
    (base : ℕ) (saved : LeafGeometryLoad.Stored endAddr base c.privateMem data)
    (entry : c.pc = loadPC pc (.inl ())) (endReg : c.reg (dfs 6) = (endAddr : Word w))
    (one : c.reg (dfs 3) = 1) :
    ∃ ready, Prefix A c (ticks w) ready ∧ ready.pc = bodyPC pc (.address 0) ∧
      (∀ i, ready.reg (values priv i) = data i) ∧ ready.privateMem = c.privateMem ∧
      ready.persistent = c.persistent ∧ ∀ i, ready.reg (dfs i) = c.reg (dfs i) := by
  obtain ⟨out,path,entry',ready,mem,state,other⟩ := LeafGeometryLoad.run (loadPC pc) dfs (ports priv)
    (priv .cursor) (bodyPC pc (.address 0)) A (load_linked pc dfs priv apart ret h) endAddr base data c entry
    endReg one saved (fun j => priv.injective.ne (by intro e; cases e)) (fun j => apart _ _) (apart _ _)
  exact ⟨out,path,entry',ready,mem,state,fun i => other _ (apart i _) (fun _ => apart i _)⟩

open private returns_prefix from OAI.Computability.VPVNP.PairSimulationDFSDecode

/-- Transfer the proved semantic parser to the actual eleven-operand image.
The continuation may execute arbitrary instructions and may revisit this
descriptor with different registers and a new choice suffix. -/
theorem exact (inj : Function.Injective pc) (h : Contains pc dfs priv apart ret A)
    (keep : PreservesOperands pc dfs priv apart ret) (P : HookParser w endAddr)
    (domain : Word w → Scratch w endAddr → Prop) (base : ℕ) (m : Memory w)
    (stored : ∀ node (c : Config w p r), domain node (scratch endAddr c.privateMem) →
      LeafGeometryLoad.Stored endAddr base c.privateMem data)
    (semantic : P.ExactOn domain (verification pc dfs priv apart ret A data)
      (enter (bodyPC pc (.address 0))) (caller ret) dfs m) :
    (withReload P).ExactOn domain A (loadPC pc (.inl ())) ret dfs m := by
  have eval := execute_body pc dfs priv apart ret A data inj h keep
  constructor
  · intro node saved domain' bits actual tail read
    obtain ⟨⟨job,rest⟩,source,e⟩ := Option.map_eq_some_iff.mp read
    cases e
    obtain ⟨hn,enabled,split,call⟩ := semantic.success node saved domain' bits job _ source
    refine ⟨hn,⟨rfl,enabled⟩,?_,?_⟩
    · simpa only [PrimedInputRAM.Flow.choiceBits_append,ticks_bits,List.nil_append] using split
    · intro c top pending enabled' entry nodeAt stack limit topAt endAt one
      obtain ⟨eqn,jobEnabled⟩ := enabled'
      have cached := stored node c (eqn ▸ domain')
      obtain ⟨ready,pre,readyPC,bank,mem,state,regs⟩ := reload pc dfs priv apart ret A data h base cached entry endAt one
      obtain ⟨out,done,nodeDone,topDone,endDone,oneDone,stateDone,stackDone,scratchDone,exec⟩ :=
        call (enterConfig ready) top pending (mem ▸ jobEnabled) (congrArg enter readyPC)
          ((regs 7).trans nodeAt) (mem ▸ stack) limit ((regs 5).trans topAt) ((regs 6).trans endAt) ((regs 3).trans one)
      refine ⟨project out,?_,nodeDone,topDone,endDone,oneDone,stateDone.trans state,stackDone,?_,?_⟩
      · change fold out.pc = ret; rw [done,fold_caller]
      · exact scratchDone.trans (congrArg (job.update ∘ scratch endAddr) mem)
      · intro fuel bs
        change execute A.program (fuel+(ticks w ++ job.trace).length) c m (choiceBits (ticks w ++ job.trace) ++ bs) = _
        rw [List.length_append, show fuel + ((ticks w).length+job.trace.length) =
          (fuel+job.trace.length)+(ticks w).length by omega]
        simp only [PrimedInputRAM.Flow.choiceBits_append,ticks_bits,List.nil_append]
        have hp := pre.execute (fuel+job.trace.length) m (choiceBits job.trace ++ bs)
        simp only [ticks_bits,List.nil_append] at hp
        rw [hp,← eval ready bank,exec,execute_return pc dfs priv apart ret A data done]
        simp [Option.map_map,Function.comp_def,List.append_assoc]
  · intro node bits c top pending dom entry nodeAt stack limit topAt endAt one read
    have bad : P.read node (scratch endAddr c.privateMem) bits = none := by
      simpa only [withReload,Option.map_eq_none_iff] using read
    obtain ⟨ready,pre,readyPC,bank,mem,_,regs⟩ := reload pc dfs priv apart ret A data h base (stored node c dom) entry endAt one
    have deny := semantic.reject node bits (enterConfig ready) top pending (mem ▸ dom) (congrArg enter readyPC)
      ((regs 7).trans nodeAt) (mem ▸ stack) limit ((regs 5).trans topAt) ((regs 6).trans endAt) ((regs 3).trans one)
      (mem ▸ bad)
    intro ok
    have after := (returns_prefix (fun fuel => by
      simpa only [ticks_bits,List.nil_append] using pre.execute fuel m bits)).mp ok
    obtain ⟨fuel,rep,accept⟩ := after
    exact deny ⟨fuel,rep,(eval ready bank fuel m bits).trans accept⟩

end PairSimulation.LeafRole

end VPVNP
end Computability
end OAI
