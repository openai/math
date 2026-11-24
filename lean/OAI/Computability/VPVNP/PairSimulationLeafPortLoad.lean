import OAI.Computability.VPVNP.PairSimulationLeafRegisterBank
import OAI.Computability.VPVNP.PairSimulationLeafFieldStage

/-! # Linking the operand staging and scalar loops at each virtual-validator port -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRegisterBank

open BurstRAM PrivateRAM PrimedCounter.GuessWord RAMTape LeafStartup StackMachine
open scoped Fin.CommRing

variable {d e w k p r pubs : ℕ} {K : Type} [DecidableEq K]

/-- The incident stack stays empty until its four supplied half-wire buffers are decoded. -/
def scalarField (f : Field k) : Field k := if f = .incident then .blank else f

theorem scalarField_ne (f : Field k) : scalarField f ≠ .incident := by by_cases h : f = .incident <;> simp [scalarField,h]

/-- Choose tally loading for unary counts and empty fields, and binary loading for word-valued
fields. -/
def mode : Field k → LeafScalarLoad.Mode
  | .blank | .incident | .addressWidth | .width | .slots | .bucket | .fuel | .siteCredit | .choices => .tally
  | _ => .binary

theorem mode_eq (x : VirtualSite.Input d e w) (args : Fin k → Word w) (f : Field k) :
    mode f = (source x args f).1 := by cases f <;> rfl

omit [DecidableEq K] in
theorem preserveSources (reg : Reg K k ↪ Fin r) (x : VirtualSite.Input d e w) (args : Fin k → Word w)
    (old new : Config w p r) (ready : Staging.Sources x args (old.reg ∘ stage reg))
    (hz : new.reg (stack reg .zero) = 0) (ho : new.reg (stack reg .one) = 1)
    (frame : ∀ j : Source k, new.reg (reg (.inr j)) = old.reg (reg (.inr j))) :
    Staging.Sources x args (new.reg ∘ stage reg) :=
  ⟨hz,ho,(frame .d).trans ready.d,(frame .width).trans ready.width,(frame .bucket).trans ready.bucket,
    (frame .fuel).trans ready.fuel,(frame .address).trans ready.address,(frame .initial).trans ready.initial,
    (frame .header).trans ready.header,fun i => (frame (.operand i)).trans (ready.operand i)⟩

/-- Prepare the length and value using native rows, then write the represented
stack directly at the pointer initialized for this port. The public source
registers are available to the next port. -/
theorem scalar_run (x : VirtualSite.Input d e w) (args : Fin k → Word w) (f : Field k)
    (hf : f ≠ .incident) (M : Machine w p r pubs) (reg : Reg K k ↪ Fin r) (L : Layout K w) (a : K)
    (stagePC : Fin ((Staging.code f).length+1) → Fin p) (fillPC : Fin 6 → Fin p) (done : Fin p)
    (joinPC : stagePC (Fin.last (Staging.code f).length) = fillPC 0)
    (stageRows : ∀ i : Fin (Staging.code f).length, M.code (stagePC i.castSucc) =
      Staging.instruction (stage reg) (stagePC i.succ) (Staging.code f)[i])
    (fillRows : LeafScalarLoad.Linked M (mode f) fillPC (LeafFill.fieldRegisters (load reg) a) done)
    (c : Config w p r) (hc : c.pc = stagePC 0) (s : Stacks K) (rep : Represents L (stack reg) c s)
    (ready : Staging.Sources x args (c.reg ∘ stage reg)) (empty : s a = [])
    (fit : ∀ j, (s j).length ≤ L.capacity) (room : (fieldBits x args f).length ≤ L.capacity) :
    let xs := fieldBits x args f
    ∃ out, Prefix M c (List.replicate ((Staging.code f).length+(6*xs.length+1)) .tick) out ∧
      out.pc = done ∧ Represents L (stack reg) out (Function.update s a xs) ∧
      Staging.Sources x args (out.reg ∘ stage reg) ∧ out.persistent = c.persistent ∧
      (∀ i, i ∉ Set.range reg → out.reg i = c.reg i) ∧
      ∀ u, u.val < L.base a ∨ L.base a+xs.length ≤ u.val → out.privateMem u = c.privateMem u := by
  intro xs
  let ls := Staging.code f
  let mid : Config w p r := {c with pc := stagePC (Fin.last ls.length), reg := ls.foldl (Staging.applyPhysical (stage reg)) c.reg}
  have staged : Prefix M c (List.replicate ls.length .tick) mid :=
    Staging.run M (stage reg) ls stagePC stageRows c hc
  have midrep := staged_represents reg L s ls mid.pc c rep
  change Represents L (stack reg) mid s at midrep
  let v := source x args f
  have spec := scalarSpec x args f hf
  change LeafScalarLoad.payload v.1 v.2.2 v.2.1 = xs.reverse at spec
  have len := congrArg List.length spec
  simp only [LeafScalarLoad.payload_length,List.length_reverse] at len
  have words := Staging.stagedWords x args (c.reg ∘ stage reg) ready f
  have physical := Staging.physical_at (stage reg) ls c.reg
  have hlen : mid.reg (load reg .length) = (xs.length : Word w) := by
    refine ((congrFun physical (.out .len)).trans words.1).trans ?_
    exact congrArg (fun n : ℕ => (n : Word w)) len
  have hval : mid.reg (load reg .value) = v.2.2 := (congrFun physical (.out .value)).trans words.2
  have bitSpec : LeafScalarLoad.payload (mode f) v.2.2 xs.length = xs.reverse := by
    rw [← len,mode_eq x args]; exact spec
  obtain ⟨out,loaded,hpc,hrep,hstate,fr,mem⟩ :=
    LeafFill.install_scalar L (load reg) a s xs v.2.2 mid fillRows (by have := x.hw; omega) joinPC
      midrep empty fit room hlen hval bitSpec
  have hr := staged.append loaded
  rw [← List.replicate_add] at hr
  have preservedOuter (i : Fin r) (hl : i ∉ Set.range (load reg)) (hs : ∀ o, i ≠ stage reg (.out o)) :
      out.reg i = c.reg i :=
    (fr i hl).trans (Staging.physical_outside (stage reg) ls c.reg i hs)
  refine ⟨out,hr,hpc,hrep,preserveSources reg x args c out ready hrep.zero hrep.unit ?_,hstate,?_,mem⟩
  · intro j
    apply preservedOuter
    · rintro ⟨i,he⟩; simp at he
    · intro o; cases o <;> simp [stagingName]
  · intro i hi
    apply preservedOuter
    · rintro ⟨j,he⟩; exact hi ⟨.inl j,he⟩
    · exact fun o he => hi ⟨stagingName (.out o),he.symm⟩

end PairSimulation.LeafRegisterBank

end VPVNP
end Computability
end OAI
