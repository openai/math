import OAI.Computability.VPVNP.PairVertexStagePrefix

/-!
# The complete child prefix in the hosted shrink and refresh images
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexStagePrefix

open BurstRAM BurstRAM.PrivateRAM VertexImage NodeArguments NodeArguments.ChildScan
open Compression CompressorRecords DFS TraversalRows
open scoped Fin.CommRing

variable {p r w a g : ℕ} (body : Segment) (locator : Fin 14 ↪ Fin body.privateRegs)
    (M : Machine w p r 11) (loc : Fin (withChildren a body locator).count → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
    (reg : Fin (withChildren a body locator).privateRegs ↪ Fin r) (done : Fin p)

/-- Private register embedding for the child-argument scan preceding a located body. -/
abbrev childBank := Preparation.phaseRegs (ChildCode.RegisterBank.segment a) body reg
/-- Recover the body's shared level-locator registers through the child-preparation layout. -/
abbrev locatorRegs := locator.trans
  (Preparation.bodyRegs (ChildCode.RegisterBank.segment a) body reg)

variable {X : State a g} {T : IncidenceDirectory w} {A : Arena} {older cap : ℕ} {m : Memory w}
variable (installed : ∀ i, M.code (loc i) =
      ((withChildren a body locator).row loc dfs saved reg done i).resize w)
    (rep : T.ActualColumns X m) (xs : List (Child X)) (src : ℕ) (c : Config w p r)
    (entry : c.pc = loc (withChildren a body locator).entry)
    (stored : (directory a older cap A T).Stored m (c.reg (locatorRegs body locator reg 12)))
    (row : Row m (c.reg (locatorRegs body locator reg 0)).val src
      (xs.map fun x => (childNode X older cap x.site : Word w)))
    (strideFit : cap + 2 < 2 ^ w) (nodes : ∀ x ∈ xs, childNode X older cap x.site < 2 ^ w)
    (packets : ∀ x ∈ xs, A.base (childNode X older cap x.site) + (x.payload X).length < 2 ^ w)

private theorem setup_apart (i : Fin 16) (j : Fin 14) :
    ChildCode.RegisterBank.regs (childBank body locator reg) i ≠ locatorRegs body locator reg j :=
  Preparation.disjoint reg _ _

include installed rep entry stored row strideFit nodes packets

/-- Copy the two actual locator outputs and scan every outgoing and incoming child field.
The remaining routine's whole bank stays available after all packet writes. -/
theorem child_run :
    let qs := xs.map (Child.packet X older cap)
    let es := List.replicate 2 .tick ++ (List.replicate (2 ^ a) .tick ++
      (ChildHeader.events m (c.reg (locatorRegs body locator reg 0))
        (c.reg (locatorRegs body locator reg 12)) ++ ChildScan.events X T m src xs))
    ∃ d, d.pc = (childPreparation a body locator).bodyPC loc body.entry ∧
      d.persistent = c.persistent ∧ d.privateMem = storePackets A qs c.privateMem ∧
      (∀ endAddr, scratch endAddr d.privateMem = writePackets A qs (scratch endAddr c.privateMem)) ∧
      (∀ i, i ∉ Set.range (childBank body locator reg) → d.reg i = c.reg i) ∧
      Prefix M m c d (qs.flatMap Packet.bits) es := by
  let ps := childBank body locator reg
  let child := ChildCode.RegisterBank.regs ps
  obtain ⟨load, init, bodyCode, _⟩ := child_rows a body locator M loc dfs saved reg done installed
  obtain ⟨mid, pre, pc', hn, hf, unchanged, hm, hp⟩ :=
    VertexLevel.childHandoff_run load (setup_apart body locator reg 7 12) c entry m
  obtain ⟨d, stop, persist, mem, upper, frame, path⟩ :=
    ChildCode.RegisterBank.native_stage init bodyCode (ChildCode.RegisterBank.bank_apart ps)
      rep xs src mid pc' (hf ▸ stored) (hn ▸ row) strideFit nodes packets
  rw [hn, hf] at path
  rw [hm] at mem upper
  refine ⟨d, stop, persist.trans hp, mem, upper, ?_, pre.trans path⟩
  intro i outside
  have off (j : Fin 16) : i ≠ child j := fun h => outside ⟨_, h.symm⟩
  have noBank : i ∉ Set.range (ChildCode.RegisterBank.bank ps) :=
    fun ⟨_, h⟩ => outside ⟨_, h⟩
  have noMut : i ∉ mutableRegs child := by simp [mutableRegs, off]
  exact (frame i noBank (fun j _ => off j) noMut).trans (unchanged i (off 7) (off 8))

/-- The short-tape case rejects even when the caller supplies arbitrarily much fuel. -/
theorem child_reject (bs : List Bool) (short : bs.length < (xs.flatMap (Child.payload X)).length) :
    ¬ Returns M c m bs := by
  let ps := childBank body locator reg
  obtain ⟨load, init, bodyCode, _⟩ := child_rows a body locator M loc dfs saved reg done installed
  obtain ⟨mid, pre, pc', hn, hf, _, _, _⟩ :=
    VertexLevel.childHandoff_run load (setup_apart body locator reg 7 12) c entry m
  have no := ChildCode.RegisterBank.reject_stage init bodyCode
    (ChildCode.RegisterBank.bank_apart ps)
    rep xs src mid pc' (hf ▸ stored) (hn ▸ row) strideFit nodes packets bs short
  exact fun accepted => no ((pre.returns bs).mp accepted)

end PairSimulation.VertexStagePrefix

end VPVNP
end Computability
end OAI
