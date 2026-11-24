import OAI.Computability.VPVNP.PairShrinkRoleSelectedEntry
import OAI.Computability.VPVNP.PairShrinkRoleBankChild
import OAI.Computability.VPVNP.PairVertexStageChildren

/-!
# Physical child argument scan in the fixed shrinking image

The selected substep first copies the node and old directory pointer, builds
its slot-ordinal register bank, and reads the child arguments. Every register
outside that segment's bank is preserved, including the shared level locator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM VertexImage Compression CompressorRecords
open ShrinkVertexImage VertexStagePrefix NodeArguments NodeArguments.ChildScan

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) {t : ℕ}
  (ord : B.Entry → Fin t) (i : Fin S.steps) {p r w g endAddr : ℕ} (M : Machine w p r 11)
  (pc : Fin (shrinkSegment B ord).count → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
  (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r) (done : Fin p)
  (installed : ∀ k, M.code (pc k) = ((shrinkSegment B ord).row pc dfs saved reg done k).resize w)

/-- The concrete register embedding for the old-child argument scan within the selected shrink
stage. -/
noncomputable abbrev argumentBank :=
  childBank (afterChildren B ord i).code (afterChildren B ord i).locator (activeBank B ord i reg)

variable (X : State (S.degreeExponent i.castSucc) g)
  (A : Arena) (T : IncidenceDirectory w) (m : Memory w) (older cap : ℕ)
  (desc : Word w → ChildArguments.Descriptor w X)

/-- This is the trace of the physical child prefix in a scheduled stage. -/
noncomputable def imageChildren : Reader w endAddr (List (Child X)) :=
  bind (Setup.ticks 2).reader fun _ => BankChild.reader A T m older cap desc

include installed in
/-- Exact local execution, including partial tapes, on the installed child
code. The inputs are the located words and actual rows, and the continuation
gets the complete packet writes as a function of its original memory. -/
theorem imageChildren_realizes
    (apart : ∀ j : Fin 9, j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 7 →
      ∀ q, dfs j ≠ argumentBank B ord i reg q)
    (rep : T.ActualColumns X m) (strideFit : cap + 2 < 2 ^ w)
    {pre : Word w → Config w p r → Prop} {post : List (Child X) → Word w → Config w p r → Prop}
    (start : ∀ node c, pre node c → c.pc = activePC B ord i pc (active B ord i).code.entry ∧
      c.reg (LocatedBody.commonLocator (active B ord) reg 0) = node ∧
      c.reg (LocatedBody.commonLocator (active B ord) reg 12) = (desc node).directoryBase ∧
      ChildArguments.Resident A T m older cap endAddr node (desc node))
    (resume : ∀ node c d xs, pre node c → xs.map Child.site = (desc node).sites →
      d.pc = afterChildPC B ord i pc (afterChildren B ord i).code.entry →
      d.persistent = c.persistent →
      d.privateMem = storePackets A (xs.map (Child.packet X older cap)) c.privateMem →
      (∀ j, j ∉ Set.range (argumentBank B ord i reg) → d.reg j = c.reg j) → post xs node d) :
    Realizes (imageChildren (endAddr := endAddr) i X A T m older cap desc) M m dfs pre post := by
  let prep := childPrep B ord i
  let place := activePC B ord i pc
  let localRegs := activeBank B ord i reg
  let bank := argumentBank B ord i reg
  let loc := locatorRegs (afterChildren B ord i).code (afterChildren B ord i).locator localRegs
  let child := ChildCode.RegisterBank.regs bank
  have loc_eq (j : Fin 14) : loc j = LocatedBody.commonLocator (active B ord) reg j :=
    active_locator B ord reg i j
  have code := active_rows B ord M pc dfs saved reg done installed i
  have hand := (child_rows (oldExponent i) (afterChildren B ord i).code
    (afterChildren B ord i).locator M place dfs saved localRegs done code).1
  obtain ⟨_,body,_⟩ := prep.links M place dfs saved localRegs done code
  let next := prep.phasePC place (ChildCode.RegisterBank.segment (oldExponent i)).entry
  let mid (node : Word w) (d : Config w p r) := d.pc = next ∧ d.reg (child 7) = node ∧
    d.reg (child 8) = (desc node).directoryBase ∧
    ChildArguments.Resident A T m older cap endAddr node (desc node) ∧
    ∃ c, pre node c ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
      ∀ j, j ∉ Set.range bank → d.reg j = c.reg j
  have before : Realizes (Setup.ticks (endAddr := endAddr) 2).reader M m dfs pre
      (fun _ => mid) := by
    apply childHandoff_realizes hand
    · exact Preparation.disjoint localRegs _ _
    · exact fun j hj => ⟨apart j hj _, apart j hj _⟩
    · exact fun node c hc => (start node c hc).1
    · intro node c d hc atNext hn hd keep mem pers
      obtain ⟨_,hNode,hDir,resident⟩ := start node c hc
      refine ⟨atNext,hn.trans ((loc_eq 0) ▸ hNode),hd.trans ((loc_eq 12) ▸ hDir),resident,
        c,hc,mem,pers,?_⟩
      exact fun j free => keep j (fun h => free ⟨_,h.symm⟩) (fun h => free ⟨_,h.symm⟩)
  apply before.bind
  intro _
  apply BankChild.realizes (prep.phasePC place) saved bank _ body apart rep strideFit
  · exact fun _ _ h => ⟨h.1,h.2.1,h.2.2.1,h.2.2.2.1⟩
  · intro node d out xs hd sites exit per mem keep
    obtain ⟨c,hc,dm,ds,beforeRegs⟩ := hd.2.2.2.2
    exact resume node c out xs hc sites exit (per.trans ds) (dm ▸ mem)
      (fun j free => (keep j free).trans (beforeRegs j free))

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
