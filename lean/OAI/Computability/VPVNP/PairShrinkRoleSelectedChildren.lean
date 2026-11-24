import OAI.Computability.VPVNP.PairShrinkRoleImageChildren
import OAI.Computability.VPVNP.PairShrinkRoleBind

/-! # Reading the child packets of a selected shrinking site -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM VertexImage Compression CompressorRecords LocalHistory
open NodeArguments NodeArguments.ChildScan TraversalRows TraversalRoles TraversalControllerInputs
open ShrinkVertexImage VertexStagePrefix
open scoped Fin.CommRing

variable {w endAddr : ℕ}

/-- The located level selects a degree, after which the node and old directory
are copied and the ordinal registers filled in order. -/
def selectedChildSetup (pub : Fin 11 → Word w) (m : Memory w) (levels old steps stage a : ℕ) :
    Setup w endAddr :=
  (((locatorSetup pub m (old + 1) (levels - (old + 1))).seq
    (Setup.ticks (steps + 7 + 2 * stage))).seq (Setup.ticks 2)).seq (Setup.ticks (2 ^ a))

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) {t : ℕ}
  (ord : B.Entry → Fin t) {p r : ℕ} (M : Machine w p r 11)
  (pc : Fin (shrinkSegment B ord).count → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
  (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r) (done : Fin p)
  {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
  {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
  (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)

local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "lr" => LocatedBody.commonLocator (active B ord) reg
private noncomputable abbrev switchRegs :=
  (VertexStageDispatch.scratchBank (fun i => (active B ord i).tailCount)).trans reg
local notation "sr" => switchRegs B ord reg

/-- The descriptor, geometry register and located old header survive the complete
child scan. Both the sites and the private packet writes are the ones actually parsed. -/
theorem selectedChildren_realizes
    (installed : ∀ k, M.code (pc k) = ((shrinkSegment B ord).row pc dfs saved reg done k).resize w)
    {H first pitch offset base : ℕ} {raw m : Memory w}
    (ds : (j : Fin (passes).length) → LevelDirectory passes[j] raw base)
    (resident : Resident M.publicData m H first pitch offset B.recordLimit base
      ⟨leafLayer (siteOrder X), .cursor⟩ (levelFibers passes ds))
    (j : Fin (passes).length) (id : Fin passes[j].outputSites)
    (shrinking : tagLevel B f hf passes[j] = .shrink) (i : Fin S.steps)
    (index : passes[j].origin.ordinal = i.val)
    (fit : layerBase B.recordLimit base tags ((passes).length + 1) < 2 ^ w)
    (separate : ∀ k : Fin 9, k = 3 ∨ k = 5 ∨ k = 6 ∨ k = 7 → ∀ l, dfs k ≠ reg l)
    {g : ℕ} (Z : State (oldExponent i) g) (A : Arena) (inc : IncidenceDirectory w)
    (older : ℕ) (desc : Word w → ChildArguments.Descriptor w Z)
    (rep : inc.ActualColumns Z m) (strideFit : B.recordLimit + 2 < 2 ^ w)
    {pre : Word w → Config w p r → Prop} {post : List (Child Z) → Word w → Config w p r → Prop}
    (start : ∀ node c, pre node c → c.pc = pc (shrinkSegment B ord).entry ∧
      c.reg (dfs 7) = node ∧ node.val =
        address B.recordLimit (layerBase B.recordLimit base tags (j.val + 1)) id.val)
    (directory : ∀ node c, pre node c →
      (desc node).directoryBase = levelHead M.publicData m j.val + 14 ∧
      ChildArguments.Resident A inc m older B.recordLimit endAddr node (desc node))
    (resume : ∀ node c d xs, pre node c → xs.map Child.site = (desc node).sites →
      d.pc = afterChildPC B ord i pc (afterChildren B ord i).code.entry →
      VertexLevel.Located M.publicData m lr node j.val (id.val : Word w) d →
      d.reg (dfs 6) = c.reg (dfs 6) → d.persistent = c.persistent →
      d.privateMem = storePackets A (xs.map (Child.packet Z older B.recordLimit)) c.privateMem →
      post xs node d) :
    Realizes (endAddr := endAddr) (bind
      (selectedChildSetup M.publicData m (passes).length j.val S.steps i.val (oldExponent i)).reader
      fun _ => ChildArguments.reader A inc m older B.recordLimit desc) M m dfs pre post := by
  let mid (node : Word w) (d : Config w p r) : Prop :=
    d.pc = activePC B ord i pc (active B ord i).code.entry ∧
    VertexLevel.Located M.publicData m lr node j.val (id.val : Word w) d ∧
    ∃ c, pre node c ∧ d.reg (dfs 6) = c.reg (dfs 6) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent
  have away (k : Fin 9) (hk : k = 3 ∨ k = 5 ∨ k = 6 ∨ k = 7) :
      dfs k ∉ Set.range lr ∧ dfs k ∉ Set.range sr :=
    ⟨fun ⟨_, h⟩ => separate k hk _ h.symm, fun ⟨_, h⟩ => separate k hk _ h.symm⟩
  have first := selectedEntry_realizes B ord M pc dfs saved reg done f hf T hT X z
    (endAddr := endAddr) installed ds resident j id shrinking i index fit away start
    (post := mid) (fun _ c _ hc ep located mem pers keep =>
      ⟨ep, located, c, hc, keep _ (away 6 (by decide)).1 (away 6 (by decide)).2, mem, pers⟩)
  have free (l : Fin 14) : lr l ∉ Set.range (argumentBank B ord i reg) := by
    rintro ⟨k, h⟩
    exact Preparation.disjoint (activeBank B ord i reg) k ((afterChildren B ord i).locator l)
      (h.trans (active_locator B ord reg i l).symm)
  have child : Realizes (endAddr := endAddr)
      (imageChildren i Z A inc m older B.recordLimit desc) M m dfs mid post := by
    apply imageChildren_realizes B ord i M pc dfs saved reg done installed Z A inc m older
      B.recordLimit desc (fun k hk _ => separate k hk _) rep strideFit
    · intro node d hd
      obtain ⟨ep, loc, c, hc, _⟩ := hd
      obtain ⟨dir, resident⟩ := directory node c hc
      exact ⟨ep, loc.state.node, loc.oldFields.trans dir.symm, resident⟩
    · intro node d out xs hd sites ep pers mem keep
      obtain ⟨_, loc, c, hc, endEq, dm, dp⟩ := hd
      exact resume node c out xs hc sites ep
        (VertexStageDispatch.retainLocated loc (fun l => keep _ (free l)))
        ((keep _ (fun ⟨_, h⟩ => separate 6 (by decide) _ h.symm)).trans endEq)
        (pers.trans dp) (dm ▸ mem)
  simpa only [selectedChildSetup, Setup.seq_reader, bind_assoc, imageChildren, BankChild.reader]
    using first.bind (fun _ => child)

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
