import OAI.Computability.VPVNP.PairShrinkRoleSetup
import OAI.Computability.VPVNP.PairShrinkVertexLinks

/-! # Canonical DFS prefix at the selected shrinking stage -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM VertexImage Compression CompressorRecords LocalHistory
open TraversalRows TraversalRoles TraversalControllerInputs NodeArguments.ChildScan
open ShrinkVertexImage
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) {t : ℕ}
  (ord : B.Entry → Fin t) {p r w endAddr : ℕ} (M : Machine w p r 11)
  (pc : Fin (shrinkSegment B ord).count → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
  (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r) (done : Fin p)
  {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
  {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
  (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)

local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z
local notation "lr" => LocatedBody.commonLocator (active B ord) reg
private noncomputable abbrev selectorBank :=
  (VertexStageDispatch.scratchBank (fun i => (active B ord i).tailCount)).trans reg

/-- The locator and the stage switch in the fixed finite image, with no
entry assumptions on any of their temporaries. -/
theorem selectedEntry_realizes
    (installed : ∀ k, M.code (pc k) = ((shrinkSegment B ord).row pc dfs saved reg done k).resize w)
    {H first pitch offset base : ℕ} {raw m : Memory w}
    (ds : (j : Fin (passes).length) → LevelDirectory passes[j] raw base)
    (resident : Resident M.publicData m H first pitch offset B.recordLimit base
      ⟨leafLayer (siteOrder X), .cursor⟩ (levelFibers passes ds))
    (j : Fin (passes).length) (id : Fin passes[j].outputSites)
    (shrinking : tagLevel B f hf passes[j] = .shrink) (i : Fin S.steps)
    (index : passes[j].origin.ordinal = i.val)
    (fit : layerBase B.recordLimit base tags ((passes).length + 1) < 2 ^ w)
    (apart : ∀ k : Fin 9, k = 3 ∨ k = 5 ∨ k = 6 ∨ k = 7 →
      dfs k ∉ Set.range lr ∧ dfs k ∉ Set.range (selectorBank B ord reg))
    {pre post : Word w → Config w p r → Prop}
    (start : ∀ node c, pre node c → c.pc = pc (shrinkSegment B ord).entry ∧
      c.reg (dfs 7) = node ∧ node.val =
        address B.recordLimit (layerBase B.recordLimit base tags (j.val + 1)) id.val)
    (resume : ∀ node c d, pre node c → d.pc = activePC B ord i pc (active B ord i).code.entry →
      VertexLevel.Located M.publicData m lr node j.val (id.val : Word w) d →
      d.privateMem = c.privateMem → d.persistent = c.persistent →
      (∀ q, q ∉ Set.range lr → q ∉ Set.range (selectorBank B ord reg) → d.reg q = c.reg q) →
      post node d) :
    Realizes (endAddr := endAddr)
      ((locatorSetup M.publicData m (j.val + 1) ((passes).length - (j.val + 1))).seq
        (Setup.ticks (S.steps + 7 + 2 * i.val))).reader M m dfs pre (fun _ => post) := by
  apply Setup.realizes
  intro node c hc
  obtain ⟨ep,hn,addr⟩ := start node c hc
  obtain ⟨l,idx,_,d,path,entry,loc,mem,per,keep⟩ :=
    selected_entry B ord M pc dfs saved reg done installed f hf T hT X z ds resident j id
      shrinking c ep (hn ▸ addr) fit
  obtain rfl : l = i := Fin.ext (idx.symm.trans index)
  exact ⟨d,resume node c d hc entry (hn ▸ loc) mem per keep,
    ⟨fun k hk => keep _ (apart k hk).1 (apart k hk).2, fun addr _ => congrFun mem addr,per⟩,
    congrArg (DFS.scratch endAddr) mem,path⟩

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
