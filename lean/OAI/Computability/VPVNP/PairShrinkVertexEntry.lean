import OAI.Computability.VPVNP.PairShrinkVertexImage
import OAI.Computability.VPVNP.PairVertexLocatedBodyLinks
import OAI.Computability.VPVNP.PairVertexStageRun

/-!
# Entering the actual shrinking stage of a selected traversal

A popped descriptor on a shrinking level reaches the fixed stage whose degree
matches the selected pass. Its local register view reads the same located owner
and old header, even when its finite matrix bank uses a different numbering.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkVertexImage

open BurstRAM BurstRAM.PrivateRAM VertexImage Compression CompressorRecords LocalHistory
open TraversalRows TraversalRoles TraversalControllerInputs NodeArguments.ChildScan
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
    {t : ℕ} (ord : B.Entry → Fin t)

/-- The located child, hidden-field, and resident-map program for the selected elementary
shrinking step. -/
noncomputable abbrev active (i : Fin S.steps) : LocatedBody :=
  ShrinkVertexStage.stage (S.degreeExponent i.castSucc) B.shrink.selectorBits (maps B ord i)

variable {p r w : ℕ} (M : Machine w p r 11)
    (pc : Fin (shrinkSegment B ord).count → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
    (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r) (done : Fin p)
    (rows : ∀ a, M.code (pc a) = ((shrinkSegment B ord).row pc dfs saved reg done a).resize w)

include rows in
theorem active_rows (i : Fin S.steps) (j : Fin (active B ord i).code.count) :
    let dest := LocatedBody.stagePC (active B ord) pc i
    let localRegs := LocatedBody.stageBank (active B ord) reg i
    M.code (dest j) = ((active B ord i).code.row dest dfs saved localRegs done j).resize w :=
  LocatedBody.stage_rows (active B ord) M pc dfs saved reg done rows i j

theorem active_locator (i : Fin S.steps) (j : Fin 14) :
    LocatedBody.stageBank (active B ord) reg i ((active B ord i).locator j) =
      LocatedBody.commonLocator (active B ord) reg j :=
  LocatedBody.shared_locator (active B ord) reg i j

variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
    {lanes : ℕ} (T : ℕ) (hT : T * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) (z : (B.execute f hf T hT X).Choices)

local notation "passes" => executeLevels B f hf T hT X z
local notation "tags" => TraversalRoles.selected B f hf T hT X z

include rows in
/-- Reach the selected stage's first child handoff with the published descriptor and owner.
The exact trace includes the real level search and the fixed modulo dispatcher. -/
theorem selected_entry {H first pitch offset base : ℕ} {raw m : Memory w}
    (ds : (j : Fin (passes).length) → LevelDirectory passes[j] raw base)
    (resident : Resident M.publicData m H first pitch offset B.recordLimit base
      ⟨leafLayer (siteOrder X), .cursor⟩ (levelFibers passes ds))
    (j : Fin (passes).length) (id : Fin passes[j].outputSites)
    (shrinking : tagLevel B f hf passes[j] = .shrink)
    (c : Config w p r) (start : c.pc = pc (shrinkSegment B ord).entry)
    (node : (c.reg (dfs 7)).val = address B.recordLimit
      (layerBase B.recordLimit base tags (j.val + 1)) id.val)
    (fit : layerBase B.recordLimit base tags ((passes).length + 1) < 2 ^ w) :
    ∃ i : Fin S.steps, passes[j].origin.ordinal = i.val ∧
      passes[j].inputExponent = S.degreeExponent i.castSucc ∧ ∃ out,
        Prefix M m c out [] (VertexLevel.trace M.publicData m (j.val + 1)
          ((passes).length - (j.val + 1)) ++ List.replicate (S.steps + 7 + 2 * i.val) .tick) ∧
        out.pc = LocatedBody.stagePC (active B ord) pc i (active B ord i).code.entry ∧
        VertexLevel.Located M.publicData m (LocatedBody.commonLocator (active B ord) reg)
          (c.reg (dfs 7)) j.val (id.val : Word w) out ∧
        out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
        ∀ q, q ∉ Set.range (LocatedBody.commonLocator (active B ord) reg) →
          q ∉ Set.range ((VertexStageDispatch.scratchBank
            (fun i => (active B ord i).tailCount)).trans reg) →
          out.reg q = c.reg q := by
  let bodies := fun i => (active B ord i).normalized
  let tail := fun i => (active B ord i).tailCount
  let lr := (VertexStageDispatch.locatorBank tail).trans reg
  let sr := (VertexStageDispatch.scratchBank tail).trans reg
  obtain ⟨front, select, _⟩ := VertexStageDispatch.locatedFamily_link bodies dfs saved done M tail
    (fun _ => rfl) pc reg rows
  obtain ⟨mid, pre, atSelect, located, _, frame⟩ :=
    VertexLevel.selected_run B f hf T hT X z ds M _ dfs saved lr _ front resident
      j id c start node fit
  have len : (m (H + 1)).val = (passes).length + 1 := by
    simpa [levelFibers] using resident.levels
  have bound : (passes).length < 2 ^ w := by have := (m (H + 1)).isLt; omega
  have total := VertexLevel.selected_pass_count B f hf T hT X z
  have positive : 0 < T := by
    by_contra! h
    have empty : (passes).length = 0 := by rw [total, Nat.eq_zero_of_le_zero h, Nat.zero_mul]
    exact Nat.not_lt_zero _ (j.isLt.trans_eq empty)
  have periodFit : S.steps + 1 < 2 ^ w :=
    (Nat.le_mul_of_pos_left _ positive).trans_lt (total ▸ bound)
  have safe (l : Fin 14) : lr l ∉ Set.range sr := by
    rintro ⟨x, h⟩
    exact VertexStageDispatch.locator_disjoint_scratch tail l ⟨x, reg.injective h⟩
  obtain ⟨i, ordinal, exp, out, post, atBody, kept⟩ :=
    VertexStageDispatch.scheduled_run B f hf T hT X z select (safe 13) periodFit j
      (j.isLt.trans bound) shrinking mid atSelect located.stage m
  exact ⟨i, ordinal, exp, out, pre.trans post, atBody,
    VertexStageDispatch.retainLocated located (fun l => kept.regs _ (safe l)),
    kept.memory.trans frame.privateMem, kept.persistent.trans frame.persistent,
    fun q hl hs => (kept.regs q hs).trans (frame.outside q hl)⟩

end PairSimulation.ShrinkVertexImage

end VPVNP
end Computability
end OAI
