import OAI.Computability.VPVNP.CompressorShrinkGreedyPlannerSupport
import OAI.Computability.VPVNP.CompressorShrinkBundleWalk

/-! # Header reads of the dense shrinking visits

All eleven workers compute their cursor bounds and public operands from
the old level's scalars, incidence heads and first table head.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkBundlePackets

open BurstRAM Compression BlockPlanner DescriptorSpace PhaseRecipe ShrinkBundlePlan
open scoped Fin.CommRing

variable {w : ℕ} {D : ℕ → Prop} {pub : Fin 5 → Word w} {s : Word w} {m : Memory w}
local notation "R" => Expr.ReadsFrom D pub s m

private theorem visit_reads (F : Shape) (step a : ℕ) (origin : Expr)
    (vert : R (LevelFields.vertices step)) (degree : R (LevelFields.degree step))
    (lanes : R (LevelFields.lanes step)) (resid : R (LevelFields.residualLanes step))
    (inc : ∀ c : Fin 6, R (LevelFields.incidence F step c)) (base : R origin)
    (j : Scheduled.Stage) : HeaderOperands.Supported D pub s m (j.visit F step a origin) := by
  have sites : R (LevelFields.sites step) := ⟨vert,lanes⟩
  have slots : R (LevelFields.slots step) := ⟨sites,degree⟩
  have off : R (GreedyLevelPlan.offsetBase step a origin) := ⟨⟨base,vert⟩,vert,trivial⟩
  have shift : R (GreedyLevelPlan.shiftBase step a origin) := ⟨⟨off,vert⟩,vert,trivial⟩
  have pre : R (preliminary step a origin) := ⟨⟨shift,vert,degree⟩,trivial⟩
  have col (n : Fin 4) : R (placementColumn step a origin n) := ⟨pre,trivial,sites⟩
  have own : R (owner step a origin) := ⟨pre,trivial,sites⟩
  have keys : R (key step a origin) := ⟨own,slots⟩
  have cnt : R (counts step a origin) := ⟨own,trivial,slots⟩
  have b : R (bundles step a) := ⟨⟨vert,trivial,resid⟩,degree⟩
  have buckets : R (bucketCount step a) := ⟨trivial,b⟩
  have idHeads : R (ids step a origin) := ⟨cnt,buckets⟩
  have rect : R (rectangle step a) := ⟨buckets,trivial⟩
  have gather : R (gathered step a origin) := ⟨idHeads,rect⟩
  have rank : R (ranks step a origin) := ⟨gather,rect⟩
  have widths : R (sorted step a origin) := ⟨rank,slots⟩
  have block : R (blockSize step a) := ⟨b,trivial⟩
  have pref : R (prefixStart step a origin) := ⟨widths,trivial,block⟩
  have total : R (totalStart step a origin) := ⟨pref,trivial,block⟩
  have abHead : R (abStart step a origin) := ⟨total,buckets⟩
  cases j with
  | positions =>
    refine ⟨trivial,sites,?_⟩
    intro n; change Fin 14 at n; fin_cases n
    exacts [resid,trivial,degree,trivial,trivial,trivial,base,off,inc 0,inc 2,
      col 0,col 1,col 2,col 3]
  | clear => exact ⟨trivial,buckets,fun _ ↦ cnt⟩
  | classify =>
    refine ⟨trivial,slots,?_⟩
    intro n; change Fin 11 at n; fin_cases n
    exacts [degree,resid,trivial,trivial,b,inc 3,col 1,col 0,col 2,own,keys]
  | collect =>
    refine ⟨trivial,slots,?_⟩
    intro n; change Fin 6 at n; fin_cases n
    exacts [slots,own,buckets,cnt,trivial,idHeads]
  | gather =>
    refine ⟨trivial,slots,?_⟩
    intro n; change Fin 7 at n; fin_cases n
    exacts [trivial,trivial,b,trivial,idHeads,keys,gather]
  | rank =>
    refine ⟨trivial,slots,?_⟩
    intro n; change Fin 6 at n; fin_cases n
    exacts [own,keys,gather,trivial,cnt,rank]
  | scatter =>
    refine ⟨trivial,slots,?_⟩
    intro n; change Fin 5 at n; fin_cases n
    exacts [own,rank,inc 5,trivial,widths]
  | thickPrefix =>
    refine ⟨trivial,⟨b,trivial⟩,?_⟩
    intro n; change Fin 5 at n; fin_cases n
    exacts [trivial,trivial,widths,pref,total]
  | motifPrefix =>
    refine ⟨trivial,block,?_⟩
    intro n; change Fin 5 at n; fin_cases n
    exacts [trivial,trivial,⟨widths,block⟩,⟨pref,block⟩,⟨total,b⟩]
  | ab =>
    refine ⟨trivial,block,?_⟩
    intro n; change Fin 5 at n; fin_cases n
    exacts [trivial,trivial,total,abHead,⟨abHead,block⟩]
  | absolute =>
    refine ⟨trivial,slots,?_⟩
    intro n; change Fin 7 at n; fin_cases n
    exacts [own,rank,keys,trivial,gather,degree,resid]

/-- In each dense stage the pitch and the first 61 cells of the active
header suffice for all planner reads. -/
theorem expr_reads {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
    (i : Fin S.steps) {w g first start : ℕ}
    {X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g)}
    {T : IncidenceDirectory w} {L : Layout} {pub : Fin 5 → Word w} {s : Word w} {m : Memory w}
    (h : ShrinkHeaderReads.Header i X T start L first m) (entry : LevelFields.Entry L first pub s m)
    (D : ℕ → Prop) (pitch : D (pub 1 - 1).val)
    (cells : ∀ n ≤ 60, D (levelStart L (first + i.val) + n))
    (j : Scheduled.Stage) :
    HeaderOperands.Supported D pub s m (j.visit (BlockProgram.geometry B) i.val
      (ShrinkBlockInputs.a i) (BlockProgram.arena B i.val 0)) := by
  have field (n : ℕ) (hn : n ≤ 60) : (LevelFields.scalar i.val n).ReadsFrom D pub s m :=
    GreedyVisit.scalar_support D L first i.val n entry pitch (cells n hn)
      ((Nat.add_le_add_left hn _).trans_lt h.room)
  exact visit_reads (BlockProgram.geometry B) i.val (ShrinkBlockInputs.a i)
    (BlockProgram.arena B i.val 0) (field 0 (by decide)) (field 1 (by decide))
    (field 2 (by decide)) (field 3 (by decide))
    (fun c => field (54+c.val) (by have := c.isLt; omega)) (field 60 le_rfl) j

end CompressorRecords.ShrinkBundlePackets

end

end VPVNP
end Computability
end OAI
