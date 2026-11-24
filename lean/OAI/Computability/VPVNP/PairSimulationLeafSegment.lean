import OAI.Computability.VPVNP.PairSimulationLeafRoleHandler
import OAI.Computability.VPVNP.PairSimulationLeafImageWork
import OAI.Computability.VPVNP.PairNativeFrameLeaf
import OAI.Computability.VPVNP.PairVertexSiteSegments

/-! # Installing the cursor leaf in the actual terminal vertex image -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafRole

open BurstRAM PrivateRAM RegisterOperands VertexImage PrimedCounter.GuessWord
open DFS CursorNetwork CursorRouting LeafStartup NativeFrame
open scoped Fin.CommRing Classical

set_option synthInstance.maxSize 10000
attribute [local irreducible] labelCount privateCount

variable {geometry rootFields shrink refresh : Segment} {p r w : ℕ}
  (V : Placement (segments geometry rootFields segment shrink refresh) p r)
  (M : Machine w p r 11)

/-- Place a numbered cursor-leaf instruction at its absolute program counter in the final
vertex image. -/
noncomputable def sitePC (j : Label) := V.stage .leaf (labelIndex j)

/-- Place the leaf's private registers in the register interval assigned to the leaf stage of
the final vertex image. -/
noncomputable def privateRegs : Private ↪ Fin r := privateIndex.toEmbedding.trans (V.localRegs .leaf)

theorem sitePC_injective : Function.Injective (sitePC V) := by
  intro i j h
  have e := V.pc.injective h
  change Sum.inr (⟨Part.leaf,labelIndex i⟩ : (s : Part) × Fin ((segments geometry rootFields segment shrink refresh s).count)) =
    Sum.inr ⟨Part.leaf,labelIndex j⟩ at e
  exact labelIndex.injective (eq_of_heq (Sigma.mk.inj (Sum.inr.inj e)).2)

theorem site_apart : Apart V.dfs (privateRegs V) := fun i j => V.reg.injective.ne (by intro h; cases h)

theorem site_contains (h : VertexImage.Contains V M) :
    Contains (sitePC V) V.dfs (privateRegs V) (site_apart V) (V.dfsPC 3) M := by
  intro j
  exact (stage_linked V M h .leaf (labelIndex j)).trans
    (congrArg (Instr.resize w) (segment_row V.dfs (V.dfsPC 3) (V.stage .leaf) V.saved
      (V.localRegs .leaf) (site_apart V) j))

variable {L : PrimedInputRAM.Lengths} {n a H s : ℕ} {Q : PrimedInputRAM.Layout L n a H w}
  (D : PrimedCounter.Data Q s) {b l e degree pad : ℕ} [NeZero (b + l)]
  (hD : 1 < b + l) (hd : 2 + pad = 2 ^ degree) (budget : ProcessorBudget n (b + l) e w)
  (m : Memory w) (header role : Word w) (arity cap clock : ℕ)

private abbrev layout := fromHeader arity M.publicData header m
private abbrev words := leafWords arity M.publicData header role m

variable (fit : (layout M m header arity).stackBase + Fintype.card ScalarPort * n ^ 40 < 2 ^ w)

/-- The physical leaf reads the actual terminal header and twelve-word
frame installed by the vertex bootstrap. The exclusive DFS end is the input
length, and both successful exits resume the child-list header. -/
theorem site_exact (link : VertexImage.Contains V M)
    (stride : (m (header + 15).val).val = cap + 2) (rb : (m (header + 18).val).val = 2 ^ b)
    (rl : (m (header + 19).val).val = 2 ^ l)
    (span : (m (header + 20).val).val = LiveAuxiliaryHeaders.span L D.hist.length)
    (shadowFit : (M.publicData 3).val + (m (header + 20).val).val ≤ 2 ^ w)
    (headers : ∀ i < (m (header + 20).val).val, (m ((M.publicData 3).val + i)).val = (D.initial i).val)
    (size : (M.publicData 6).val = n)
    (time : ∀ (v : Position (b + l)) (buf : Buffers (b + l) (2 ^ e) w),
      steps 52 (auxiliary D budget.tags budget.capFits v buf) ≤ clock)
    (room : ∀ (v : Position (b + l)) (buf : Buffers (b + l) (2 ^ e) w) j,
      (auxiliaryBank D budget.tags budget.capFits v buf j).length + clock ≤ n ^ 40) :
    let R := fromHeader arity M.publicData header m
    let data := leafWords arity M.publicData header role m
    (parser (endAddr := n) data D budget R fit m clock).ExactOn
      (Domain (e := e) data D hD hd R cap (frameBase R)) M (V.entry .leaf) (V.dfsPC 3) V.dfs m := by
  intro R data
  let pc := sitePC V
  let priv := privateRegs V
  let sep := site_apart V
  let ret := V.dfsPC 3
  let sem := verification pc V.dfs priv sep ret M data
  have assigned : sem.publicData ∘ pubSlot = data ∘ LeafGeometryLoad.slot := by
    funext j
    simp only [sem, verification, shadow, publicData, Function.comp_apply, pubSlot, Fin.addCases_left]
  obtain ⟨op, length⟩ := leaf_operands arity M.publicData header role m (enter ∘ bodyPC pc)
    (bodyReg V.dfs priv sep) pubSlot (caller ret) sem assigned D b l cap stride rb rl span shadowFit headers size
  have start : n = R.arguments.start := size.symm
  have geoLow : n ≤ frameBase R := by
    change n ≤ R.arguments.start + R.nodes * R.arguments.stride + R.histWords
    omega
  have geoFit : frameBase R + 10 ≤ 2 ^ w := by
    have high := (Nat.le_add_right R.stackBase _).trans_lt fit
    change R.histBase + R.histWords + R.otherWords + 38 < 2 ^ w at high
    change R.histBase + R.histWords + 10 ≤ 2 ^ w
    omega
  exact native_exact pc V.dfs priv sep ret M data D hD hd budget R cap (frameBase R) fit m clock
    (sitePC_injective V) (site_contains V M link) op ((congrFun assigned .size).symm.trans length)
    start.le geoLow geoFit time room

/-- Exact accounting for the geometry reload. Every source job has the same
external probes, update and choice suffix in the physical parser. -/
theorem reload_read {endAddr : ℕ} (P : HookParser w endAddr) (node : Word w) (saved : Scratch w endAddr)
    (bits tail : List Bool) (job : VisitPath w endAddr) (h : (withReload P).read node saved bits = some (job,tail)) :
    ∃ source, P.read node saved bits = some (source,tail) ∧ job.node = source.node ∧
      job.update = source.update ∧ job.trace = List.replicate 21 .tick ++ source.trace ∧
      countProbes job.trace = countProbes source.trace ∧ job.trace.length = 21 + source.trace.length := by
  obtain ⟨⟨source,rest⟩,read,e⟩ := Option.map_eq_some_iff.mp h
  cases e
  exact ⟨source,read,rfl,rfl,rfl,rfl,by rw [List.length_append]; rfl⟩

/-- The native reload leaves room for the surrounding role dispatch. -/
theorem site_work (hn : 2048 ≤ n)
    (boot : ∀ (v : Site (b + l)) (buf : Buffers (b + l) (2 ^ e) w),
      LeafBoot.ticks D budget.tags budget.capFits v buf ≤ n ^ 15)
    (node : Word w) (saved : Scratch w n) (bits tail : List Bool) (job : VisitPath w n)
    (h : (parser (words M m header role arity) D budget (layout M m header arity) fit m (n ^ 39)).read
      node saved bits = some (job,tail)) :
    countProbes job.trace ≤ 1 ∧ job.trace.length + 26 ≤ n ^ 40 := by
  let data := words M m header role arity
  let R := layout M m header arity
  let source : HookParser w n := LeafHandler.parser D budget.tags budget.capFits (LeafVisit.storage R fit)
    (LeafVisit.loaded D budget R fit (addressFields data) m) (n ^ 39)
  obtain ⟨old,hit,_,_,_,probes,ticks⟩ := reload_read source node saved bits tail job h
  let measure : Machine w 1 0 10 := ⟨0,fun _ => .reject,data⟩
  obtain ⟨p,t⟩ := LeafVisit.parser_work (M := measure) D budget R fit LeafGeometryLoad.slot m hn boot node saved bits hit
  rw [probes,ticks]; exact ⟨p,by omega⟩

end PairSimulation.LeafRole

end VPVNP
end Computability
end OAI
