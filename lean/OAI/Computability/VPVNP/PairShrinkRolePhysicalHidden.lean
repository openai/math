import OAI.Computability.VPVNP.PairShrinkRoleCachedSetup
import OAI.Computability.VPVNP.PairShrinkRoleHeaderSetup
import OAI.Computability.VPVNP.PairShrinkRoleHidden
import OAI.Computability.VPVNP.PairShrinkVertexLinks

/-!
# The absorbed-field scan in the selected shrinking stage

The handoff saves the live hidden-field base in the shared locator bank.
The header reads the selected old level and passes its directory to the
guess loop. These two stages leave the entry scratch intact. The loop
writes precisely the decoded fields and returns to the map reload.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM ShrinkHiddenGuess VertexImage VertexStagePrefix
open Compression CompressorRecords ShrinkVertexImage
open scoped Fin.CommRing

variable {w p r endAddr : ℕ}

/-- The geometry and located old level at the end of the child scan. -/
structure PhysicalHiddenEntry (entry : Fin p) (dfs : Fin 9 ↪ Fin r) (loc : Fin 14 ↪ Fin r)
    (g : Args w) (oldHead : ℕ) (c : Config w p r) : Prop where
  pc : c.pc = entry
  owner : c.reg (loc 7) = (g.owner : Word w)
  oldLevel : c.reg (loc 11) = (oldHead : Word w)
  base : let G := c.privateMem (c.reg (dfs 6))
         VertexLevel.hiddenBaseWord (c.privateMem (G + 8)) (c.privateMem (G + 9)) =
           (g.scratchBase : Word w)
  stride : let G := c.privateMem (c.reg (dfs 6))
           let n := c.privateMem (G + 9)
           n * n = (g.slotStride : Word w)

/-- The setup trace consists of the handoff ticks and the real compiler's
five reads of the old level. -/
noncomputable def physicalHiddenSetup (s t oldHead : ℕ) (m : Memory w) : Setup w endAddr :=
  (Setup.ticks (VertexLevel.hiddenCount + 1)).seq (hiddenHeader s t oldHead m)

private theorem setup_realizes_core {M : Machine w p r 11} {m : Memory w} (s t : ℕ)
    (hp : Fin (VertexLevel.hiddenCount + 1) → Fin p)
    (phasePC : Fin (Table.segmentCount s t) → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r) (loc : Fin 14 ↪ Fin r)
    (prv : Fin (Table.R s t) ↪ Fin r) (ret : Fin p) (g : Args w) (oldHead : ℕ)
    (load : ∀ j, M.code (hp j.castSucc) = VertexLevel.hiddenHandoff (hp ∘ Fin.castSucc) loc
      ((Table.segmentInputs s t).trans prv) (dfs 6) (hp (Fin.last VertexLevel.hiddenCount)) j)
    (copy : M.code (hp (Fin.last VertexLevel.hiddenCount)) = .copy (loc 8)
      (prv (Table.segmentInputs s t 1)) (phasePC (Table.segment s t).entry))
    (phase : ∀ j, M.code (phasePC j) =
      ((Table.segment s t).row phasePC dfs saved prv ret j).resize w)
    (freeLoc : ∀ j, loc j ∉ Set.range prv)
    (safe : ∀ j : Fin 9, j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 7 → dfs j ≠ loc 8 ∧ dfs j ∉ Set.range prv)
    (selectors : g.selectorBits = (s : Word w)) (pitch : g.rowStride = t)
    (fit : oldHead + 38 < 2 ^ w) (headers : Header.Published g oldHead m)
    {pre post : Word w → Config w p r → Prop}
    (start : ∀ node c, pre node c → PhysicalHiddenEntry (hp 0) dfs loc g oldHead c)
    (finish : ∀ node c d, pre node c → d.pc = Table.segmentLoop s t phasePC (.inl .one) →
      Inputs g ((Table.regs s t).trans prv) d → d.reg (loc 8) = (g.scratchBase : Word w) →
      d.privateMem = c.privateMem → d.persistent = c.persistent →
      (∀ q, q ≠ loc 8 → q ∉ Set.range prv → d.reg q = c.reg q) → post node d) :
    Realizes (physicalHiddenSetup (endAddr := endAddr) s t oldHead m).reader M m dfs
      pre (fun _ => post) := by
  let src := (Table.segmentInputs s t).trans prv
  let mid (node : Word w) (d : Config w p r) : Prop :=
    d.pc = phasePC (Table.segment s t).entry ∧ Table.SegmentOperands s t prv g oldHead d ∧
    d.reg (loc 8) = (g.scratchBase : Word w) ∧ ∃ c, pre node c ∧ d.privateMem = c.privateMem ∧
      d.persistent = c.persistent ∧ ∀ q, q ≠ loc 8 → q ∉ Set.range prv → d.reg q = c.reg q
  have boot : Realizes (Setup.ticks (endAddr := endAddr) (VertexLevel.hiddenCount + 1)).reader
      M m dfs pre (fun _ => mid) := by
    apply cachedHiddenHandoff_realizes (pre := pre) (post := mid) (pc := hp) (inputs := src)
      load copy (fun a b e => freeLoc b ⟨Table.segmentInputs s t a, e⟩)
      (fun j hj => ⟨(safe j hj).1, fun k e => (safe j hj).2 ⟨Table.segmentInputs s t k, e.symm⟩⟩)
      (fun node c hc => (start node c hc).pc)
    intro node c d hc G n atHead owner base stride level cached keep mem pers
    have ready := start node c hc
    refine ⟨atHead, ⟨level.trans ready.oldLevel, owner.trans ready.owner,
      base.trans ready.base, stride.trans ready.stride⟩, cached.trans (base.trans ready.base),
      c, hc, mem, pers, ?_⟩
    intro q ne outside
    have free (k : Fin 6) : q ≠ src k := fun e => outside ⟨Table.segmentInputs s t k, e.symm⟩
    exact keep q ne (free 0) (free 1) (free 2) (free 5)
  apply Setup.seq_realizes (b := hiddenHeader s t oldHead m) boot
  apply hiddenHeader_realizes (pre := mid) (post := post) s t phasePC dfs saved prv ret phase g
    oldHead selectors pitch fit headers
    (fun j hj ⟨k, eqn⟩ => (safe j hj).2 ⟨Table.vm s t k, eqn⟩) (fun _ _ h => ⟨h.1, h.2.1⟩)
  intro node d z hd atLoop values mem pers keep
  obtain ⟨_, _, cached, c, hc, dm, dp, kept⟩ := hd
  have frame (q : Fin r) (outside : q ∉ Set.range prv) : z.reg q = d.reg q :=
    keep q fun ⟨k, eqn⟩ => outside ⟨Table.vm s t k, eqn⟩
  exact finish node c z hc atLoop values ((frame _ (freeLoc 8)).trans cached)
    (mem.trans dm) (pers.trans dp) (fun q hq outside => (frame q outside).trans (kept q hq outside))

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
  {t : ℕ} (ord : B.Entry → Fin t) (i : Fin S.steps) (M : Machine w p r 11)
  (pc : Fin (shrinkSegment B ord).count → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
  (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r) (done : Fin p)
  (installed : ∀ j, M.code (pc j) = ((shrinkSegment B ord).row pc dfs saved reg done j).resize w)
  (separate : ∀ j : Fin 9, j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 7 → ∀ k, dfs j ≠ reg k)
  (m : Memory w) (g : Args w) (oldHead : ℕ)
  (selectors : g.selectorBits = (B.shrink.selectorBits : Word w))
  (pitch : g.rowStride = hiddenStride i) (fit : oldHead + 38 < 2 ^ w)
  (headers : Header.Published g oldHead m)
  {pre : Word w → Config w p r → Prop}

attribute [local irreducible] ShrinkVertexImage.maps

local notation "s" => B.shrink.selectorBits
local notation "t₀" => hiddenStride i
local notation "lr" => LocatedBody.commonLocator (active B ord) reg
local notation "prv" => hiddenRegs B ord i reg
local notation "locPC" => hiddenPC B ord i pc
private noncomputable abbrev preparationPC (j : Fin (VertexLevel.hiddenCount + 1)) : Fin p :=
  (hiddenPrep B ord i).setupPC (afterChildPC B ord i pc) j
local notation "handoff" => preparationPC B ord i pc
private noncomputable abbrev reloadEntry := reloadPC B ord i pc (mapReload B ord i).code.entry
local notation "reloadDest" => reloadEntry B ord i pc
local notation "loop" => Table.segmentLoop s t₀ locPC
private noncomputable abbrev scanBank := (Table.regs s t₀).trans prv
local notation "bank" => scanBank B ord i reg

private theorem loc_free (j : Fin 14) : lr j ∉ Set.range prv := by
  rintro ⟨k, h⟩
  exact Preparation.disjoint (afterChildRegs B ord i reg) k ((mapReload B ord i).locator j)
    (h.trans (map_locator_shared B ord i reg j).symm)

private theorem scan_free (q : Fin r) (h : q ∉ Set.range prv) : HiddenPreserved bank q := by
  have free (k : Fin 22) : q ≠ bank k := fun eqn => h ⟨Table.regs s t₀ k, eqn.symm⟩
  exact ⟨free _, free _, fun j _ => free j⟩

private noncomputable abbrev hiddenInputs := (Table.segmentInputs s t₀).trans prv
local notation "src" => hiddenInputs B ord i reg

include installed in
private theorem handoffLinks :
    (∀ j, M.code (handoff j.castSucc) = VertexLevel.hiddenHandoff (handoff ∘ Fin.castSucc) lr
      src (dfs 6) (handoff (Fin.last VertexLevel.hiddenCount)) j) ∧
    M.code (handoff (Fin.last VertexLevel.hiddenCount)) =
      .copy (lr 8) (src 1) (locPC (Table.segment s t₀).entry) := by
  let physical := (mapReload B ord i).locator.trans (reloadRegs B ord i reg)
  have locEq : physical = lr := DFunLike.ext _ _ (map_locator_shared B ord i reg)
  have rows := ShrinkVertexStage.prepare_rows s t₀ (mapReload B ord i) M
    (afterChildPC B ord i pc) dfs saved (afterChildRegs B ord i reg) done
    (after_child_rows B ord i M pc dfs saved reg done installed)
  constructor
  · intro j
    apply (rows.1 j).trans
    exact congrArg (fun l => VertexLevel.hiddenHandoff (handoff ∘ Fin.castSucc) l src (dfs 6)
      (handoff (Fin.last VertexLevel.hiddenCount)) j) locEq
  · apply rows.2.1.trans
    exact congrArg (fun l : Fin 14 ↪ Fin r => Instr.copy (w := w) (k := 11) (l 8) (src 1)
      (locPC (Table.segment s t₀).entry)) locEq

include separate in
private theorem protectedDFS (j : Fin 9) (hj : j = 3 ∨ j = 5 ∨ j = 6 ∨ j = 7) :
    dfs j ≠ lr 8 ∧ dfs j ∉ Set.range prv := by
  refine ⟨separate j hj (LocatedBody.commonLocator (active B ord)
    (Function.Embedding.refl _) 8), ?_⟩
  rintro ⟨k, e⟩
  exact separate j hj (hiddenRegs B ord i (Function.Embedding.refl _) k) e.symm

include installed separate selectors pitch fit headers in
/-- Link the selected image's setup rows to the native header and retain
the cached field base, all exterior registers, and the original private memory. -/
theorem physicalHiddenSetup_realizes
    (start : ∀ node c, pre node c → PhysicalHiddenEntry (handoff 0) dfs lr g oldHead c)
    {post : Word w → Config w p r → Prop}
    (finish : ∀ node c d, pre node c → d.pc = loop (.inl .one) → Inputs g bank d →
      d.reg (lr 8) = (g.scratchBase : Word w) → d.privateMem = c.privateMem →
      d.persistent = c.persistent →
      (∀ q, q ≠ lr 8 → q ∉ Set.range prv → d.reg q = c.reg q) → post node d) :
    Realizes (physicalHiddenSetup (endAddr := endAddr) s t₀ oldHead m).reader M m dfs
      pre (fun _ => post) := by
  have links := handoffLinks B ord i M pc dfs saved reg done installed
  exact setup_realizes_core (M := M) (m := m) (pre := pre) (post := post) (endAddr := endAddr)
    s t₀ handoff locPC dfs saved lr prv reloadDest g oldHead links.1 links.2
    (hidden_rows B ord i M pc dfs saved reg done installed) (loc_free B ord i reg)
    (protectedDFS B ord i dfs reg separate)
    selectors pitch fit headers start finish

include installed separate selectors pitch fit headers in
/-- Run setup and the entire hidden scan in the selected image. On success,
the map receives the exact field writes and the saved hidden base. -/
theorem physicalHidden_realizes
    (start : ∀ node c, pre node c → PhysicalHiddenEntry (handoff 0) dfs lr g oldHead c)
    (seed : List Row) (countFit : g.countBase + g.owner < 2 ^ w)
    (count : (m (g.countBase + g.owner)).val = seed.length) (valid : ValidRows g m seed)
    (above : endAddr ≤ g.scratchBase) {post : List Row → Word w → Config w p r → Prop}
    (finish : ∀ node c d es, pre node c → ValidRows g m es → d.pc = reloadDest →
      d.privateMem = storeRows g.scratchBase g.slotStride es c.privateMem →
      d.persistent = c.persistent → d.reg (lr 8) = (g.scratchBase : Word w) →
      (∀ j : Fin 14, j ≠ 8 → d.reg (lr j) = c.reg (lr j)) →
      (∀ q, q ≠ lr 8 → q ∉ Set.range prv → d.reg q = c.reg q) → post es node d) :
    Realizes (bind (physicalHiddenSetup s t₀ oldHead m).reader fun _ =>
      hiddenReader (endAddr := endAddr) g m seed) M m dfs pre post := by
  let mid (node : Word w) (d : Config w p r) : Prop :=
    d.pc = loop (.inl .one) ∧ Inputs g bank d ∧ d.reg (lr 8) = (g.scratchBase : Word w) ∧
      ∃ c, pre node c ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent ∧
        ∀ q, q ≠ lr 8 → q ∉ Set.range prv → d.reg q = c.reg q
  have setup : Realizes (physicalHiddenSetup (endAddr := endAddr) s t₀ oldHead m).reader
      M m dfs pre (fun _ => mid) :=
    physicalHiddenSetup_realizes (pre := pre) (post := mid) (endAddr := endAddr) B ord i M pc
      dfs saved reg done installed separate m g oldHead
      selectors pitch fit headers start (fun _ c _ hc ep inputs cache mem pers keep =>
        ⟨ep, inputs, cache, c, hc, mem, pers, keep⟩)
  have scan := (Table.segment_linked s t₀ M locPC dfs saved prv reloadDest
    (hidden_rows B ord i M pc dfs saved reg done installed)).2
  apply setup.bind
  intro _
  apply hidden_realizes scan g m seed dfs mid post (fun _ _ h => ⟨h.1, h.2.1⟩)
    countFit count valid above (fun j hj => scan_free B ord i reg _ fun ⟨k, eqn⟩ =>
      separate j hj (hiddenRegs B ord i (Function.Embedding.refl _) k) eqn.symm)
  intro node d es z hd validRows atExit mem pers keep
  obtain ⟨_, _, cached, c, hc, dm, dp, kept⟩ := hd
  have frame (q : Fin r) (outside : q ∉ Set.range prv) : z.reg q = d.reg q :=
    keep q (scan_free B ord i reg q outside)
  have ext (q : Fin r) (ne : q ≠ lr 8) (outside : q ∉ Set.range prv) : z.reg q = c.reg q :=
    (frame q outside).trans (kept q ne outside)
  exact finish node c z es hc validRows atExit (dm ▸ mem) (pers.trans dp)
    ((frame _ (loc_free B ord i reg 8)).trans cached)
    (fun j hj => ext _ ((LocatedBody.commonLocator (active B ord) reg).injective.ne hj)
      (loc_free B ord i reg j)) ext

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
