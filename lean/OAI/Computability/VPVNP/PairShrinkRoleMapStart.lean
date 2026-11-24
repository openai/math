import OAI.Computability.VPVNP.PairShrinkVertexLinks
import OAI.Computability.VPVNP.PairSimulationShrinkGatherSource
import OAI.Computability.VPVNP.PairShrinkRoleExact

/-!
# Entering the map-list loop in the actual shrinking role

The reload and the five external header probes prepare the loop at the row of the
selected site. The chronological trace depends on the published level and owner.
All private cells are retained, including the child and hidden fields just written.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace PairSimulation.ShrinkVertexImage

open BurstRAM BurstRAM.PrivateRAM VertexImage Compression CompressorRecords
open ShrinkMapImage Registers MapResidentInputs MapResidentRows NodeArguments.ChildScan
open ShrinkRole DFS
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates)
    {t : ℕ} (ord : B.Entry → Fin t) (i : Fin S.steps)
    {p r w : ℕ} (pc : Fin (shrinkSegment B ord).count → Fin p)
    (reg : Fin (shrinkSegment B ord).privateRegs ↪ Fin r) (done : Fin p)

/-- First instruction of the histogram reload reached before the resident map loop at this
scheduled shrink. -/
abbrev reloadStart := Segment.leftPC (ShrinkMapReload.setup (maps B ord i)) (maps B ord i).code
  (reloadPC B ord i pc) (0 : Fin 4)

/-- Embedding of the map loop's shared locator registers into the enclosing shrink stage's
private register bank. -/
abbrev shared := (gatherShared (matrixFamily B ord i) (gatherFamily B ord i)).trans
  (reloadRegs B ord i reg)

/-- Physical program counters for the gather-enabled resident map handler inside the selected
stage. -/
abbrev gatheredPC :=
  matrixPC B ord i pc ∘ gatherLocations (matrixFamily B ord i) (gatherFamily B ord i)

/-- Program-counter map for the core resident map loop after locating it inside the
gather-enabled handler. -/
abbrev basePC := corePC (matrixFamily B ord i) (gatherFamily B ord i) (gatheredPC B ord i pc)

/-- The resident map loop installed for this shrink, with its physical program counters, shared
registers, and return address. -/
abbrev mapLoop := loop (matrixFamily B ord i) mapRegisters (basePC B ord i pc)
  (shared B ord i reg) done

/-- Each of the fourteen live location registers lies outside the seven modified
registers of the map header. -/
theorem locator_header_frame (l : Fin 14) : HeaderFrame
    (mapRegisters.headerReg (shared B ord i reg)) (shared B ord i reg (l.castAdd 10)) := by
  have away (k : Fin 24) (hk : 14 ≤ k.val) :
      shared B ord i reg (l.castAdd 10) ≠ shared B ord i reg k := by
    apply (shared B ord i reg).injective.ne
    intro he
    have eq := congrArg Fin.val he
    change l.val = k.val at eq
    omega
  exact ⟨away _ (by decide), away _ (by decide), away _ (by decide), away _ (by decide),
    away _ (by decide), away _ (by decide), away _ (by decide)⟩

/-- Physical data supplied to the item loop, including all resident source operands and
the unchanged memory used to establish each item's field invariant. -/
structure MapStart (common : Fin 24 ↪ Fin r) (dfs : Fin 9 ↪ Fin r)
    (term : Word w) (c d : Config w p r) : Prop where
  geometry : d.reg (common 9) = c.privateMem (c.reg (dfs 6))
  histogram : d.reg (common 10) = c.privateMem (c.privateMem (c.reg (dfs 6)) + 11)
  term : d.reg (common 16) = term
  stride : d.reg (common 17) = 10
  one : d.reg (common 22) = 1
  outside : ∀ q, q ≠ common 9 → q ≠ common 10 →
    HeaderFrame (mapRegisters.headerReg common) q → d.reg q = c.reg q
  memory : d.privateMem = c.privateMem
  persistent : d.persistent = c.persistent

/-- Sixteen header instructions follow the four private reload instructions. -/
def mapStartSetup {endAddr : ℕ} (m : Memory w) (level owner : Word w) : Setup w endAddr where
  trace _ _ := List.replicate 4 .tick ++ headerEvents m level owner
  updated _ s := s
  quiet _ _ := by simpa [choiceBits] using (headerCost m level owner).2.2

theorem mapStart_cost (m : Memory w) (level owner : Word w) :
    (List.replicate 4 (Event.tick : Event w) ++ headerEvents m level owner).length = 20 ∧
    countProbes (List.replicate 4 .tick ++ headerEvents m level owner) = 5 := by
  obtain ⟨len, probes, _⟩ := headerCost m level owner
  exact ⟨by simp [len], by simpa [countProbes] using probes⟩

variable {g : ℕ} {Z : State (oldExponent i) (packingLaneBits (oldExponent i) g)}
    {sel : Z.ShrinkSelection B.shrink} {side : Bool} {m : Memory w} {level term : Word w}
    (source : MapRowSource Z sel side m level term) (site : Site Z)

/-- First resident map entry for the selected site's directory row, obtained from the row base,
site ordinal, and fixed row capacity. -/
abbrev firstMap :=
  ((ShrinkResidentLayout.layout Z source.first).params (oldExponent i) true w 5).val +
  (siteIndex Z site).val * capacity (oldExponent i)

variable (M : Machine w p r 11) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
    (rows : ∀ a, M.code (pc a) = ((shrinkSegment B ord).row pc dfs saved reg done a).resize w)
    (words : Published m level
      ((ShrinkResidentLayout.layout Z source.first).params (oldExponent i) true w 3)
      ((ShrinkResidentLayout.layout Z source.first).params (oldExponent i) true w 5) term 10)
    (room : level.val + 37 < 2 ^ w)

set_option maxHeartbeats 1400000 in
-- The real image contains nested dependent register banks for every party and stage.
include rows words room in
/-- The concrete gathered map image reaches the correct guard and the exact selected row.
It prepares the term table, the raw geometry head, and the histogram pointer. -/
theorem mapStart_native (c : Config w p r) (start : c.pc = reloadStart B ord i pc)
    (oldHead : c.reg (shared B ord i reg 11) = level)
    (owner : (c.reg (shared B ord i reg 7)).val = (siteIndex Z site).val) :
    let src := firstMap B i source site
    let P := mapLoop B ord i pc reg done
    ∃ d, Prefix M m c d [] (List.replicate 4 .tick ++
      headerEvents m level ((siteIndex Z site).val : Word w)) ∧
      d.pc = P.test ∧ d.reg P.cursor = (src : Word w) ∧
      d.reg P.stop = ((src + (order Z side site).length : ℕ) : Word w) ∧ d.reg P.one = 1 ∧
      MapStart (shared B ord i reg) dfs term c d := by
  let common := shared B ord i reg
  let loc := ((maps B ord i).locator).trans (reloadRegs B ord i reg)
  obtain ⟨reload, matrix⟩ := ShrinkMapReload.links (maps B ord i) M (reloadPC B ord i pc)
    dfs saved (reloadRegs B ord i reg) done (reload_rows B ord i M pc dfs saved reg done rows)
  obtain ⟨mid, pre, entry, geometry, histogram, keep, memory, persist⟩ :=
    ShrinkMapReload.run reload c start m
  have keepLoc (l : Fin 14) (h₉ : l ≠ 9) (h₁₀ : l ≠ 10) : mid.reg (loc l) = c.reg (loc l) :=
    keep _ (loc.injective.ne h₉) (loc.injective.ne h₁₀)
  have head : mid.reg ((mapRegisters.headerReg common) 0) = level :=
    (keepLoc 11 (by decide) (by decide)).trans oldHead
  have ownerEq : (mid.reg ((mapRegisters.headerReg common) 1)).val = (siteIndex Z site).val :=
    (congrArg Fin.val (keepLoc 7 (by decide) (by decide))).trans owner
  have ownerWord : mid.reg ((mapRegisters.headerReg common) 1) =
      ((siteIndex Z site).val : Word w) := by
    rw [← ownerEq]
    exact Fin.ext (Nat.mod_eq_of_lt (mid.reg ((mapRegisters.headerReg common) 1)).isLt).symm
  have hl := map_linked B ord i M (matrixPC B ord i pc) dfs saved (reloadRegs B ord i reg)
    done matrix
  obtain ⟨out, hdr, result, cursor, stop, termAt, stride⟩ :=
    source.header_native site _ _ _ hl.header mid entry head ownerEq words room
  rw [ownerWord] at hdr
  exact ⟨out, pre.trans hdr, result.pc, cursor, stop, result.one,
    ⟨(result.frame _ (locator_header_frame B ord i reg 9)).trans geometry,
      (result.frame _ (locator_header_frame B ord i reg 10)).trans histogram, termAt, stride,
      result.one,
      fun q h₉ h₁₀ hf => (result.frame q hf).trans (keep q h₉ h₁₀),
      result.memory.trans memory, result.persistent.trans persist⟩⟩

set_option maxHeartbeats 1400000 in
-- The real image contains nested dependent register banks for every party and stage.
include rows words room in
/-- The remaining invariant can use every fact from the genuine map header and reload;
the code, exact trace, loop pointers, state and stack frame are already discharged. -/
theorem mapStart_realizes {endAddr : ℕ} {pre inv : Word w → Config w p r → Prop}
    (start : ∀ node c, pre node c → c.pc = reloadStart B ord i pc)
    (oldHead : ∀ node c, pre node c → c.reg (shared B ord i reg 11) = level)
    (owner : ∀ node c, pre node c → (c.reg (shared B ord i reg 7)).val = (siteIndex Z site).val)
    (separate : ∀ l : Fin 9, l = 3 ∨ l = 5 ∨ l = 6 ∨ l = 7 →
      dfs l ∉ Set.range (shared B ord i reg))
    (resume : ∀ node c d, pre node c → MapStart (shared B ord i reg) dfs term c d → inv node d) :
    Realizes (endAddr := endAddr) (mapStartSetup m level ((siteIndex Z site).val : Word w)).reader
      M m dfs pre (fun _ => ResidentMapLoop.Exact.Entry (mapLoop B ord i pc reg done) inv
        (firstMap B i source site) (order Z side site).length) := by
  apply Setup.realizes
  intro node c hc
  obtain ⟨d, run, pc', cursor, stop, one, facts⟩ :=
    mapStart_native B ord i pc reg done source site M dfs saved rows words room c
      (start node c hc) (oldHead node c hc) (owner node c hc)
  refine ⟨d, ⟨pc', cursor, stop, one, resume node c d hc facts⟩, ⟨?_, ?_, facts.persistent⟩,
    congrArg (scratch endAddr) facts.memory, run⟩
  · intro j hj
    have off (l : Fin 24) : dfs j ≠ shared B ord i reg l := fun e => separate j hj ⟨l, e.symm⟩
    exact facts.outside _ (off _) (off _)
      ⟨off _, off _, off _, off _, off _, off _, off _⟩
  · intro a _
    exact congrFun facts.memory a

end PairSimulation.ShrinkVertexImage

end

end VPVNP
end Computability
end OAI
