import OAI.Computability.VPVNP.PairSimulationShrinkGatherImage
import OAI.Computability.VPVNP.PairSimulationShrinkGatherSource

/-!
# Entering the selected shrinking party's field gather

The count and ID tables use the same ordered list as the compression pass.
The selected term determines the grid and the old header determines the
layout. The chronological trace here depends only on those published words.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM CompressorRecords Compression Compression.ShrinkMotif
open MotifGrid MotifBlocks MotifConversion MapResidentRows NodeArguments.ChildScan
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {p r t shared w a g : ℕ} (F : MapHandlerImage.Family B t shared)
  (G : ShrinkGatherBank.Family F) (S : Registers shared)
  (pc : GatherAddress F G → Fin p) (dfs : Fin 9 ↪ Fin r)
  (saved : VertexImage.Saved ↪ Fin r) (common : Fin shared ↪ Fin r)
  (own : F.PrivateReg ↪ Fin r) (gatherReg : G.PrivateReg ↪ Fin r) (tmp : Fin r) (ret : Fin p)
  (M : Machine w p r 11) (link : GatherLinked F G S pc dfs saved common own gatherReg tmp ret M)
  (X : State a (packingLaneBits a g)) (selection : X.ShrinkSelection B)
  (side : Bool) (site : Site X) (m : Memory w) (level term : Word w)

/-- Classical equality on base vertices for looking up the selected resident row. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _

variable (R : MapRowSource X selection side m level term)
  (i : Fin (order X side site).length)

set_option maxHeartbeats 4500000 in
-- The selected term, typed packet and installed register bank have dependent indices.
include link in
/-- Execute the real map-ID read, term read, grid and party cases, and layout
read at the indicated resident-row address. All operand base registers survive. -/
theorem enterGather (hw : 0 < w) (outside : ∀ b, common b ≠ tmp) (c : Config w p r)
    (start : c.pc = inputPC F (corePC F G pc) (.inr 0))
    (cursor : (c.reg ((S.headerReg common) 2)).val =
      rowCursor X selection side site m level term R i)
    (head : c.reg ((S.headerReg common) 0) = level)
    (base : c.reg ((S.headerReg common) 4) = term)
    (stride : c.reg ((S.headerReg common) 5) = 10)
    (one : c.reg ((S.headerReg common) 10) = 1) :
    let reg := S.headerReg common
    let e := entry X side site i
    let z := rowGrid (B := B) X side site i
    ∃ d, Prefix M m c d [] (routeEvents X selection side site m level term R i) ∧
      d.pc = G.entry (gatherPC F G pc) (writer F G pc) z e.2 side ∧
      (d.reg (reg 6)).val = (ordinal X e.1).val ∧
      (d.reg (reg 8)).val = term.val + (ordinal X e.1).val * 10 ∧
      (∀ q, q ≠ tmp → q ≠ common S.zero →
        (∀ l : Fin 11, 6 ≤ l.val → l.val ≤ 9 → q ≠ reg l) → d.reg q = c.reg q) ∧
      d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  intro reg e z
  obtain ⟨d, reads, hp, hm, ht, frame, memory, persistent⟩ :=
    item_selected F S (corePC F G pc) common M (fun z j ↦ layoutPC F G pc z j 0)
      link.item link.dispatch X R.first R.fit R.rows site i c start cursor base stride one
      R.terms R.termFit R.retained
  change (d.reg (reg 6)).val = (ordinal X e.1).val at hm
  change (d.reg (reg 8)).val = term.val + (ordinal X e.1).val * 10 at ht
  have keep (j : Fin 11) (hj : j.val < 6 ∨ 9 < j.val) : d.reg (reg j) = c.reg (reg j) :=
    frame _ (common.injective.ne (S.apart j).symm) (fun l lo hi ↦ reg.injective.ne (by
      intro h
      rw [h] at hj
      omega))
  have levelEq := (keep 0 (by decide)).trans head
  have oneEq := (keep 10 (by decide)).trans one
  obtain ⟨out, layoutRun, branch, _, savedReg, memEq, perEq⟩ := ShrinkLayoutBranch.native
    (link.layout z e.2) m d hp hw (outside _) (outside _) oneEq side (by
      rw [levelEq]
      exact R.layout)
  have address : c.reg (reg 2) = (rowCursor X selection side site m level term R i : Word w) := by
    apply Fin.ext
    change (c.reg (reg 2)).val = rowCursor X selection side site m level term R i % (2 ^ w)
    rw [← cursor, Nat.mod_eq_of_lt (c.reg (reg 2)).isLt]
  refine ⟨out, ?_, branch, ?_, ?_, ?_, memEq.trans memory, perEq.trans persistent⟩
  · let ticks := List.replicate
      (1 + ((2 * ((demandOrder B.grid.demands).symm z).val + 1) + (2 * e.2.val + 1)))
      (.tick : Event w)
    have readPrefix : Prefix M m c d [] (MapResidentInputs.itemEvents m
        (c.reg (reg 2)) (c.reg (reg 4)) (c.reg (reg 5)) ++ ticks) := reads
    have layoutPrefix : Prefix M m d out [] (ShrinkLayoutBranch.events m (d.reg (reg 0))) :=
      layoutRun
    let cursorWord := (rowCursor X selection side site m level term R i : Word w)
    have readEq : MapResidentInputs.itemEvents m (c.reg (reg 2)) (c.reg (reg 4))
        (c.reg (reg 5)) = MapResidentInputs.itemEvents m cursorWord term 10 :=
      congr (congr (congrArg (MapResidentInputs.itemEvents m) address) base) stride
    have eq : (MapResidentInputs.itemEvents m (c.reg (reg 2)) (c.reg (reg 4)) (c.reg (reg 5)) ++
        ticks) ++ ShrinkLayoutBranch.events m (d.reg (reg 0)) =
        routeEvents X selection side site m level term R i :=
      congr (congrArg List.append (congrArg (fun es ↦ es ++ ticks) readEq))
        (congrArg (ShrinkLayoutBranch.events m) levelEq)
    exact eq ▸ readPrefix.trans layoutPrefix
  · exact (congrArg Fin.val (savedReg (reg 6) (outside (S.header 6)))).trans hm
  · exact (congrArg Fin.val (savedReg (reg 8) (outside (S.header 8)))).trans ht
  · intro q nt nz nr
    exact (savedReg q nt).trans (frame q nz nr)

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
