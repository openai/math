import OAI.Computability.VPVNP.PairSimulationShrinkMapImage
import OAI.Computability.VPVNP.PairSimulationMapResidentRows
import OAI.Computability.VPVNP.RAMProcessorReportPrefix

/-!
# Dispatching one map of the actual shrinking directory

A genuine packed row gives the dense motif ordinal, party and term-record
address. Its first term word selects the same demand-grid point used by the
six-party conversion evaluator. The external reads and all subsequent private
branches below are actual instructions of the combined shrinking map image.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkMapImage.Registers

open BurstRAM BurstRAM.PrivateRAM PrimedCounter.GuessWord CompressorRecords Compression
open MotifGrid MotifBlocks MotifConversion ShrinkMotif MapResidentRows NodeArguments.ChildScan
open scoped Fin.CommRing

variable {K : Type} [Field K] {factor : ℝ}
  {B : FixedBlock K demandSource demandTarget supply
    (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
  {p r t shared w a g : ℕ} (F : MapHandlerImage.Family B t shared)
  (S : Registers shared) (loc : Address F → Fin p)
  (common : Fin shared ↪ Fin r) (M : Machine w p r 11)
  (target : B.grid.demands → Fin 6 → Fin p)
  (item : MapResidentInputs.ItemLinked M (inputPC F loc ∘ Sum.inr) (S.headerReg common)
    (casePC F loc (.inl ())))
  (dispatch : ({ cases F S loc common with target := target }).Linked M)
  (X : State a (packingLaneBits a g)) {layout : Bool} {m : Memory w}
  {dense term : Word w} {cap : ℕ} {s : X.ShrinkSelection B}
  {before : Memory w} {rs : List (Report w)}

private theorem word_of_val {x : Word w} {n : ℕ} (h : x.val = n) : x = (n : Word w) := by
  apply Fin.ext
  rw [← h]
  exact (Nat.mod_eq_of_lt x.isLt).symm

open Classical in
include item dispatch in
/-- The item and dispatch prefix ends at the real writer of the intended
`(z,j)` matrix. It preserves the motif and term pointers needed by that writer. -/
theorem item_selected (first : ℕ) (fit : (ShrinkResidentLayout.layout X first).endAddr < 2 ^ w)
    (rows : Directory X layout ((ShrinkResidentLayout.layout X first).params a true w) m)
    (site : Site X) (i : Fin (order X layout site).length) (c : Config w p r)
    (hc : c.pc = inputPC F loc (.inr 0))
    (cursor : (c.reg ((S.headerReg common) 2)).val =
      ((ShrinkResidentLayout.layout X first).params a true w 5).val +
        (siteIndex X site).val * capacity a + i.val)
    (headReg : c.reg ((S.headerReg common) 4) = term)
    (strideReg : c.reg ((S.headerReg common) 5) = 10)
    (one : c.reg ((S.headerReg common) 10) = 1)
    (terms : ShrinkTermSelection.Written B X dense term 10 cap s before rs)
    (termFit : term.val + (LocalHistory.shrinkMotifOrder X).length * 10 ≤ 2 ^ w)
    (retained : ∀ x : X.packingData.Motif, m (term.val + (ordinal X x).val * 10) =
      after before (eventLog rs) (term.val + (ordinal X x).val * 10)) :
    let reg := S.headerReg common
    let e := entry X layout site i
    let z := demandGrid B demandMass_pos
      (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth e.1)
    let code := (demandOrder B.grid.demands).symm z
    let es := MapResidentInputs.itemEvents m (c.reg (reg 2)) (c.reg (reg 4)) (c.reg (reg 5)) ++
      List.replicate (1 + ((2 * code.val + 1) + (2 * e.2.val + 1))) .tick
    ∃ d, NodeArguments.ChildScan.Prefix M m c d [] es ∧
      d.pc = target z e.2 ∧
      (d.reg (reg 6)).val = (ordinal X e.1).val ∧
      (d.reg (reg 8)).val = term.val + (ordinal X e.1).val * 10 ∧
      (∀ q, q ≠ common S.zero → (∀ l : Fin 11, 6 ≤ l.val → l.val ≤ 9 → q ≠ reg l) →
        d.reg q = c.reg q) ∧ d.privateMem = c.privateMem ∧ d.persistent = c.persistent := by
  intro reg e z code es
  obtain ⟨m₁, read, info⟩ := MapResidentInputs.item_native item m c hc
  obtain ⟨hm, hj, ht, hz⟩ := MapResidentInputs.ItemResult.selected X B info first fit rows site i
    cursor headReg strideReg terms termFit retained
  obtain ⟨hgrid, hval⟩ := List.getElem?_eq_some_iff.mp hz
  let idx : Fin B.grid.demands.toList.length := ⟨(m₁.reg (reg 9)).val, hgrid⟩
  have heq : demandOrder B.grid.demands idx = z := Subtype.ext hval
  have iEq : idx = code := (demandOrder B.grid.demands).eq_symm_apply.mpr heq
  have gv : (m₁.reg (reg 9)).val = code.val := congrArg Fin.val iEq
  have one' : m₁.reg (reg 10) = 1 := (info.frame _ (fun l _ hi ↦ reg.injective.ne
    (by intro eq; have h := congrArg Fin.val eq; change 10 = l.val at h; omega))).trans one
  let C := { cases F S loc common with target := target }
  have apart := distinct F S loc common
  have apartC : C.Distinct := ⟨apart.gz, apart.pz, apart.go', apart.po, apart.oz, apart.pg⟩
  obtain ⟨out, tail, outPC, frame, memory, persistent⟩ := C.native M dispatch
    apartC code e.2 (gv ▸ (m₁.reg (reg 9)).isLt)
    (hj ▸ (m₁.reg (reg 7)).isLt) m₁ info.pc (word_of_val gv) (word_of_val hj) one'
  have next : NodeArguments.ChildScan.Prefix M m m₁ out []
      (List.replicate (1 + ((2 * code.val + 1) + (2 * e.2.val + 1))) .tick) := by
    intro fuel bs
    have noBits (n : ℕ) : choiceBits (List.replicate n (.tick : Event w)) = [] := by
      induction n with
      | zero => rfl
      | succ n ih => simpa only [List.replicate_succ, choiceBits] using ih
    simpa only [noBits, List.nil_append] using tail.execute fuel m bs
  have untouched (l : Fin 11) (ng : l ≠ 9) (np : l ≠ 7) : out.reg (reg l) = m₁.reg (reg l) :=
    frame _ (common.injective.ne (S.apart l).symm) (reg.injective.ne ng) (reg.injective.ne np)
  refine ⟨out, read.trans next, ?_, ?_, ?_, ?_, memory.trans info.memory,
    persistent.trans info.persistent⟩
  · simpa [C, cases, code] using outPC
  · rw [untouched 6 (by decide) (by decide), hm]
  · rw [untouched 8 (by decide) (by decide), ht]
  · intro q zero other
    exact (frame _ zero (other 9 (by decide) (by decide)) (other 7 (by decide) (by decide))).trans
      (info.frame _ other)

end PairSimulation.ShrinkMapImage.Registers

end VPVNP
end Computability
end OAI
