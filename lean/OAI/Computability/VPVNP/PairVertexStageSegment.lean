import OAI.Computability.VPVNP.PairVertexStageDispatch
import OAI.Computability.VPVNP.PairVertexLevelLocator
import OAI.Computability.VPVNP.PairVertexSegmentChain

/-!
# Linking the stage selector to a heterogeneous family of shrink handlers

The selector and each handler have separate code ranges. The locator and every
handler share the same fourteen-word header bank. The selector's scratch words
and the variable-length handler tails occupy disjoint ranges.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexStageDispatch

open VertexImage BurstRAM PrivateRAM

variable {N n p r w : ℕ}

/-- Size of the scheduled dispatch family, including the selector table and every stage body's
instructions. -/
def familyCount (B : Fin N → Segment) := count N + ∑ i, (B i).count

/-- Place stage-selection instructions before the concatenated bodies of the dispatch family. -/
def selectorPC (B : Fin N → Segment) (loc : Fin (familyCount B) → Fin p)
    (j : Fin (count N)) := loc (j.castAdd (∑ i, (B i).count))

/-- Place an instruction of a particular scheduled body using its dependent ordinal in the
concatenated family. -/
def bodyPC (B : Fin N → Segment) (loc : Fin (familyCount B) → Fin p)
    (i : Fin N) (j : Fin (B i).count) :=
  loc ((finSigmaFinEquiv (n := fun i ↦ (B i).count) ⟨i,j⟩).natAdd (count N))

/-- Any explicit bank placement can host the family. Every selected handler
returns to the enclosing role continuation. -/
def family (B : Fin N → Segment) (locator : Fin 14 ↪ Fin n) (scratch : Fin 4 ↪ Fin n)
    (bank : ∀ i, Fin (B i).privateRegs ↪ Fin n) : Segment where
  count := familyCount B
  privateRegs := n
  entry := (entry N).castAdd (∑ i, (B i).count)
  row loc dfs saved reg done := Fin.addCases
    (row N (selectorPC B loc) (scratch.trans reg) (reg (locator 13))
      (fun i ↦ bodyPC B loc i (B i).entry))
    (fun j ↦ let z := (finSigmaFinEquiv (n := fun i ↦ (B i).count)).symm j
             (B z.1).row (bodyPC B loc z.1) dfs saved ((bank z.1).trans reg) done z.2)

variable (B : Fin N → Segment) (locator : Fin 14 ↪ Fin n) (scratch : Fin 4 ↪ Fin n)
    (bank : ∀ i, Fin (B i).privateRegs ↪ Fin n)
    (loc : Fin (familyCount B) → Fin p) (dfs : Fin 9 ↪ Fin r) (saved : Saved ↪ Fin r)
    (reg : Fin n ↪ Fin r) (done : Fin p) (M : Machine w p r 11)

/-- Split the concrete image into its selector table and its individually
relocated branch bodies, with the exact native jump destinations. -/
theorem family_link (rows : ∀ j, M.code (loc j) =
    ((family B locator scratch bank).row loc dfs saved reg done j).resize w) :
    Linked M (selectorPC B loc) (scratch.trans reg) (reg (locator 13))
      (fun i ↦ bodyPC B loc i (B i).entry) ∧
    ∀ i j, M.code (bodyPC B loc i j) =
      ((B i).row (bodyPC B loc i) dfs saved ((bank i).trans reg) done j).resize w := by
  constructor
  · intro j
    simpa only [family, selectorPC, Fin.addCases_left] using rows (j.castAdd (∑ i, (B i).count))
  · intro i j
    let E := finSigmaFinEquiv (n := fun i ↦ (B i).count)
    let emit (z : (i : Fin N) × Fin (B i).count) :=
      ((B z.1).row (bodyPC B loc z.1) dfs saved ((bank z.1).trans reg) done z.2).resize w
    calc
      M.code (bodyPC B loc i j) = emit (E.symm (E ⟨i,j⟩)) := by
        have hh := rows ((E ⟨i,j⟩).natAdd (count N))
        simp only [family, Fin.addCases_right] at hh
        exact hh
      _ = _ := congrArg emit (E.symm_apply_apply ⟨i,j⟩)

section Canonical

variable (tail : Fin N → ℕ)

/-- The shared locator prefix is followed by four selector scratch words
and by the private tails in increasing order of shrink stage. -/
def bankCount := 14 + (4 + ∑ i, tail i)

/-- Number the shared locator and selector scratch registers followed by each body's private
tail bank. -/
def bankIndex : (Fin 14 ⊕ Fin 4 ⊕ (i : Fin N) × Fin (tail i)) ≃ Fin (bankCount tail) :=
  let rest := ((Equiv.refl (Fin 4)).sumCongr finSigmaFinEquiv).trans finSumFinEquiv
  ((Equiv.refl (Fin 14)).sumCongr rest).trans finSumFinEquiv

/-- Embed the common fourteen-register locator bank in the dispatch family's register layout. -/
def locatorBank := Function.Embedding.inl.trans (bankIndex tail).toEmbedding

/-- Embed the selector's four scratch registers beside the common locator bank. -/
def scratchBank := Function.Embedding.inl.trans
  (Function.Embedding.inr.trans (bankIndex tail).toEmbedding)

/-- Embed only the indicated stage's tail registers in the dependent family of private tail
banks. -/
def tailBank (i : Fin N) := (Function.Embedding.sigmaMk (β := fun i ↦ Fin (tail i)) i).trans
  (Function.Embedding.inr.trans (Function.Embedding.inr.trans (bankIndex tail).toEmbedding))

variable (split : ∀ i, (B i).privateRegs = 14 + tail i)

/-- A handler sees the locator in its first fourteen registers and sees
only its own tail in the remaining registers. -/
def bodyBank (i : Fin N) : Fin (B i).privateRegs ↪ Fin (bankCount tail) :=
  let blocks := (finCongr (split i)).trans finSumFinEquiv.symm
  let suffix := (Function.Embedding.sigmaMk (β := fun i ↦ Fin (tail i)) i).trans
    (Function.Embedding.inr (α := Fin 4))
  blocks.toEmbedding.trans ((Function.Embedding.sumMap (.refl (Fin 14)) suffix).trans
    (bankIndex tail).toEmbedding)

theorem bodyBank_locator (i : Fin N) (j : Fin 14) :
    bodyBank B tail split i ((j.castAdd (tail i)).cast (split i).symm) = locatorBank tail j := by
  change (bankIndex tail) (Sum.map _ _ (finSumFinEquiv.symm _)) = (bankIndex tail) (.inl j)
  rw [show (finCongr (split i)) ((j.castAdd (tail i)).cast (split i).symm) =
    finSumFinEquiv (.inl j : Fin 14 ⊕ Fin (tail i)) from rfl, Equiv.symm_apply_apply]
  rfl

theorem bodyBank_tail (i : Fin N) (j : Fin (tail i)) :
    bodyBank B tail split i ((j.natAdd 14).cast (split i).symm) = tailBank tail i j := by
  change (bankIndex tail) (Sum.map _ _ (finSumFinEquiv.symm _)) =
    (bankIndex tail) (.inr (.inr ⟨i,j⟩))
  rw [show (finCongr (split i)) ((j.natAdd 14).cast (split i).symm) =
    finSumFinEquiv (.inr j : Fin 14 ⊕ Fin (tail i)) from rfl, Equiv.symm_apply_apply]
  rfl

theorem locator_disjoint_scratch (j : Fin 14) :
    locatorBank tail j ∉ Set.range (scratchBank tail) := by
  rintro ⟨s,eqn⟩
  have eq : (Sum.inr (Sum.inl s)) = (Sum.inl j) := (bankIndex tail).injective eqn
  cases eq

theorem scratch_disjoint_body (i : Fin N) (j : Fin (B i).privateRegs) :
    bodyBank B tail split i j ∉ Set.range (scratchBank tail) := by
  rintro ⟨s,eqn⟩
  obtain ⟨j | j, rfl⟩ := (((finCongr (split i)).trans finSumFinEquiv.symm).symm).surjective j
  · exact locator_disjoint_scratch tail j ⟨s, eqn.trans (bodyBank_locator B tail split i j)⟩
  · have eq := eqn.trans (bodyBank_tail B tail split i j)
    have e : (Sum.inr (Sum.inl s) : Fin 14 ⊕ Fin 4 ⊕ (i : Fin N) × Fin (tail i)) =
        Sum.inr (Sum.inr ⟨i,j⟩) := (bankIndex tail).injective eq
    injection e with h
    cases h

/-- The full shrink role starts by recovering its level and then dispatches
its zero-based producing ordinal to the selected handler. -/
def locatedFamily : Segment :=
  Segment.thenWith VertexLevel.segment
    (family B (locatorBank tail) (scratchBank tail) (bodyBank B tail split))
    (locatorBank tail) (.refl _)

/-- Total instruction count of a family preceded by the level locator. -/
abbrev locatedCount := VertexLevel.segment.count + familyCount B

/-- Program counters of the locator at the beginning of the combined locator-and-dispatch
image. -/
def locatorPC (where_ : Fin (locatedCount B) → Fin p) (j : Fin 35) :=
  where_ (j.castAdd (familyCount B))

/-- Program counters of the dispatch family after the locator's 35 instructions. -/
def familyPC (where_ : Fin (locatedCount B) → Fin p) (j : Fin (familyCount B)) :=
  where_ (j.natAdd 35)

/-- Both the 35 locator rows and every selector and stage-body row occur at
their indicated PCs in the single hosted role. -/
theorem locatedFamily_link (where_ : Fin (locatedCount B) → Fin p)
    (reg : Fin (bankCount tail) ↪ Fin r)
    (rows : ∀ j, M.code (where_ j) =
      ((locatedFamily B tail split).row where_ dfs saved reg done j).resize w) :
    (∀ j, M.code (locatorPC B where_ j) =
      (VertexLevel.segment.row (locatorPC B where_) dfs saved ((locatorBank tail).trans reg)
        (selectorPC B (familyPC B where_) (entry N)) j).resize w) ∧
    Linked M (selectorPC B (familyPC B where_)) ((scratchBank tail).trans reg)
      (reg (locatorBank tail 13)) (fun i ↦ bodyPC B (familyPC B where_) i (B i).entry) ∧
    ∀ i j, M.code (bodyPC B (familyPC B where_) i j) =
      ((B i).row (bodyPC B (familyPC B where_) i) dfs saved
        ((bodyBank B tail split i).trans reg) done j).resize w := by
  obtain ⟨headRows, familyRows⟩ := Segment.split_link VertexLevel.segment
    (family B (locatorBank tail) (scratchBank tail) (bodyBank B tail split))
    (locatorBank tail) (.refl _) where_ dfs saved reg done M rows
  exact ⟨headRows, family_link B (locatorBank tail) (scratchBank tail) (bodyBank B tail split)
    (familyPC B where_) dfs saved reg done M familyRows⟩

end Canonical
end PairSimulation.VertexStageDispatch

end VPVNP
end Computability
end OAI
