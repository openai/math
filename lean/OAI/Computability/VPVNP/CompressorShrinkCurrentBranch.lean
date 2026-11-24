import OAI.Computability.VPVNP.CompressorCurrentGraph
import OAI.Computability.VPVNP.CompressorDefaultSelection
import OAI.Computability.VPVNP.CompressorShrinkHistoryDirectory
import OAI.Computability.VPVNP.CompressorRecordsShrinkBranch
import OAI.Computability.VPVNP.CompressorPrefixScoreFit
import OAI.Computability.VPVNP.CompressorShrinkPublishedHeader

/-!
# The common physical prefix at a shrinking boundary

All terms have identical header reports, so the current packed graph
starts one deterministic prefix before any term is read. The branch at
its endpoint accepts precisely the typed shrinking terms and runs the
selected score and geometry construction for each one.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkCurrentBranch

open BurstRAM Compression Compression.ShrinkMotif BlockHeaderRun DescriptorSpace CurrentGraph
open PairSimulation.LocalHistory PairSimulation.TraversalRows PortRefresh.TraversalHeaders CursorBounds Filter
open scoped Classical Fin.CommRing

variable {k R : Type*} [_root_.Field k] [CommRing R] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)
variable {g w : ℕ} (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))

/-- The shrinking pass occurrence at the given substep and input state. -/
abbrev origin : PassOrigin B f hf (B.shrinkPassAt f hf i rfl X) := .shrink i rfl X
/-- The default selected term of this shrinking occurrence, used to describe the header shared
by every choice. -/
abbrev defaultTerm := defaultSelection (origin B f hf i X)
/-- The selected level with the default term and an empty choice stream, used for the common
header before branching. -/
abbrev beforeLevel := shrinkLevel B f hf i X (defaultTerm B f hf i X) []

variable (base positions blocks : ℕ)
local notation "L" => BlockProgram.layout B base positions blocks
variable (old new : Fin (BlockProgram.layout B base positions blocks).levels) (m : Memory w)
local notation "V" => beforeLevel B f hf i X
local notation "start" => tableBase L old (ShrinkHeaderReads.firstTable B base positions blocks)
local notation "T" => packedIncidence L w old (DemandRAM.oldCount X)
local notation "post" => finalMemory V L old new m
local notation "stride" => (10 : Word w)
/-- The shrinking template's selector-bit count encoded at the host word width. -/
abbrev selectorWord (w : ℕ) : Word w := (B.shrink.selectorBits : Word w)
local notation "selBits" => selectorWord B w
local notation "N" => ShrinkTermInputs.motifCount X

theorem capacity_eq : slotCapacity L = positions*slotDegree S := rfl

theorem scalarFit : 6 ≤ (L).shape.scalarFields := by change 6 ≤ 54; decide

theorem header_eq (s : SelectedScore.Selection B X) (bits : List Bool) :
    finalMemory (shrinkLevel B f hf i X s bits) L old new m = post ∧
      reports (shrinkLevel B f hf i X s bits) L old new m = reports V L old new m := ⟨rfl,rfl⟩

attribute [local irreducible] BlockProgram.script BlockProgram.layout BlockHeaderRun.finalMemory
  PairSimulation.LocalHistory.defaultSelection

/-- Data at the common selection boundary and the true execution on
every continuation. The level indices are relative to the given layout. -/
structure Boundary (L₀ : Layout) (old₀ new₀ : Fin L₀.levels) (six : 6 ≤ L₀.shape.scalarFields)
    (T₀ : IncidenceDirectory w) (begin₀ fuel : ℕ) (input₀ : Memory w) where
  /-- The common shrinking prefix run from the post-header memory through the input and demand
  preparation before term selection. -/
  pre : ShrinkBranch.Prefix X T₀ begin₀ fuel (finalMemory V L₀ old₀ new₀ input₀)
  header : ∀ (s : SelectedScore.Selection B X) (bits : List Bool),
    Substep (w := w) (shrinkLevel B f hf i X s bits) L₀ old₀ new₀ six input₀
  incidence : T₀.Represents X (finalMemory V L₀ old₀ new₀ input₀)
  oldHeads : HeadBank L₀ old₀ (DemandRAM.oldCount X) (finalMemory V L₀ old₀ new₀ input₀)
  nextHeads : ∀ (s : SelectedScore.Selection B X) (bits : List Bool),
    HeadBank L₀ new₀ (shrinkLevel B f hf i X s bits).outputSlots (finalMemory V L₀ old₀ new₀ input₀)
  legal : ∀ bs : Fin N → List Bool,
    (runSegment (ShrinkTermSelection.termProgram B.shrink (ShrinkInput.demandHead X begin₀)
      (ShrinkInput.termHead X begin₀) 10) fuel (some 0) pre.beforeTerm (List.ofFn bs)).isSome ↔
      ∃! s : X.ShrinkSelection B.shrink, bs = ShrinkTermSelection.tapes B.shrink X s w
  selected : ∀ s : SelectedScore.Selection B X, Nonempty (ShrinkBranch.Selected B X T₀ begin₀ stride selBits
    fuel (finalMemory V L₀ old₀ new₀ input₀) pre s)

/-- The physical branch boundary for this packed shrinking level, specialized to the block's
scalar bounds, headers, scratch base and entry memory. -/
abbrev Common (fuel : ℕ) :=
  Boundary B f hf i X L old new (scalarFit B base positions blocks) T start fuel m

set_option maxHeartbeats 1000000 in
theorem build (length fuel : ℕ) (current : Current L old X length m) (next : old.val+1 = new.val)
    (sites : X.positions ≤ positions) (sitesFit : X.positions < 2^w) (degreeFit : slotDegree S < 2^w)
    (fit : endAddress L < 2^w) (prefixFit : ShrinkBranch.PrefixFits B X T start stride fuel)
    (bitsFit : (selBits).val = B.shrink.selectorBits) (weights : ∀ t, MotifAdmission.weight relativeMass t < 2^w)
    (scores : ∀ s : SelectedScore.Selection B X, ∀ l,
      layoutScore relativeMass (X.packingData.termWidths B.shrink X.shrinkNumber X.packingWidth s) l < 2^w) :
    Nonempty (Common B f hf i X base positions blocks old new m fuel) := by
  have count : IncidenceDirectory.slotCount X ≤ slotCapacity L := by
    have eqn : Fintype.card X.Base*2^(packingLaneBits (S.degreeExponent i.castSucc) g) = X.positions := by
      simp only [State.positions,Fintype.card_prod,Fintype.card_congr (bitWordFinEquiv _),Fintype.card_fin]
    have deg : 2^S.degreeExponent i.castSucc ≤ slotDegree S :=
      (Finset.le_sup (f := fun j : Fin (S.steps+1) => 2^S.degreeExponent j) (Finset.mem_univ _)).trans (le_max_right ..)
    rw [capacity_eq]
    change Fintype.card X.Base*2^_*2^_ ≤ positions*slotDegree S
    rw [eqn]; exact Nat.mul_le_mul sites deg
  have publish (s : SelectedScore.Selection B X) (bits : List Bool) :=
    Current.publish («L» := L) (n := length) (B := B) (f := f) (hf := hf) (m := m)
      (shrinkLevel B f hf i X s bits) old new current next (scalarFit B base positions blocks)
      fit count sitesFit degreeFit
  obtain ⟨_,rep,heads,_⟩ := publish (defaultTerm B f hf i X) []
  have geometry := ShrinkBranch.selected_geometry_fit B i X base positions blocks old sites fit
  obtain ⟨p,legal,selected⟩ := ShrinkBranch.build B X T start stride selBits fuel post rep prefixFit bitsFit weights geometry
  have ten : (stride).val = 10 := by
    have h := prefixFit.wide
    exact (Nat.mod_eq_of_lt (h.trans_lt (stride).isLt))
  rw [ten] at legal
  have nextHeads (s : SelectedScore.Selection B X) (bits : List Bool) :
      HeadBank (w := w) L new (shrinkLevel B f hf i X s bits).outputSlots post := by
    rw [← (header_eq B f hf i X base positions blocks old new m s bits).1]
    exact (publish s bits).2.2.2
  exact ⟨⟨p,fun s bits => (publish s bits).1,rep,heads,nextHeads,legal,fun s => selected s (scores s)⟩⟩

end CompressorRecords.ShrinkCurrentBranch

end

end VPVNP
end Computability
end OAI
