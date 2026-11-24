import OAI.Computability.VPVNP.CompressorRecordsSelectedFinish
import OAI.Computability.VPVNP.PairTraversalLevelDirectories

/-!
# The completed shrinking scan as a level of the actual DFS history

The selected pass, its term, and both site orders come from the compressor
execution. Later native calls can retain this directory by preserving its
three physical regions. They may change other cells, including the scheduler
header below the raw tables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRows

open BurstRAM CompressorRecords NetworkKernel LocalHistory Compression

variable {A : Type*} [CommRing A] {N : Network} {t : Term A N} {w limit : ℕ}
variable {old : Order N.Site} {next : Order t.output.Site} {m m' : Memory w}

/-- Addresses occupied by the old-owner column, the new-site counts and the fixed-capacity
preimage rows of a DFS directory. -/
def directoryCell (pub : Fin 6 → Word w) (x : ℕ) : Prop :=
  ((pub 1).val ≤ x ∧ x < (pub 1).val+(pub 0).val) ∨
  ((pub 3).val ≤ x ∧ x < (pub 3).val+(pub 2).val) ∨
  ((pub 5).val ≤ x ∧ x < (pub 5).val+(pub 2).val*(pub 4).val)

open private countAt_val rowAt_val from OAI.Computability.VPVNP.CompressorRecordPreimageScan

/-- Reuse a collected DFS directory at a larger limit in another memory that agrees on its
owner, count and preimage-row regions. -/
def Directory.transfer (dir : Directory t old next m limit) (newLimit : ℕ)
    (room : limit ≤ newLimit) (agree : ∀ x, directoryCell dir.pub x → m' x = m x) :
    Directory t old next m' newLimit := by
  refine {dir with inputEnd := dir.inputEnd.trans room, collected := ⟨?_,?_⟩}
  · intro i hi
    have bounds := dir.regions.ownersBeforeCounts
    have hfit := (dir.pub 3).isLt
    have hi' : i.val < (dir.pub 0).val := hi
    have addr : (dir.pub 1+i).val = (dir.pub 1).val+i.val := by
      rw [Fin.val_add,Nat.mod_eq_of_lt (by omega)]
    change m' (dir.pub 1+i).val = _
    rw [agree _ (.inl (by rw [addr]; omega))]
    exact dir.collected.owners i hi
  · intro v hv
    have row := dir.collected.rows v hv
    have c := countAt_val dir.regions hv
    have r := rowAt_val dir.regions hv
    have hv' : v.val < (dir.pub 2).val := hv
    constructor
    · rw [agree _ (.inr (.inl (by rw [c]; omega)))]
      exact row.1
    · intro j
      have hc := j.isLt.trans_le (dir.capacity v hv)
      have mul := Nat.mul_le_mul_right (dir.pub 4).val hv'
      rw [Nat.succ_mul] at mul
      rw [agree _ (.inr (.inr (by rw [r]; omega)))]
      exact row.2 j

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f)
variable (i : Fin S.steps) {g : ℕ} (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g))
variable (term stride selectors : Word w) (p₀ : Fin 14 → Word w) (s : SelectedScore.Selection B X)
variable (mem : Memory w) (p : SelectedStage.Passes w) (q : SelectedFinish.Passes w)

/-- Any selector bit string indexing this selected pass yields the same
DFS directory for its native placement rows. -/
noncomputable def shrinkLevel (selector : List Bool) : SelectedLevel B f hf :=
  ⟨_,_,_,_,X,B.shrinkPassAt f hf i rfl X,.shrink i rfl X,s,selector⟩

/-- The selected shrinking pass's old-site placement directory in the final report memory,
bounded by the end of the selected allocation. -/
noncomputable def selectedShrinkDirectory (selector : List Bool)
    (built : SelectedFinish.Built B X term stride selectors p₀ s mem p q)
    (room : SelectedFinish.stop X term stride ≤ 2^w) :
    LevelDirectory (shrinkLevel B f hf i X s selector) (q.final (p.final mem)) (SelectedFinish.stop X term stride) :=
  built.selectedDirectory B X term stride selectors p₀ s mem p (f ∘ Sum.inl) ((B.solution_iff f).mp hf).1 (S.shrink i) room

end PairSimulation.TraversalRows

end VPVNP
end Computability
end OAI
