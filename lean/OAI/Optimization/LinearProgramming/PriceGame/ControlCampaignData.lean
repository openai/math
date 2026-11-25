import OAI.Optimization.LinearProgramming.PriceGame.ControlData
import OAI.Optimization.LinearProgramming.PriceGame.Campaign

/-! # The outer campaign update on first-order lists

Old expert identifiers persist by list append. The new batch is generated from
the exact public price and ancestor rows read from the packed cumulative history.
-/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control

open Learning

variable {N : ℕ}

theorem testsAt_history_ext (s : Skeleton N) (level : ℕ) (prices : States.Mass.Vertex N level → ℚ)
    (h g : History N) (eq : ∀ j, j < level → h j = g j) :
    s.testsAt ⟨level,prices,h⟩ = s.testsAt ⟨level,prices,g⟩ := by
  by_cases hl : level = s.level
  · subst level
    have outside (i : Fin 64) : s.outsideTest h prices i = s.outsideTest g prices i := by
      unfold Skeleton.outsideTest
      cases hp : s.pivot with
      | none => rfl
      | some pivot =>
        obtain ⟨j,i⟩ := pivot
        simp [eq j j.isLt]
    simp [Skeleton.testsAt, outside]
  · simp [Skeleton.testsAt, hl]

theorem testsAt_unpack_pack (s : Skeleton N) (p : Probe N) :
    s.testsAt (unpackProbe N (packProbe p)) = s.testsAt p := by
  rcases p with ⟨l,x,h⟩
  change s.testsAt ⟨l, lookupTable N l (packTable N l x), unpackHistory N (packHistory l h)⟩ =
    s.testsAt ⟨l,x,h⟩
  rw [show lookupTable N l (packTable N l x) = x by funext i; exact lookupTable_pack _ _ _ i]
  apply testsAt_history_ext
  intro j hj
  funext i
  exact unpackHistory_pack h hj i

private theorem tests_flatMap_eq (s : Skeleton N) (ps : List (Probe N)) :
    ((ps.map packProbe).map (unpackProbe N)).flatMap s.testsAt = ps.flatMap s.testsAt := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.map_cons, List.flatMap_cons, testsAt_unpack_pack, ih]

/-- Enumerate the paper's actual comparison cells, with list-valued inputs and output. -/
def packedBatch (N R : ℕ) (ps : List PackedProbe) : List PackedExpert :=
  (Pool.batch N R (ps.map (unpackProbe N))).map packExpert

theorem packedBatch_eq (R : ℕ) (ps : List (Probe N)) :
    packedBatch N R (ps.map packProbe) = (Pool.batch N R ps).map packExpert := by
  have thresholds (s : Skeleton N) :
      Compact.thresholds s ((ps.map packProbe).map (unpackProbe N)) = Compact.thresholds s ps := by
    funext feat
    simp only [Compact.thresholds, tests_flatMap_eq]
  have each (s : Skeleton N) :
      Pool.forSkeleton R s ((ps.map packProbe).map (unpackProbe N)) = Pool.forSkeleton R s ps := by
    simp only [Pool.forSkeleton, thresholds]
  simp only [packedBatch, Pool.batch, each]

/-- Empty history, all first-generation experts and their uniform weights. -/
def initialPopulation (N R : ℕ) : PackedPopulation :=
  let first := packedBatch N R []
  ⟨first, List.replicate first.length (first.length : ℚ)⁻¹⟩

theorem initialPopulation_eq (N R : ℕ) :
    initialPopulation N R = packPopulation (Population.start (Pool.batch N R)) := by
  have h : packedBatch N R [] = (Pool.batch N R []).map packExpert := packedBatch_eq R []
  simp [initialPopulation, h, Population.start, packPopulation]

/-- Multiply the old weights by the integer powers of two of their returned scores. -/
def scaledWeights (weights : List ℚ) (scores : List ℕ) : List ℚ :=
  List.ofFn fun i : Fin weights.length => 2 ^ scores[i.val]?.getD 0 * weights[i.val]

private theorem scaledWeights_eq (p : Population N) (round : RoundResult N) :
    scaledWeights (packPopulation p).weights (packRound p.experts.length round).scores =
      (p.scaled round).toList := by
  apply List.ext_getElem
  · simp [scaledWeights, packPopulation, Population.scaled]
  · intro i hi hj
    simp [scaledWeights, packPopulation, packRound, Population.scaled]

private theorem lookup_vectorGetD {n : ℕ} (v : Vector ℚ n) (i : ℕ) :
    v[i]?.getD 0 = Population.lookup v i := by
  by_cases hi : i < n <;> simp [Population.lookup, hi]

/-- The old and new expert weights after the fixed-share update. -/
def nextWeights (scaled : List ℚ) (newSize : ℕ) : List ℚ :=
  let total := ∑ j ∈ Finset.range newSize, scaled[j]?.getD 0
  let share := ((1/64 : ℚ) / newSize) * total
  List.ofFn fun j : Fin newSize => (1-1/64) * scaled[j.val]?.getD 0 + share

private theorem nextWeights_eq (p : Population N) (round : RoundResult N) (size : ℕ) :
    nextWeights (p.scaled round).toList size = (p.advanceVector round size).toList := by
  apply List.ext_getElem
  · simp [nextWeights, Population.advanceVector]
  · intro i hi hj
    simp [nextWeights, Population.advanceVector, lookup_vectorGetD]

/-- Add a real returned round, update the stored probe sequence, append the new
comparison-cell representatives, and materialize the next weight vector. -/
def advancePacked (N R : ℕ) (p : PackedPopulation) (seen : List PackedProbe) (round : PackedRound) :
    PackedPopulation × List PackedProbe :=
  let history := seen ++ round.log
  let entries := p.experts ++ packedBatch N R history
  (⟨entries, nextWeights (scaledWeights p.weights round.scores) entries.length⟩, history)

theorem advancePacked_eq (R : ℕ) (p : Population N) (round : RoundResult N) :
    advancePacked N R (packPopulation p) (p.probes.map packProbe) (packRound p.experts.length round) =
      (packPopulation (p.advance (Pool.batch N R) round),
        (p.advance (Pool.batch N R) round).probes.map packProbe) := by
  have append : p.probes.map packProbe ++ (packRound p.experts.length round).log =
      (p.probes ++ round.observations).map packProbe := by simp [packRound]
  simp only [advancePacked, append, packedBatch_eq, scaledWeights_eq, nextWeights_eq]
  simp [packPopulation, Population.advance]
  apply congrArg (fun size => (p.advanceVector round size).toList)
  simp

end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
