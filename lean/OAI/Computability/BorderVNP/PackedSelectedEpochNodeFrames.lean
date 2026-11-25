import OAI.Computability.BorderVNP.ShortenEnrichedPathFrames
import OAI.Computability.BorderVNP.PackedSelectedEpochOffset
import OAI.Computability.BorderVNP.PackedSelectedTreeWork

/-! # Realizing all physical combining frames in an executed epoch

At the actual starting depth, the public range theorem supplies every positive
decoder depth, selector width and allocated rectangle. Thus one compiled
family operates on the epoch's assigned named states with the common
processor word width. Its gate, flag and histogram cost is measured on the
actual joined rectangle at each stage.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing Cover Cover.Frame Epoch Shortening Shortening.Adaptive Shortening.PublicDenseReceipt
open Packing PublicCapacity Diagonal TeamScales Filter
open scoped Classical BorderVNP.Epoch.Cube

universe u v
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m} (S : SiteSchedule e)

/-- The template's seed count is exactly the size of the scheduled directory,
including the relative bin tag. -/
theorem stageSeeds_offset {start T t : ℕ} (deep : S.floor+1+S.drop*T ≤ start) (ht : t<T)
    (i : Fin S.rounds) :
    S.source.stageSeeds S.last (S.high (EnrichedOuter.offset S start t)) i = seedCount S start t i := by
  have hl := level_offset S deep ht (i.val+1)
  simp only [SourcePath.stageSeeds,Seed,Fintype.card_prod,seedCount,dite_eq_left i.isLt]
  change Fintype.card (Cube D → Deck (S.level (EnrichedOuter.offset S start t) (i.val+1)+1)) * _ = _
  rw [hl]

/-- The checked range at the processor's actual public word width discharges
every numerical premise of the scheduled named-node compiler. -/
theorem Ranges.nodeRange {r n start T t : ℕ} {i : Fin S.rounds} {den cut : ℕ}
    (ranges : Ranges S r n start t i den cut) (deep : S.floor+1+S.drop*T ≤ start) (ht : t<T) :
    S.source.NodeRange S.last (S.high (EnrichedOuter.offset S start t)) S.fanIn
      (fun j => (before S start t j).sites) (fun j => (before S start t j).edges)
      (fun _ => (2*n*r)^2) (60*logWidth r n) i den cut := by
  let d := EnrichedOuter.offset S start t
  have level (j : ℕ) : S.source.asPath.depth S.last (S.high d) j = stageLevel S start t j :=
    level_offset S deep ht j
  have seed := stageSeeds_offset S deep ht i
  obtain ⟨a,ha,hlev,hfloor,hcut⟩ := ranges.depth
  obtain ⟨hd,hw,hscore,hs,_he,hsd,hv',he',hc,_pad,_log⟩ := ranges.words
  refine ⟨⟨a,ha,(congrArg (·+1) (level _)).trans hlev⟩, (level _) ▸ hfloor, (level _) ▸ hcut, ?_, ?_, ?_, ?_⟩
  · rw [seed,before_next]
    rfl
  · rw [seed,before_next]
    rfl
  · refine ⟨hd,hw,?_⟩
    rw [level]
    exact hscore
  · rw [seed]
    exact ⟨hs,hsd,hv',he',hc⟩

/-- For every sufficiently large length, all executed epochs admit their
actual named frame families, uniformly in the processor count and port type.
The full measured source receipt and the joined-rectangle work bound hold
for the same frames. -/
theorem eventually_epoch_nodes (hm : 0 < m) {a x : ℕ} (scales : EpochScales S a x) :
    ∃ C p : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      let start := CoverScale.initialDepth (Cube D) r n
      ∀ t < epochs scales.τ n, ∀ {P : Type} {bits : P → ℕ},
        let high := S.high (EnrichedOuter.offset S start t)
        let V := fun j => (before S start t j).sites
        let E := fun j => (before S start t j).edges
        let w := 60*logWidth r n
        ∃ nodes : ∀ i : Fin S.rounds, S.source.Node S.last high V E w S.fanIn i,
          (∀ i, SourceTemplate.NodeRun.{u,v} (P := Port S.fanIn P i.val) (bits := width bits S.fanIn i.val)
            (S.source.pattern i) (S.source.stepDepth S.last high i) S.positiveFanIn
            (S.source.catalog (i.val+1)) ((2*n*r)^2) (nodes i)) ∧
          ∀ i, (nodes i).size+(2*S.fanIn+4)+Fintype.card (Words
            (Seed (S.source.pattern i).bins (S.source.asPath.depth S.last high (i.val+1))) e.count w) ≤
            rowWork C (CoverScale.sites (Cube D) start) (logWidth r n) p
              ((before S start t i).parallel S.fanIn) := by
  obtain ⟨den,cut,A,p,_hden,make⟩ := SourcePath.pathNode_frames.{u,v} S.source hm
  refine ⟨receiptFactor S.fanIn (bins S) A p,p,?_⟩
  filter_upwards [eventually_ranges S scales den cut,eventually_offsets S scales] with n range offsets
  intro r hr start t ht P bits high V E w
  have deep := (offsets r hr).1
  have hi (i : Fin S.rounds) : Ranges S r n start t i (den i) (cut i) := (range r hr).2 t ht i
  have hnode (i : Fin S.rounds) := Ranges.nodeRange S (hi i) deep ht
  obtain ⟨nodes,semantics,work⟩ := make (P := P) (bits := bits) S.last high S.fanIn S.positiveFanIn
    V E (fun _ => (2*n*r)^2) w hnode
  refine ⟨nodes,semantics,?_⟩
  intro i
  obtain ⟨_hd,_hw,_hscore,hs,he,_hseed,_hv',_he',_hc,hpad,_hlog⟩ := (hi i).words
  have hcost := work i (2^w) hs he hpad
  apply receipt_rowWork S (hi i) A p _
  have hlevel : S.source.asPath.depth S.last high (i.val+1) = stageLevel S start t (i.val+1) :=
    level_offset S deep ht _
  have hseed : S.source.stageSeeds S.last high i = seedCount S start t i := stageSeeds_offset S deep ht i
  simpa only [SourcePath.nodeRows,hlevel,hseed,CoverScale.sites,V,E,w] using hcost

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
