import OAI.Computability.BorderVNP.PackedHistoryNormalizedProcessor
import OAI.Computability.BorderVNP.PackedSelectedEpochNodeFrames
import OAI.Computability.BorderVNP.PackedSelectedRecordRanges

/-! # Realizing the physical processor on every sufficiently large input length -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Adaptive Packing PublicCapacity
open Diagonal TeamScales Filter EnrichedOuter
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

universe u
variable {D m : ℕ} [NeZero D] {K : Type u} [Field K] {e : PaidIdentity K D m}

private theorem transfer_width {X : Type} {f g : Fintype X} {n m : ℕ}
    (h : @Fintype.card X f*n ≤ m) : @Fintype.card X g*n ≤ m :=
  (Subsingleton.elim f g) ▸ h

set_option maxHeartbeats 1500000 in
/-- On the physical processor ranges, every epoch is compiled from its actual
receipts. The global record, word and row bounds are discharged at the
calibrated cover depths, uniformly for every processor count and free port list. -/
theorem eventually_compiled (S : SiteSchedule e) (hm : 0 < m) {a x : ℕ} (scales : EpochScales S a x)
    (physical : ∀ d ≥ S.floor, S.FitsLevels d ∧ S.HasLeaves d ∧ S.RunsEnriched.{max 1 u,u} d) :
    ∃ A a₀ B b C p : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      ∀ base : ℕ, 1+base ≤ TeamScales.width n (1/2:ℝ) →
      ∀ (P : Type) [Fintype P] (bits : P → ℕ),
        let T := epochs scales.τ n
        let start := CoverScale.initialDepth (Cube D) r n
        let w := 60*logWidth r n
        ∃ deep : S.floor+1+S.drop*T ≤ start,
        ∃ R : Compiled bits deep (boundaryBudget S base) (innerCap S base) w, ∀ t (ht : t<T),
          let d := offset S start t
          (R.machine t ht).pre.size ≤ startCost (Fintype.card (Cube D)) (interiors S) A a₀ (fan S)
            (S.high d) w (boundaryShape S start t) ∧
          (R.machine t ht).post.size ≤ finishCost B b d w (boundaryShape S start (t+1)) ∧
          ∀ i : Fin S.rounds, ((R.machine t ht).step i.val i.isLt).size+(2*S.fanIn+4)+
            Fintype.card (Shortening.PublicDenseReceipt.Words
              (Shortening.PublicDenseReceipt.Seed (S.source.pattern i).bins (S.level d (i.val+1))) e.count w) ≤
            rowWork C (CoverScale.sites (Cube D) start) (logWidth r n) p ((before S start t i).parallel S.fanIn) := by
  obtain ⟨A,a₀,B,b,assemble⟩ := Boundary.epoch_of_nodes S
  obtain ⟨C,p,make⟩ := eventually_epoch_nodes.{u,0} S hm scales
  refine ⟨A,a₀,B,b,C,p,?_⟩
  filter_upwards [make,eventually_offsets S scales,eventually_record_words S scales,
    eventually_ranges S scales (fun _ => 0) (fun _ => 0)] with n compile room records ranges
  intro r hr base hbase P fp bits T start w
  have deep : S.floor+1+S.drop*T ≤ start := (room r hr).1
  choose node nodeRun nodeCost using fun (t : ℕ) (ht : t<T) =>
    compile r hr t ht (P := Port (fan S) P t) (bits := Adaptive.width bits (fan S) t)
  have build (t : ℕ) (ht : t<T) := by
    let d := offset S start t
    let v := fun j => (before S start t j).sites
    let edges := fun j => (before S start t j).edges
    obtain ⟨level,leaves,runs⟩ := physical d (levels S deep ht).1
    obtain ⟨startFits,endFits⟩ := boundary_fits S ((ranges r hr).2 t ht)
    exact assemble deep ht level leaves runs (boundaryShape S start) (boundaryBudget S base)
      v edges (innerCap S base t) w rfl rfl rfl startFits endFits (inner_zero S base t).symm.le
      (boundary_next S base t).le P bits (node t ht) (fun _ => (2*n*r)^2) (nodeRun t ht)
      (fun i => transfer_width (X := Cube D → Deck (S.level d i.val+1))
        (records r hr base hbase t ht i.val i.isLt.le)) (inner_next S base t)
  choose atLevel costs using build
  let R : Compiled bits deep (boundaryBudget S base) (innerCap S base) w := ⟨node,atLevel⟩
  refine ⟨deep,R,fun t ht => ⟨(costs t ht).1,(costs t ht).2,?_⟩⟩
  intro i
  rw [R.node_size]
  exact nodeCost t ht i

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
