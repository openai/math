import OAI.Computability.BorderVNP.PackedFrozenNodeSchedule
import OAI.Computability.BorderVNP.PackedFrozenSharedNode
import OAI.Computability.BorderVNP.PackedFrozenSelectedMeasures

/-! # Gate budget for the complete tree of immutable command writers

The old-source mask and the selected tape writer run beside the real
width-augmented successor. All previous records use the actual selected
format's row count. The total estimate charges every occurrence of these
frames in the rooted tree.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Cover Epoch Shortening Shortening.PublicCapacity Shortening.StaticRows
open Shortening.PublicDenseReceipt PackedHistoryCircuit PackedHistoryCircuit.Normalized.SelectedSchedule
open Diagonal TeamScales Filter CellAddressCircuit VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)

omit [NeZero D] in
/-- The old presence mask, two literals, and the immutable writer fit one public
rectangle bound. Geometry and its width extension are charged separately by
the sizes of the two source frames appearing in this very circuit. -/
theorem Shared.install_rowWork {M V L C p : ℕ} (shape : Shape) (rows : M ≤ shape.edges) (hL : 1≤L)
    {Input MeasuredInput A Widths Tape : Type} [Fintype Input] [Fintype MeasuredInput] [Fintype Widths] [Fintype Tape]
    (O : Operands MeasuredInput A D M (60*L)) (fromGeo : MeasuredInput → Input) (next : Frame Input (Widths ⊕ Unit))
    (emit : Frame (Shared.Context Input O.Pin Widths M (60*L)) Tape) (bound : emit.size ≤ rowWork C V L p shape) :
    (Shared.install O fromGeo next emit).size ≤ O.frame.size+next.size+rowWork (C+186) V L (max 1 p) shape := by
  let v := shape.volume V
  have v₁ : 1 ≤ v := by unfold v Shape.volume; omega
  have e' : M ≤ v := rows.trans (by unfold v Shape.volume; omega)
  have unit : 1 ≤ v*L := Nat.mul_pos v₁ hL
  have mask : (M*(60*L)+2)*3 ≤ 186*v*L := by nlinarith only [unit,Nat.mul_le_mul_right L e']
  have h₁ : L ≤ L^(max 1 p) := by simpa only [pow_one] using Nat.pow_le_pow_right hL (le_max_left 1 p)
  have hp := Nat.pow_le_pow_right hL (le_max_right 1 p)
  have both : (M*(60*L)+2)*3 + emit.size ≤ rowWork (C+186) V L (max 1 p) shape :=
    (Nat.add_le_add mask bound).trans ((Nat.add_le_add (Nat.mul_le_mul_left (186*v) h₁)
      (Nat.mul_le_mul_left (C*v) hp)).trans_eq (by unfold rowWork; dsimp only [v]; ring))
  have total := Shared.install_size O fromGeo next emit
  omega

/-- Price the selected writer on any prior format that fits the scheduled
row slots, with the actual seed and port types carried through their
cardinality equalities. -/
theorem NodeWork.on_rows {hm : 0 < m} {start baseRows t L C p : ℕ} {i : Fin S.rounds}
    (prior : Format) (rows : Fintype.card prior.Rows ≤ priorSlots S start baseRows t i)
    (bound : NodeWork S hm start t i baseRows L C p) :
    let old := (before S start t i).parallel S.fanIn
    let w := 60*L
    let lev := stageLevel S start t (i.val+1)
    ∀ {I A σ : Type} [Fintype I] [Fintype A] [Fintype σ] (O : Operands I A D old.edges w),
      O.keyBits = operandBits D (S.source.pattern i).bins.Bin lev →
      ∀ (selectPin : O.Pin → σ) (guess : A → Fin e.count → Fin w → σ),
      let pass := selectedPass e O selectPin guess hm
      ∀ {s np : ℕ}, s = seedCount S start t i → np = portSlots S start t (i.val+1) →
        ∀ (seed : A ≃ Fin s) (oldRoom : (before S start t i).sites ≤ 2^w) (newRoom : old.sites ≤ 2^w)
        (childPin : Fin S.fanIn × Pins prior.Rows prior.Payload w → σ)
        {cells cells' cw cw' : ℕ} (oldF : Fields old.sites old.edges np cells w cw w σ)
        (newF : Fields (siteCapacity e old.sites s) (edgeCapacity e old.edges s) np cells' w cw' w σ)
        (work extent : Fin old.sites → Fin w → σ) (occupied : Fin old.edges → σ) (ports : Fin np → Bool)
        (successor : Fin (edgeCapacity e old.edges s) → σ),
          (Node.frame e (0,false) hm seed.toEmbedding (carryFrame oldRoom newRoom childPin)
            oldF newF pass.cut pass.counts work extent occupied ports successor).size ≤
            rowWork C (CoverScale.sites (Cube D) start) L p old := by
  intro old w lev I A σ _ _ _ O key selectPin guess pass s np seedSize numPorts
  subst s; subst np
  intro seed oldRoom newRoom childPin cells cells' cw cw' oldF newF work extent occupied ports successor
  exact bound I A σ O key selectPin guess prior.Rows prior.Payload
    rows
    oldRoom newRoom childPin seed oldF newF work extent occupied ports successor

/-- Apply the budget to the actual carried schema and true scheduled seed and
port cardinalities, allowing the address types to use their physical names. -/
theorem NodeWork.on_format {hm : 0 < m} {start t T L C p : ℕ} {i : Fin S.rounds}
    (base : Format) (deep : S.floor+1+S.drop*T ≤ start) (ht : t<T)
    (bound : NodeWork S hm start t i (Fintype.card base.Rows) L C p) :
    let old := (before S start t i).parallel S.fanIn
    let w := 60*L
    let prior := ProgramSchemas.stage S start w base t i
    let lev := stageLevel S start t (i.val+1)
    ∀ {I A σ : Type} [Fintype I] [Fintype A] [Fintype σ] (O : Operands I A D old.edges w),
      O.keyBits = operandBits D (S.source.pattern i).bins.Bin lev →
      ∀ (selectPin : O.Pin → σ) (guess : A → Fin e.count → Fin w → σ),
      let pass := selectedPass e O selectPin guess hm
      ∀ {s np : ℕ}, s = seedCount S start t i → np = portSlots S start t (i.val+1) →
        ∀ (seed : A ≃ Fin s) (oldRoom : (before S start t i).sites ≤ 2^w) (newRoom : old.sites ≤ 2^w)
        (childPin : Fin S.fanIn × Pins prior.Rows prior.Payload w → σ)
        {cells cells' cw cw' : ℕ} (oldF : Fields old.sites old.edges np cells w cw w σ)
        (newF : Fields (siteCapacity e old.sites s) (edgeCapacity e old.edges s) np cells' w cw' w σ)
        (work extent : Fin old.sites → Fin w → σ) (occupied : Fin old.edges → σ) (ports : Fin np → Bool)
        (successor : Fin (edgeCapacity e old.edges s) → σ),
          (Node.frame e (0,false) hm seed.toEmbedding (carryFrame oldRoom newRoom childPin)
            oldF newF pass.cut pass.counts work extent occupied ports successor).size ≤
            rowWork C (CoverScale.sites (Cube D) start) L p old := by
  exact NodeWork.on_rows S (ProgramSchemas.stage S start (60*L) base t i)
    (ProgramSchemas.stage_slots S start (60*L) base deep ht i i.isLt.le).le bound

/-- The sum of the actual per-node ceilings, including the old presence mask,
is strictly below the paper's public-work exponent. The same fixed constants
bound the physical node circuits for every reached level and base format. -/
theorem eventually_frozen_tree_work {a x : ℕ} (hm : 0 < m) (s : EpochScales S a x) (C₀ : ℕ) :
    ∃ C p : ℕ, ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
      let start := CoverScale.initialDepth (Cube D) r n
      let T := epochs s.τ n
      let V := CoverScale.sites (Cube D) start
      let L := logWidth r n
      (∀ base ≤ C₀*physicalRows (bottom (D := D) start), ∀ t < T, ∀ i : Fin S.rounds, NodeWork S hm start t i base L C p) ∧
      (treeWork S.fanIn S.rounds T (fun t i => rowWork (C+186) V L (max 1 p) ((before S start t i).parallel S.fanIn)):ℝ)
        < r*(n:ℝ)^(915/1000:ℝ) := by
  obtain ⟨C,p,localWork⟩ := eventually_frozen_node_work S hm s C₀
  obtain ⟨ω,hω,tree⟩ := eventually_treeWork S s (C+186) (max 1 p)
  refine ⟨C,p,ω,hω,?_⟩
  filter_upwards [localWork,tree,eventually_ranges S s (fun _ => 0) (fun _ => 0)] with n local' total ranges
  intro r hr hrmax start T V L
  exact ⟨local' r hr,total r hr hrmax (ranges r hr).1 _ (fun _ _ => le_rfl)⟩

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
