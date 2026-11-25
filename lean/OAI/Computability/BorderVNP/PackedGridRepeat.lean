import OAI.Computability.BorderVNP.PackedGridCells
import OAI.Computability.BorderVNP.PackedProfiles
import OAI.Computability.BorderVNP.CrossingProfileNetwork

/-! # Keeping the bottom bundle on the same public grid

All copies of a cell occupy the same physical box. On each directed host channel the
copy-number slices of one wide cable carry the independent indices of the copies.
External slots remain individually addressable for the original exterior contraction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open BorderVNP.Packing BorderVNP.Shortening
open scoped Classical
variable {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits) (b : ℕ)

/-- Repeat every cable width in the physical grid while keeping one cable per direction
and cell. External ports carry the original copy labels. -/
abbrev repeatGrid : Network D (Fin b × P) (fun p => bits p.2) where
  Site := N.Site
  Edge := N.Edge
  finiteSite := N.finiteSite
  finiteEdge := N.finiteEdge
  src := N.src
  dst := N.dst
  width e := b * N.width e
  attach p := N.attach p.2
  position := N.position
  in_ball := N.in_ball

/-- Split every physical cable word into its consecutive one-copy words. -/
def repeatWords : (N.repeatGrid b).Assignment ≃ (Fin b → N.Assignment) where
  toFun z i e := Profile.blocks (z e) i
  invFun a e := Profile.blocks.symm (fun i => a i e)
  left_inv z := funext fun e => Profile.blocks.symm_apply_apply (z e)
  right_inv a := by funext i e; exact congrFun (Profile.blocks.apply_symm_apply (fun j => a j e)) i

variable {R : Type*} [CommSemiring R]

/-- The one private box reads its table on each cable slice, multiplying the independent
copy factors. The same private table and slice convention are used throughout the bundle. -/
noncomputable def repeatTables (table : N.Tables R) : (N.repeatGrid b).Tables R :=
  fun v a x => ∏ i : Fin b, table v (fun e => Profile.blocks (a e) i)
    (fun p => x ⟨(i,p.val),p.property⟩)

/-- The contracted repeated box computes the pointwise product on independent external
assignments. No copy's edge assignment is tied to the assignment of any other copy. -/
theorem value_repeatGrid (table : N.Tables R) (x : Ports (fun p : Fin b × P => bits p.2)) :
    (N.repeatGrid b).value (N.repeatTables b table) x =
      ∏ i : Fin b, N.value table (fun p => x (i,p)) := by
  classical
  unfold value
  rw [Fintype.prod_sum]
  apply Fintype.sum_equiv (N.repeatWords b)
  intro z
  change (∏ v : N.Site, ∏ i : Fin b, N.read table (N.repeatWords b z i) (fun p => x (i,p)) v) =
    ∏ i : Fin b, ∏ v : N.Site, N.read table (N.repeatWords b z i) (fun p => x (i,p)) v
  rw [Finset.prod_comm]

/-- In the paper's pack tree the physical bottom grid may replace the disjoint copies
without changing the tensor on its copy-indexed external slots. -/
theorem repeatGrid_tensor_parallel (table : N.Tables R) :
    (Pack.mk (N.repeatGrid b) (N.repeatTables b table)).tensor =
      (parallelPacks (fun _ : Fin b => (⟨N,table⟩ : ValuedPack R D bits))).tensor := by
  funext x
  exact (N.value_repeatGrid b table x).trans
    (parallel_value (fun _ : Fin b => N) (fun _ => table) x).symm

/-- Each local box and its directed neighbor records are charged once. The widths of
internal words are multiplied by `b`, and the external records repeat for every copy. -/
theorem repeatGrid_records [Fintype P] (expanded : Bool) (prior payload : N.Site → ℕ)
    (test : N.Site → Prop) :
    localRecords (N.repeatGrid b) expanded prior payload test =
      testedWidth (fun v => boxCost expanded (prior v) (payload v)) test +
      testedWidth (fun e => recordCost expanded (b * N.width e)) (fun e => test (N.src e)) +
      testedWidth (fun e => recordCost expanded (b * N.width e)) (fun e => test (N.dst e)) +
      b * testedWidth (fun p => recordCost expanded (bits p)) (fun p => test (N.attach p)) := by
  unfold localRecords
  congr 1
  unfold testedWidth
  rw [Fintype.sum_prod_type]
  simp

/-- On the Cayley grid, the exact charge per site is one box, two ends per direction,
and the copy-indexed external records. Every end is a single record of width `b*H`. -/
theorem repeatCayley_records {G J : Type} [Group G] [Fintype G] [Fintype J] [Fintype P]
    (cell : N.Site → G) (position : G → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (step : J → G) (H : ℕ) (expanded : Bool) (prior payload : G → ℕ) (g : G) :
    localRecords ((N.cayleyGrid cell position step H).repeatGrid b) expanded prior payload (· = g) =
      boxCost expanded (prior g) (payload g) + 2 * Fintype.card J * recordCost expanded (b * H) +
        b * testedWidth (fun i => recordCost expanded (bits i)) (fun i => cell (N.attach i) = g) := by
  rw [repeatGrid_records]
  have hc := N.cayleyGrid_records cell position step (b*H) expanded prior payload g
  unfold localRecords at hc
  exact congrArg (· + b * _) (Nat.add_right_cancel hc)

end Crossing.Network

end BorderVNP
end Computability
end OAI
