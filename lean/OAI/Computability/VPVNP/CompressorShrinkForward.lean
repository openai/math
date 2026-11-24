import OAI.Computability.VPVNP.CompressorBlockGroups
import OAI.Computability.VPVNP.CompressorSourceGroups

/-!
# Joining the scheduled shrinking visit windows

The concrete script breaks a shrinking substep into twelve chronological groups.
The live ordinal of each group's first visit includes the initial startup rows, all
completed compression blocks, all preceding shrinking substeps, and all earlier
groups of this substep. Source runs, clock and memory checks, and operand readback
are transported across these offsets by concatenating the true packet lists.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceOnline

open BurstRAM BlockPlanner DescriptorSpace

variable {w : ℕ} {A : Script} {L : Layout} {base : Word w} {cap total : ℕ}

namespace Group

/-- Concatenate finitely many checked groups, each evaluated from the post-memory of
all groups before it. The earlier packet lengths determine the current ordinal. -/
theorem flatten (ordinal : ℕ) (m : Memory w) (batches : List (List (Packet A w)))
    (runs : ∀ i : Fin batches.length,
      Group A L base cap (ordinal+(batches.take i.val).flatten.length) total
        (post m (batches.take i.val).flatten) batches[i.val]) :
    Group A L base cap ordinal total m batches.flatten := by
  induction batches generalizing ordinal m with
  | nil => exact nil
  | cons ps batches ih =>
    have head : Group A L base cap ordinal total m ps := by simpa [post,eventLog,after] using runs 0
    have tail (i : Fin batches.length) :
        Group A L base cap (ordinal+ps.length+(batches.take i.val).flatten.length) total
          (post (post m ps) (batches.take i.val).flatten) batches[i.val] := by
      have h := runs (Fin.succ i)
      simpa only [Fin.val_succ,List.take_succ_cons,List.flatten_cons,List.length_append,
        Nat.add_assoc,List.getElem_cons_succ,post_append] using h
    exact head.append (ih (ordinal+ps.length) (post m ps) tail)

end Group

end CompressorRecords.SourceOnline

namespace CompressorRecords.ShrinkForward

open BurstRAM Compression BlockPlanner DescriptorSpace SourceOnline

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {w : ℕ} (L : Layout) (base : Word w) (cap total round : ℕ)
local notation "A" => BlockProgram.script B

/-- Ordinal of the first call in the substep, including all earlier iterations. -/
noncomputable def first := (A).initial.length + round*(A).block.length + (BlockIndex.earlier B i).length

/-- The static visit count in a prefix of the twelve constituent windows. -/
noncomputable def visitsBefore (j : ℕ) := ((BlockGroups.parts B i).take j).flatten.length

/-- A physical group retains all data and guard checks, and is attached to the actual
catalog occurrences of this particular shrinking substep. -/
structure Groups (m : Memory w) (rows : Fin 12 → List (Packet A w)) : Prop where
  length : ∀ j, (rows j).length = ((BlockGroups.parts B i)[j.val]'j.isLt).length
  checked : ∀ j,
    Group A L base cap (first B i round + visitsBefore B i j.val) total
      (post m ((List.ofFn rows).take j.val).flatten) (rows j)

/-- Source execution and operand/clock/footprint facts for the whole chronological
window of the actual online script. -/
theorem joined (m : Memory w) (rows : Fin 12 → List (Packet A w))
    (h : Groups B i L base cap total round m rows) :
    Group A L base cap (first B i round) total m (List.ofFn rows).flatten := by
  apply Group.flatten
  intro j
  let u : Fin 12 := ⟨j.val, by simpa using j.isLt⟩
  have lengths : (List.ofFn rows).map List.length = (BlockGroups.parts B i).map List.length := by
    apply List.ext_getElem
    · simp [BlockGroups.parts_length]
    · intro z hz hz'
      have hv : z<12 := by simpa using hz
      simp only [List.getElem_map,List.getElem_ofFn]
      exact h.length ⟨z,hv⟩
  have offset : ((List.ofFn rows).take j.val).flatten.length = visitsBefore B i j.val := by
    rw [visitsBefore,List.length_flatten,List.length_flatten,List.map_take,List.map_take,lengths]
  rw [offset]
  rw [List.getElem_ofFn]
  exact h.checked u

end CompressorRecords.ShrinkForward

end VPVNP
end Computability
end OAI
