import OAI.Hierarchy.TaggedWideCursorPlacement
import OAI.Hierarchy.TaggedWideDatedHistoryRange
import OAI.Hierarchy.TaggedWireTransportAt

namespace OAI
/-! # Placing a complete funded cursor's reachable site bits in their original role cells -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles
open LinearAlgebra.SpectralBooks ChordGraph
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ReportSockets ProtocolRAM.Calendar WireTelescope CalendarTape
open scoped Classical BigOperators
variable {X : Type} {slots : Event→Slot X} {es : List Event} {start : X}
variable {h W k jobs : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
variable (cap : Public S h W k jobs → ℕ)
    (wire : Prefix.Cursor slots es start → Widths (siteLast h (2^W) k + 1))

/-- One concrete original-calendar row dictionary and its amounts at all
dates of a selected branch. The original row numbers and placed chords are
identical at every date, including rows whose funded amount is still zero. -/
structure BranchRoles (j : Path slots es start) where
  mark : Marks h W k jobs
  exclusive : Exclusive mark
  count : ℕ
  order : Fin count≃Source S π depth mark
  bits : Fin (es.length + 1) →Fin count→ℕ
  ident : Fin count→ℕ
  atWidth : ∀i,installedWidths (sorted S π depth mark ∘ order) (bits i)=wire (Prefix.boundaryIndex j i)
  fits : ∀i e b,bits i e≤cap (named S π depth mark exclusive order (e,b))

namespace BranchRoles
variable {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))} {depth : ℕ}
variable {cap : Public S h W k jobs → ℕ}
variable {wire : Prefix.Cursor slots es start → Widths (siteLast h (2^W) k + 1)}
variable (possible : ∀ c : Prefix.Cursor slots es start, Nonempty (Path slots c.todo c.mem))
variable (R : ∀ j : Path slots es start, BranchRoles S π depth cap wire j)
/-- The transport is a bijection on all site bits, so it changes only their Lean width index. -/
def atTime (j : Path slots es start) (i : Fin (es.length + 1)) : ((x : Fin (siteLast h (2^W) k + 1)) × SiteBit (wire (Prefix.boundaryIndex j i)) x) ↪ ((r : Public S h W k jobs)×Fin (cap r)) :=
  (NamedAperture.transport ((R j).atWidth i)).symm.toEmbedding.trans
    (statePlace S π depth (R j).mark (R j).exclusive (R j).order ((R j).bits i) cap ((R j).fits i))

def cells (j : Path slots es start) :=
  Prefix.rowPlacement
    (D := fun c => (x : Fin (siteLast h (2^W) k + 1)) × SiteBit (wire c) x)
    (Q := (r : Public S h W k jobs) × Fin (cap r)) j possible (atTime R)

theorem cells_at (j : Path slots es start) (i : Fin (es.length + 1)) :
    cells possible R j (Prefix.boundaryIndex j i)=atTime R j i :=
  Prefix.rowPlacement_boundary
    (D := fun c => (x : Fin (siteLast h (2^W) k + 1)) × SiteBit (wire c) x)
    (Q := (r : Public S h W k jobs) × Fin (cap r)) j possible (atTime R) i

theorem cells_range (j : Path slots es start) (i : Fin (es.length + 1)) (z : (r : Public S h W k jobs)×Fin (cap r)) :
    z∈Set.range (cells possible R j (Prefix.boundaryIndex j i)) ↔
      z∈Set.range (statePlace S π depth (R j).mark (R j).exclusive (R j).order ((R j).bits i) cap ((R j).fits i)) := by
  rw [cells_at]
  let eqv:=(NamedAperture.transport ((R j).atWidth i)).symm
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨eqv a,rfl⟩
  · rintro ⟨b,rfl⟩
    refine ⟨eqv.symm b,?_⟩
    exact congrArg (statePlace S π depth (R j).mark (R j).exclusive (R j).order ((R j).bits i) cap ((R j).fits i))
      (eqv.apply_symm_apply b)

set_option maxHeartbeats 1200000 in
/-- Word zero on each original three-column sheet decides membership in the
timeline dictionary after later native phases returned. -/
theorem observed (j : Path slots es start) (i : Fin (es.length + 1)) (n start native : ℕ) (before after:Memory native)
    (capWord:∀r,cap r<2^native)
    (page : DatedRoleSheets.roleFact n S π depth (R j).mark (R j).exclusive (R j).order
      start ((R j).bits i) (R j).ident before 0)
    (keep : ∀r : Public S h W k jobs,after (start+1+(shelfSlot S r).val)=before (start+1+(shelfSlot S r).val)) :
    (∀r : Public S h W k jobs,(after (start+1+(shelfSlot S r).val)).val≤cap r) ∧
      ∀z:(r : Public S h W k jobs)×Fin (cap r), z∈Set.range (cells possible R j (Prefix.boundaryIndex j i)) ↔
        z.2.val<(after (start+1+(shelfSlot S z.1).val)).val := by
  have words (e:Fin (R j).count) : (R j).bits i e<2^native :=
    ((R j).fits i e false).trans_lt (capWord _)
  have obs:=DatedRoleSheets.observed_range S π depth (R j).mark (R j).exclusive (R j).order
    ((R j).bits i) (R j).ident cap ((R j).fits i) n start before after words page keep
  exact ⟨obs.1,fun z=>(cells_range possible R j i z).trans (obs.2 z)⟩

end BranchRoles
end Hierarchy.ProbeStage.CoreBoard.HistoryRoles

end
end OAI
