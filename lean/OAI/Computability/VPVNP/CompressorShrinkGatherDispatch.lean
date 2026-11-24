import OAI.Computability.VPVNP.CompressorShrinkDemandGather
import OAI.Computability.VPVNP.CompressorRecordsOrdinalFootprint
import OAI.Computability.VPVNP.RAMChoicePrefix

/-!
# Dispatching the shrinking width gather

The finite width worker reads only its two sorted rectangles. Its
writes stay within the dense demand pairs. The same reports can thus
be replayed after the online scheduler has prepared the active frame.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkDemandGather

open BurstRAM Schedule OrdinalRun SourceTransport
open scoped Fin.CommRing

variable {B Q w : ℕ} (p : Fin 6 → Word w) (L : Layout B Q p)

/-- Union of the two source rectangles from which the gather worker may read across `B` rows,
each with its own base and stride. -/
def ReadRegion (B : ℕ) (p : Fin 6 → Word w) (x : ℕ) : Prop :=
  ((p 3).val ≤ x ∧ x < (p 3).val+B*(p 1).val) ∨ ((p 4).val ≤ x ∧ x < (p 4).val+B*(p 2).val)

/-- Dense output interval for the width pairs, containing two words for each of the `B * Q`
visited motifs. -/
def WriteRegion (B Q : ℕ) (p : Fin 6 → Word w) (x : ℕ) : Prop :=
  (p 5).val ≤ x ∧ x < (p 5).val+2*(B*Q)

include L in
private theorem row_footprint {j : ℕ} (hj : j < B*Q) (mem : Memory w) :
    Reads (ReadRegion B p) (visits p (j : Word w) mem).events ∧
      Writes (WriteRegion B Q p) (visits p (j : Word w) mem).events := by
  obtain ⟨dst,dst'⟩ := dest_bounds L hj
  change (ShrinkDemandGather.dst p (j : Word w)).val = _ at dst
  change (ShrinkDemandGather.dst p (j : Word w)+1).val = _ at dst'
  have ab := source_range L hj 1 3 L.abStride L.abFit L.abApart
  have cd := source_range L hj 2 4 L.cdStride L.cdFit L.cdApart
  constructor
  · intro a v h
    simp [visits] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · exact .inl ab
    · exact .inr cd
  · intro a v h
    simp [visits] at h
    rcases h with ⟨rfl,_⟩ | ⟨rfl,_⟩
    · unfold WriteRegion; rw [dst]; omega
    · unfold WriteRegion; rw [dst']; omega

variable {cap : ℕ} (hcap : cost < cap) (mem : Memory w) (rs : List (Report w))
variable (run : runSegment (program p) cap (some 0) mem (List.replicate (B*Q) []) = some rs)

include L hcap run

/-- All reads can be transported across control-memory changes. All writes
are confined to the dense output even for the last pair. -/
theorem footprints : Reads (ReadRegion B p) (eventLog rs) ∧ Writes (WriteRegion B Q p) (eventLog rs) := by
  let cursor (i : ℕ) : Word w := i
  apply OrdinalRun.footprint (program p) cap cursor (B*Q) (fun _ _ => True) _ _ _ 0 _ mem rs (by simp) trivial run
  intro j hj m _ bits r h
  have eqn := (execute_prefix_unique (visit_run p (j : Word w) m hcap)
    (show execute (program p) cap ((program p).start (j : Word w)) m ([] ++ bits) = some r from h)).2
  subst r
  obtain ⟨rd,wr⟩ := row_footprint p L hj m
  exact ⟨by simp [cursor,visits_result],trivial,rd,wr⟩

/-- The complete dense gather satisfies every exclusive guard and preserves
the frame, tag, ordinal and row count of the online dispatcher. -/
theorem valid_trace {d : ℕ} (C : Catalog d) (worker : Fin d) (ports : Ports w)
    (pub : Fin (C worker).params → Word w) (stopFit : B*Q < 2^w)
    (apart : ∀ x, ControlCell (C worker).params ports x → ¬ WriteRegion B Q p x)
    (ready : Ready C worker ports pub (B*Q : ℕ) mem) :
    ValidTrace C worker ports pub (B*Q : ℕ) 0 mem rs ∧ Preserved (C worker).params ports mem (after mem (eventLog rs)) := by
  let cursor (i : ℕ) : Word w := i
  have active (i : ℕ) (hi : i < B*Q) : cursor i < cursor (B*Q) := by
    change i%(2^w) < (B*Q)%(2^w)
    rwa [Nat.mod_eq_of_lt (hi.trans stopFit),Nat.mod_eq_of_lt stopFit]
  have advance (j : ℕ) (hj : j < B*Q) (m : Memory w) (_ : True) (bits : List Bool) (r : Report w)
      (h : execute (program p) cap ((program p).start (cursor j)) m bits = some r) :
      r.result = some (cursor (j+1)) ∧ True ∧ Preserved (C worker).params ports m (after m r.events) := by
    have eqn := (execute_prefix_unique (visit_run p (j : Word w) m hcap)
      (show execute (program p) cap ((program p).start (j : Word w)) m ([] ++ bits) = some r from h)).2
    subst r
    exact ⟨by simp [cursor,visits_result],trivial,fun x hx =>
      after_outside m (row_footprint p L hj m).2 (apart x hx)⟩
  obtain ⟨h,_,keep⟩ := OrdinalRun.validTrace C worker ports (program p) cap pub (cursor (B*Q)) cursor (B*Q)
    (fun _ _ => True) active le_rfl advance 0 _ mem rs (by simp) trivial ready run
  exact ⟨h,keep⟩

end CompressorRecords.ShrinkDemandGather

end VPVNP
end Computability
end OAI
