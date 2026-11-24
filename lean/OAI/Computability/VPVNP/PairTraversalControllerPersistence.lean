import OAI.Computability.VPVNP.PairTraversalControllerInputs

/-!
# Persistent traversal parameters during the role and row scans

Only six terminal scalars are used by the traversal workers. Their level
scalars all precede the row arena. Agreement on these words therefore
preserves each chronological worker's count, role and parameter bank.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalControllerInputs

open BurstRAM CompressorRecords LocalHistory Compression TraversalRows TraversalRoles

variable {w : ℕ} {pub : Fin 11 → Word w} {m m' : Memory w} {H first pitch offset cap base : ℕ}
variable {old : TaggedLayer} {ls : List (Fiber w)}

/-- The terminal words read by the traversal stage. -/
def terminalScalars : Finset ℕ := {1, 7, 14, 15, 16, 17}

/-- Transfer resident scalars after any partial scan. Only the terminal
words read by the controller need survive writes in the high header. -/
theorem Resident.transfer (d : Resident pub m H first pitch offset cap base old ls)
    (headersBefore : ∀ j ≤ ls.length, first + j*pitch + 28 ≤ base)
    (below : ∀ x < base, m' x = m x)
    (terminal : ∀ f ∈ terminalScalars, m' (H+f) = m (H+f)) :
    Resident pub m' H first pitch offset cap base old ls := by
  have atLevel (j field : ℕ) (hj : j ≤ ls.length) (hf : field < 28) :
      m' (first+j*pitch+field) = m (first+j*pitch+field) :=
    below _ ((Nat.add_lt_add_left hf _).trans_le (headersBefore j hj))
  refine ⟨d.header,d.headerFits,d.levelFits,
    (terminal 16 (by decide)).trans d.firstHead,(terminal 17 (by decide)).trans d.levelPitch,
    (congrArg Fin.val (terminal 1 (by decide))).trans d.levels,
    (terminal 14 (by decide)).trans d.roleOffset,(terminal 15 (by decide)).trans d.rowStride,
    fun j hj => (atLevel j 14 hj (by decide)).trans (d.currentBase j hj),
    fun j => (atLevel j.val 27 (by simpa using j.isLt) (by decide)).trans (d.role j),
    ?_, fun h => (congrArg Fin.val (terminal 7 (by decide))).trans (d.terminalSites h),
    fun i => (congrArg Fin.val (atLevel i.val 22 i.isLt.le (by decide))).trans (d.produced i),
    fun i => (atLevel i.val 24 i.isLt.le (by decide)).trans (d.childCounts i),
    fun i => (atLevel i.val 25 i.isLt.le (by decide)).trans (d.childLists i),
    fun i => (atLevel i.val 26 i.isLt.le (by decide)).trans (d.childCapacity i)⟩
  intro h
  have same := atLevel 0 21 (Nat.zero_le _) (by decide)
  simp only [Nat.zero_mul,Nat.add_zero] at same
  exact (congrArg Fin.val same).trans (d.initial h)

variable {k A : Type*} [Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {n : ℕ} (T : ℕ)
variable (hT : T*S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices) (raw : Memory w)
variable (ds : let vs := executeLevels B f hf T hT X z
  (i : Fin vs.length) → LevelDirectory vs[i] raw base)

/-- Every reference prefix sees the same selected schedule and initial
site count when its row and tag writes preserve the resident headers. -/
theorem selected_prefix_schedule
    (d : Resident pub m H first pitch offset B.recordLimit base
      ⟨leafLayer (siteOrder X),.cursor⟩ (levelFibers (executeLevels B f hf T hT X z) ds))
    (headersBefore : ∀ j ≤ (executeLevels B f hf T hT X z).length, first+j*pitch+28 ≤ base)
    (refs : List (Report w))
    (below : ∀ q ≤ refs.length, ∀ x < base, after m (eventLog (refs.take q)) x = m x)
    (terminal : ∀ q ≤ refs.length, ∀ f ∈ terminalScalars,
      after m (eventLog (refs.take q)) (H+f) = m (H+f)) :
    ∀ q ≤ refs.length, let m' := after m (eventLog (refs.take q))
      Schedule pub m' offset B.recordLimit base (selected B f hf T hT X z)
        (selectedJobs B f hf T hT X z base raw ds) ∧ (siteCount pub m' 0).val = X.positions := by
  intro q hq m'
  have d' := d.transfer (by simpa only [levelFibers,List.length_ofFn] using headersBefore)
    (below q hq) (terminal q hq)
  refine ⟨selected_schedule B f hf T hT X z base raw ds d', (count_zero d').trans ?_⟩
  change (siteOrder X).length = Fintype.card X.network.Site
  simpa only [Fintype.card_fin] using Fintype.card_congr (siteOrder X).entries

end PairSimulation.TraversalControllerInputs

end VPVNP
end Computability
end OAI
