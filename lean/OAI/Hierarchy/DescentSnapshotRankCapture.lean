import OAI.Hierarchy.DescentNamedSnapshotRoster
import OAI.Hierarchy.DescentPhysicalSnapshotRanks
import OAI.Hierarchy.DescentLowCountBook

namespace OAI
/-! # Preserving archived snapshot ranks during the final count capture -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentExteriorReplay DescentDatedAddressBook
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
section RankFrames
variable {F P : Type} [Field F] [Fintype P] {d k wire hist w : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {I W : MarkedWorld F d P bits}
  {z₀ D₀ age grain degree : ℕ} {initial : Reached I G q ε S k 0 z₀ D₀ wire hist}
  {current : Reached W G q ε S k age grain degree wire hist}
  (p : Path initial current) (A : Snapshots k)

omit [Fintype P] in
/-- Every installed earlier reset directory has the range stored at its own date. -/
theorem Path.snapshotRanks_old_bank {root : ℕ} {m : Memory w} (past : p.snapshotRanks A root m) :
    ∀t<age,∀B,A.compact t=some B→B.Fits w root :=
  p.snapshot_rank_rooms A root m past

omit [Fintype P] in
/-- Count capture writes precisely the contiguous prefix of count words. -/
theorem Path.snapshotRanks_count_capture {lo hi first n : ℕ} (source : ℕ→ℕ) {m : Memory w}
    (ranks : p.snapshotRanks A lo m) (grows : lo≤hi)
    (disjoint : ∀t<age,∀B,A.compact t=some B→B.base+B.size≤first ∨ first+n≤B.base) :
    p.snapshotRanks A hi (DescentLowCountBook.output first source m n) := by
  apply p.snapshotRanks_banks A ranks grows
  intro t earlier bank atDate a lower upper
  apply DescentLowCountBook.frame
  rcases disjoint t earlier bank atDate with low|high
  · exact Or.inl (upper.trans_le low)
  · exact Or.inr (high.trans lower)
end RankFrames

end
end Hierarchy.DescentSixParty.Chronology

end OAI
