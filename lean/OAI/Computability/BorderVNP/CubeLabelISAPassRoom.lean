import OAI.Computability.BorderVNP.CubeLabelISAPassFootprint
import OAI.Computability.BorderVNP.CubeLabelISAChooser

/-! # Word and address bounds for the complete label pass -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

/-- The scored partial sums increase with the number of visited bins. -/
theorem PassBins.score_mono (b : PassBins) (m : ℕ → ℕ) : Monotone (b.score m) :=
  monotone_nat_of_le_succ fun i => by rw [b.score_succ]; omega

/-- The trial's full score bounds every intermediate score and each multiplication. -/
theorem PassRoom.trial (p : Frame) (w c v : ℕ) (m : ℕ → ℕ) (es : List Incident)
    (initial : ∀ i < p.Z^2+p.Z, p.room w c v i m es)
    (cap : p.score c m es v < 2^w) : PassRoom p w c v m es false := by
  refine ⟨initial,fun _ _ => rfl,?_⟩
  intro i hi
  let b := p.bins c v m es
  change 0 + b.score m i + m (b.addr i) * b.after i < 2^w
  rw [Nat.zero_add, ← b.score_succ]
  exact (b.score_mono m (Nat.succ_le_of_lt hi)).trans_lt cap

/-- Disjoint cache segments assign a unique physical address to every bin ordinal. -/
theorem Frame.cacheAddr_inj (p : Frame)
    (segments : p.cables+p.Z^2 ≤ p.data ∨ p.data+p.Z ≤ p.cables)
    {i j : ℕ} (hi : i < p.Z^2+p.Z) (hj : j < p.Z^2+p.Z) (eq : p.cacheAddr i = p.cacheAddr j) :
    i = j := by
  unfold cacheAddr at eq
  split at eq <;> split at eq <;> omega

/-- A commit can use initial fit bounds at every bin, since earlier writes touch
distinct cache addresses and leave the scanner's input words intact. -/
theorem PassRoom.commit (p : Frame) (w c v : ℕ) (m : ℕ → ℕ) (es : List Incident)
    (initial : ∀ i < p.Z^2+p.Z, p.room w c v i m es)
    (segments : p.cables+p.Z^2 ≤ p.data ∨ p.data+p.Z ≤ p.cables)
    (off : ∀ a ∈ p.probes c m es, ∀ j < p.Z^2+p.Z, a ≠ p.cacheAddr j)
    (safe : ∀ i < p.Z^2+p.Z,
      let b := p.bins c v m es
      b.before i ≤ m (b.addr i) ∧ m (b.addr i) - b.before i + b.after i < 2^w) :
    PassRoom p w c v m es true := by
  let b := p.bins c v m es
  have transport (i : ℕ) (hi : i < p.Z^2+p.Z) := p.pass_room true w c v i m es (initial i hi)
    (fun a ha j hj => off a ha j (hj.trans hi))
  refine ⟨fun i hi => (transport i hi).1,fun i hi => (transport i hi).2,?_⟩
  intro i hi
  have orig : b.image m i (b.addr i) = m (b.addr i) := b.image_off m i (b.addr i) (by
    intro j hj eq
    exact (Nat.ne_of_gt hj) (p.cacheAddr_inj segments hi (hj.trans hi) eq))
  change b.before i ≤ b.image m i (b.addr i) ∧ b.image m i (b.addr i)-b.before i+b.after i < 2^w
  rw [orig]
  exact safe i hi

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
