import OAI.Computability.BorderVNP.TransmissionSafeAllocation
import OAI.Computability.BorderVNP.TransmissionScheduled

/-! # Endpoint address safety throughout the actual sequence of memory updates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- The routing read addresses themselves remain fixed if the frame fields are preserved. -/
theorem KeepsSchedule.sameReads {pub : Arg → ℕ} {R : ℕ} {m m' : ℕ → ℕ}
    (keep : KeepsSchedule pub R m m') (a : ℕ) : scheduleRead pub m' R a ↔ scheduleRead pub m R a := by
  simp only [scheduleRead, keep.field (by decide : 17 ≤ 25), keep.field (by decide : 18 ≤ 25)]

/-- Immutability of the concrete schedule composes across successive ranges. -/
theorem KeepsSchedule.trans {pub : Arg → ℕ} {R : ℕ} {m m' m'' : ℕ → ℕ}
    (k : KeepsSchedule pub R m m') (k' : KeepsSchedule pub R m' m'') : KeepsSchedule pub R m m'' :=
  fun a ha => (k' a ((k.sameReads a).mpr ha)).trans (k a ha)

/-- The destination-separation certificate established at the beginning of the directory
still applies at any later memory with the same routing table. -/
theorem Range.scheduleSeparated_of_keeps {r : Range w} {self : Word w} {pub : Arg → Word w}
    {m m' : Memory w} {R : ℕ} (keep : KeepsSchedule (readings pub) R (readings m) (readings m'))
    (sep : r.scheduleSeparated self pub m R) : r.scheduleSeparated self pub m' R := by
  intro mode sel d hd
  obtain ⟨fit, away⟩ := sep mode sel d hd
  exact ⟨fit, fun a ha => away a ((keep.sameReads a).mp ha)⟩

private theorem keeps_after_range {r : Range w} {self : Word w} {pub : Arg → Word w}
    {m : Memory w} {R : ℕ} (sep : r.scheduleSeparated self pub m R) (bits : ℕ → Bool) :
    KeepsSchedule (readings pub) R (readings m) (readings (r.apply self pub m bits)) := by
  cases sel : r.selected self with
  | none => simp only [Range.apply, sel]; exact fun _ _ => rfl
  | some role =>
    cases role with
    | none => simp only [Range.apply, sel, finishedMemory]; exact fun _ _ => rfl
    | some mode =>
      change KeepsSchedule _ R _ (readings ((r.selected self).elim m (fun role =>
        finishedMemory role pub (r.bank self) m bits)))
      rw [sel]
      exact rangeMemory_keepsSchedule mode pub (r.bank self) m bits r.width.val le_rfl
        (fun d hd => (sep mode sel d hd).1) (fun a ha d hd => (sep mode sel d hd).2 a ha)

/-- The actual frame, offsets, and oriented load entries survive all earlier ranges,
including ranges that overwrite destinations many times. Only the written intervals
of a team that actually handles a range are required to avoid those arrays. -/
theorem tableMemory_keepsSchedule (rows : ℕ → Range w) (self : Word w) (pub : Arg → Word w)
    (m : Memory w) (bits : ℕ → ℕ → Bool) (R k : ℕ)
    (sep : ∀ i < k, (rows i).scheduleSeparated self pub m R) :
    KeepsSchedule (readings pub) R (readings m) (readings (tableMemory rows self pub m bits k)) := by
  induction k with
  | zero => exact fun _ _ => rfl
  | succ k ih =>
    have prev := ih (fun i hi => sep i (by omega))
    exact prev.trans (keeps_after_range (Range.scheduleSeparated_of_keeps prev (sep k (by omega))) _)

/-- A numerical certificate for the entire sparse directory. Each row's addresses are
checked in the actual prefix memory. The schedule bounds need to be established just
once, before the first destination write. -/
theorem allTableArithmetic {f : BroadcastFrame} {width : Fin f.teams → Fin f.teams → ℕ}
    (rows : ℕ → Range w) (self : Word w) {pub : Arg → Word w} {m : Memory w}
    (a : Schedule f width pub m) (hs : self.val = f.team) (count : ℕ)
    (spans : ∀ i < count, ScheduledRange f width (rows i))
    (sep : ∀ i < count, (rows i).scheduleSeparated self pub m f.teams) :
    ∀ bits : ℕ → ℕ → Bool, ∀ i < count,
      (rows i).arithmeticSafe self pub (tableMemory rows self pub m bits i) := by
  intro bits i hi
  have keep := tableMemory_keepsSchedule rows self pub m bits f.teams i
    (fun j hj => sep j (hj.trans hi))
  exact Range.arithmeticSafe_of_tables (a.of_keeps keep) (spans i hi) self hs
    (Range.scheduleSeparated_of_keeps keep (sep i hi))

/-- In the actual memory at the beginning of any directory row, the predicate consumed
by the native forward proof equals just its physical sender comparison. -/
theorem table_allowed_iff_senderMatches {f : BroadcastFrame} {width : Fin f.teams → Fin f.teams → ℕ}
    (rows : ℕ → Range w) (self : Word w) {pub : Arg → Word w} {m : Memory w}
    (a : Schedule f width pub m) (hs : self.val = f.team) (count : ℕ)
    (spans : ∀ i < count, ScheduledRange f width (rows i))
    (kind : ∀ i < count, (rows i).kind = 0 ∨ (rows i).kind = 1)
    (sep : ∀ i < count, (rows i).scheduleSeparated self pub m f.teams)
    (sourceFit : ∀ i < count, (rows i).selected self = some (some .sendData) →
      (rows i).source.val+(rows i).width.val ≤ 2^w) (bits : ℕ → ℕ → Bool) {i : ℕ} (hi : i<count) :
    (rows i).allowed self pub (tableMemory rows self pub m bits i) (bits i) ↔
      (rows i).senderMatches self pub (tableMemory rows self pub m bits i) := by
  have keep := tableMemory_keepsSchedule rows self pub m bits f.teams i (fun j hj => sep j (hj.trans hi))
  exact Range.allowed_iff_senderMatches (a.of_keeps keep) (spans i hi) self hs (kind i hi)
    (Range.scheduleSeparated_of_keeps keep (sep i hi)) (sourceFit i hi) (bits i)

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
