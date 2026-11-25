import OAI.Computability.BorderVNP.RoutingISATableAddressImage
import OAI.Computability.BorderVNP.RoutingISAPaddingSchedule
import OAI.Computability.BorderVNP.TransmissionReadPreservation

/-!
# Immutable words of the physical endpoint schedule

The address program reads the frame, the cubic partner-prefix array and the square oriented
totals array. The following lemmas carry their *actual* values through each selected scan,
allowing writable input slots elsewhere in memory to change.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

/-- Words read to locate scheduled physical endpoint bits in a team of `R` peers. -/
def scheduleRead (pub : Arg → ℕ) (m : ℕ → ℕ) (R a : ℕ) : Prop :=
  (∃ i ≤ 25, a = pub 0+i) ∨
    (∃ u v j : Fin R, a = tripleIndex (frameField pub m 17) R u v j) ∨
    ∃ u v : Fin R, a = pairIndex (frameField pub m 18) R u v

/-- Equality of all addressed immutable words required by a physical routing lookup. -/
def KeepsSchedule (pub : Arg → ℕ) (R : ℕ) (m m' : ℕ → ℕ) : Prop :=
  ∀ a, scheduleRead pub m R a → m' a = m a

/-- The stored base address and dimension words survive any writes outside the table. -/
theorem KeepsSchedule.field {pub : Arg → ℕ} {R : ℕ} {m m' : ℕ → ℕ}
    (keep : KeepsSchedule pub R m m') {i : ℕ} (hi : i ≤ 25) :
    frameField pub m' i = frameField pub m i := keep _ (Or.inl ⟨_,hi,rfl⟩)

/-- A scan with separated destination slots preserves the complete broadcast frame. -/
theorem KeepsSchedule.broadcast {pub : Arg → ℕ} {R : ℕ} {m m' : ℕ → ℕ}
    (keep : KeepsSchedule pub R m m') {f : BroadcastFrame} (h : f.At pub m) : f.At pub m' := by
  simpa only [BroadcastFrame.At, keep.field (by decide : 0 ≤ 25), keep.field (by decide : 1 ≤ 25),
    keep.field (by decide : 2 ≤ 25), keep.field (by decide : 3 ≤ 25),
    keep.field (by decide : 4 ≤ 25), keep.field (by decide : 5 ≤ 25), keep.field le_rfl] using h

/-- All oriented prefix and load words still agree with the same mathematical hop bijections. -/
theorem KeepsSchedule.addressTables {pub : Arg → ℕ} {R : ℕ} {m m' : ℕ → ℕ}
    (keep : KeepsSchedule pub R m m') {hR : 2<R} {width : Fin R → Fin R → ℕ}
    (tab : AddressTables hR width pub m) : AddressTables hR width pub m' := by
  refine ⟨(keep.field (by decide)).trans tab.teams, ?_, ?_⟩
  · intro u v j
    rw [keep.field (by decide : 17 ≤ 25)]
    exact (keep _ (.inr (.inl ⟨u,v,j,rfl⟩))).trans (tab.front u v j)
  · intro u v
    rw [keep.field (by decide : 18 ≤ 25)]
    exact (keep _ (.inr (.inr ⟨u,v,rfl⟩))).trans (tab.total u v)

/-- Every prefix of a valid destination range preserves the routing data if its actual
writable intervals fit in memory and are disjoint from the relevant read words. -/
theorem rangeMemory_keepsSchedule {w R : ℕ} (mode : Role) (pub : Arg → Word w) (s : Bank w)
    (m : Memory w) (bits : ℕ → Bool) (k : ℕ) (hk : k ≤ (s 11).val)
    (fit : ∀ d ∈ mode.destinations, (s d).val+(s 11).val ≤ 2^w)
    (apart : ∀ a, scheduleRead (readings pub) (readings m) R a →
      ∀ d ∈ mode.destinations, a < (s d).val ∨ (s d).val+(s 11).val ≤ a) :
    KeepsSchedule (readings pub) R (readings m) (readings (rangeMemory mode pub s m bits k)) := by
  intro a ha
  exact congrArg Fin.val (rangeMemory_eq_of_outside mode pub s m bits k a
    (fun d hd => by have := fit d hd; omega)
    (fun d hd => by have := apart a ha d hd; omega))

/-- The sender does not write to either destination array. Its memory remains the memory
at the beginning of the range at every offset. -/
theorem rangeMemory_send {w : ℕ} (pub : Arg → Word w) (s : Bank w) (m : Memory w) (bits : ℕ → Bool)
    (k : ℕ) : rangeMemory .sendData pub s m bits k = m := by
  induction k with
  | zero => rfl
  | succ k ih => exact ih

end RoutingISA.Transmission

end BorderVNP
end Computability
end OAI
