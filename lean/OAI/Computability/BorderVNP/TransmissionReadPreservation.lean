import OAI.Computability.BorderVNP.TransmissionScan
import OAI.Computability.BorderVNP.TransmissionPinsInput

/-! # Read-only memory across a physical transmission range

Only an endpoint locally selected for writing needs an address-fit or disjointness
bound. A sending team performs no writes, even to its nominal destination addresses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Transmission

open VPVNP.BurstRAM

variable {w : ℕ}

/-- Registers whose destination intervals a team actually writes in the selected role. -/
def Role.destinations : Role → List Reg
  | .sharedHere => [13,14]
  | .receiveA => [13]
  | .dataHere | .receiveB => [14]
  | .sendData => []

private theorem dest_ne_cursor {mode : Role} {d : Reg} (h : d ∈ mode.destinations) : d ≠ 16 := by
  intro he
  subst d
  cases mode <;> revert h <;> decide

/-- A single transmission update preserves every word outside its actual physical writes. -/
theorem Role.output_eq_of_outside (mode : Role) (pub : Arg → Word w) (s : Bank w)
    (m : Memory w) (b : Bool) (a : ℕ)
    (outside : ∀ d ∈ mode.destinations, a ≠ (s d + s 16).val) :
    mode.output pub s m b a = m a := by
  cases mode with
  | sharedHere =>
    rw [Role.output,write,Function.update_of_ne (outside 14 (by decide)),
      write,Function.update_of_ne (outside 13 (by decide))]
  | dataHere | receiveB =>
    exact Function.update_of_ne (outside 14 (by decide)) ..
  | receiveA =>
    exact Function.update_of_ne (outside 13 (by decide)) ..
  | sendData => rfl

/-- A prefix of an addressed range leaves every word outside the selected destination
intervals unchanged. The endpoint sums may equal the word capacity at the exclusive end. -/
theorem rangeMemory_eq_of_outside (mode : Role) (pub : Arg → Word w) (s : Bank w)
    (m : Memory w) (bits : ℕ → Bool) (k a : ℕ)
    (fit : ∀ d ∈ mode.destinations, (s d).val+k ≤ 2^w)
    (outside : ∀ d ∈ mode.destinations, a < (s d).val ∨ (s d).val+k ≤ a) :
    rangeMemory mode pub s m bits k a = m a := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [rangeMemory,Role.output_eq_of_outside]
    · exact ih (fun d hd ↦ by have := fit d hd; omega)
        (fun d hd ↦ by have := outside d hd; omega)
    · intro d hd
      have hb := fit d hd
      have hk : k < 2^w := by omega
      have hs : (s d).val+k < 2^w := by omega
      rw [Function.update_of_ne (dest_ne_cursor hd),Function.update_self,
        Fin.val_add,Fin.val_ofNat,Nat.mod_eq_of_lt hk,Nat.mod_eq_of_lt hs]
      have := outside d hd
      omega

/-- A protected consecutive array is unchanged after the range. This applies equally
to frame words, prefix tables, offset tables, source literals, and the two pin arrays. -/
theorem rangeMemory_segment (mode : Role) (pub : Arg → Word w) (s : Bank w)
    (m : Memory w) (bits : ℕ → Bool) (k base len : ℕ)
    (fit : ∀ d ∈ mode.destinations, (s d).val+k ≤ 2^w)
    (disjoint : ∀ d ∈ mode.destinations, base+len ≤ (s d).val ∨ (s d).val+k ≤ base) :
    ∀ i < len, rangeMemory mode pub s m bits k (base+i) = m (base+i) := by
  intro i hi
  apply rangeMemory_eq_of_outside _ _ _ _ _ _ _ fit
  intro d hd
  have := disjoint d hd
  omega

end RoutingISA.Transmission

namespace RoutingISA.Pins

open VPVNP.BurstRAM Transmission

variable {w : ℕ} {L : Layout}

/-- All original processor literal, exterior, and pin words survive every partial range
whose local destination intervals lie above the actual initialized header. -/
theorem ProcessorFields.ContainsInput.rangeMemory {r : ProcessorFields L} {m : Memory w}
    (h : r.ContainsInput m) (mode : Role) (pub : Arg → Word w) (s : Bank w) (bits : ℕ → Bool)
    (k : ℕ) (fit : ∀ d ∈ mode.destinations, (s d).val+k ≤ 2^w)
    (above : ∀ d ∈ mode.destinations, r.header.length ≤ (s d).val) :
    r.ContainsInput (Transmission.rangeMemory mode pub s m bits k) := by
  intro a ha
  rw [rangeMemory_eq_of_outside mode pub s m bits k a fit
    (fun d hd ↦ Or.inl (ha.trans_le (above d hd)))]
  exact h a ha

/-- Protecting the 25 consecutive public descriptor words preserves the pin layout read
from the real memory, for every prefix of the selected transmission interval. -/
theorem Frame.rangeMemory {pub : Arg → Word w} {m : Memory w} (h : Frame L (readings pub) (readings m))
    (mode : Role) (s : Bank w) (bits : ℕ → Bool) (k : ℕ)
    (fit : ∀ d ∈ mode.destinations, (s d).val+k ≤ 2^w)
    (disjoint : ∀ d ∈ mode.destinations,
      (pub 0).val+25 ≤ (s d).val ∨ (s d).val+k ≤ (pub 0).val) :
    Frame L (readings pub) (readings (Transmission.rangeMemory mode pub s m bits k)) := by
  have fields (i : ℕ) (hi : i < 25) :
      frameField (readings pub) (readings (Transmission.rangeMemory mode pub s m bits k)) i =
        frameField (readings pub) (readings m) i :=
    congrArg Fin.val (rangeMemory_segment mode pub s m bits k (pub 0).val 25 fit disjoint i hi)
  exact ⟨(fields 0 (by decide)).trans h.team, (fields 1 (by decide)).trans h.teams,
    (fields 2 (by decide)).trans h.processors, (fields 3 (by decide)).trans h.literal,
    (fields 4 (by decide)).trans h.link, (fields 21 (by decide)).trans h.ibase,
    (fields 22 (by decide)).trans h.hbase, (fields 23 (by decide)).trans h.width,
    (fields 24 (by decide)).trans h.starbase⟩

end RoutingISA.Pins

end BorderVNP
end Computability
end OAI
