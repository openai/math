import OAI.Computability.VPVNP.RAMBitTranscript
import OAI.Computability.VPVNP.RAMValidatorLocality

/-!
# The incident-bit input of a single RAM validator

A site's predicate depends only on its own header and its incident vector of
the width in equation (10.1). Equality of two such vectors gives equality of
the adjacent successor messages and both messages of every incident sorting
exchange. This applies to malformed assignments as well as accepted ones.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM

open RAMLayout RAMSerialization

variable {d e w : ℕ} {C : Type*}

/-- One site's physical bit vector in the contiguous layout of equation (10.1). -/
def incidentBits (bits : RawAssignment d e w) (v : Fin (2 ^ d)) : Fin (width d (2 ^ e) w) → Bool :=
  RAMLayout.incidentBits (sendArraysEquiv d (2 ^ e) w bits) v

@[simp] theorem incidentBits_at (bits : RawAssignment d e w) (v : Fin (2 ^ d)) (p : Slot d (2 ^ e) w) :
    incidentBits bits v (offset d (2 ^ e) w p) =
      (incidentEquiv d (2 ^ e) w (sendArraysEquiv d (2 ^ e) w bits)).val (v, p) := by
  simp [incidentBits]

theorem incidentBits_sort_send (bits : RawAssignment d e w) (v : Fin (2 ^ d)) (l : Layer d)
    (j : Fin (blockBits (2 ^ e) w)) :
    incidentBits bits v (offset d (2 ^ e) w (.inr (l, 0, j))) =
      (sendArraysEquiv d (2 ^ e) w bits).2 l v j := by
  rw [incidentBits_at]
  exact incident_send _ (.inr (l, v, j))

theorem incidentBits_sort_receive (bits : RawAssignment d e w) (v : Fin (2 ^ d)) (l : Layer d)
    (j : Fin (blockBits (2 ^ e) w)) :
    incidentBits bits v (offset d (2 ^ e) w (.inr (l, 1, j))) =
      (sendArraysEquiv d (2 ^ e) w bits).2 l (l.partner v) j := by
  rw [incidentBits_at, incident_receive_sort]

theorem incidentBits_successor_send (bits : RawAssignment d e w) (v : Fin (2 ^ d))
    (hv : v.val + 1 < 2 ^ d) (j : Fin (8 * w)) :
    incidentBits bits v (offset d (2 ^ e) w (.inl (0, j))) =
      (sendArraysEquiv d (2 ^ e) w bits).1 ⟨v.val, by omega⟩ j := by
  rw [incidentBits_at]
  exact incident_send _ (.inl (⟨v.val, by omega⟩, j))

theorem incidentBits_successor_receive (bits : RawAssignment d e w) (v : Fin (2 ^ d))
    (hv : 0 < v.val) (j : Fin (8 * w)) :
    incidentBits bits v (offset d (2 ^ e) w (.inl (1, j))) =
      (sendArraysEquiv d (2 ^ e) w bits).1 ⟨v.val - 1, by have := v.isLt; omega⟩ j := by
  rw [incidentBits_at, incident_receive_successor _ v hv j]

theorem incidentBits_clamped (bits : RawAssignment d e w) (v : Fin (2 ^ d))
    (p : Slot d (2 ^ e) w) (h : peer v p = none) :
    incidentBits bits v (offset d (2 ^ e) w p) = false := by
  rw [incidentBits_at]
  exact incident_clamp _ _ h

/-- Equality of all of the physical sender arrays consulted at a single site. -/
private structure AgreeAt (a b : SendArrays d (2 ^ e) w) (v : Fin (2 ^ d)) : Prop where
  successor : ∀ j : Fin (2 ^ d - 1), j.val = v.val ∨ j.val + 1 = v.val → a.1 j = b.1 j
  sorting : ∀ l, a.2 l v = b.2 l v ∧ a.2 l (l.partner v) = b.2 l (l.partner v)

private theorem agree_of_incident {a b : RawAssignment d e w} {v : Fin (2 ^ d)}
    (h : incidentBits a v = incidentBits b v) :
    AgreeAt (sendArraysEquiv d (2 ^ e) w a) (sendArraysEquiv d (2 ^ e) w b) v := by
  constructor
  · intro j hj
    funext i
    obtain he | he := hj
    · have hs : v.val + 1 < 2 ^ d := by have := j.isLt; omega
      have heq := congrFun h (offset d (2 ^ e) w (.inl (0, i)))
      simpa only [incidentBits_successor_send _ v hs, ← he] using heq
    · have hv : 0 < v.val := by omega
      have heq := congrFun h (offset d (2 ^ e) w (.inl (1, i)))
      have hij : v.val - 1 = j.val := by omega
      simpa only [incidentBits_successor_receive _ v hv, hij] using heq
  · intro l
    constructor
    · funext i
      simpa only [incidentBits_sort_send] using congrFun h (offset d (2 ^ e) w (.inr (l, 0, i)))
    · funext i
      simpa only [incidentBits_sort_receive] using congrFun h (offset d (2 ^ e) w (.inr (l, 1, i)))

private theorem AgreeAt.parsed {a b : SendArrays d (2 ^ e) w} {v : Fin (2 ^ d)} (hab : AgreeAt a b v)
    (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) :
    (unpackMessages (parseMessages hw hc a)).AgreeAt (unpackMessages (parseMessages hw hc b)) v := by
  constructor
  · intro j hj
    simp [unpackMessages, parseMessages, hab.successor j hj]
  · intro l
    simp [unpackMessages, parseMessages, (hab.sorting l).1, (hab.sorting l).2]

private theorem AgreeAt.formats {a b : SendArrays d (2 ^ e) w} {v : Fin (2 ^ d)} (hab : AgreeAt a b v)
    (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w) :
    (OutgoingOK hw hc a v ↔ OutgoingOK hw hc b v) ∧ (IncomingOK hw hc a v ↔ IncomingOK hw hc b v) := by
  constructor
  · unfold OutgoingOK
    apply and_congr
    · split
      · simp [messageBits, parseMessages, hab.successor ⟨v.val, by omega⟩ (.inl rfl)]
      · rfl
    · apply forall_congr'
      intro l
      simp [messageBits, parseMessages, (hab.sorting l).1]
  · unfold IncomingOK
    apply and_congr
    · split
      · have he : v.val - 1 + 1 = v.val := by omega
        simp [messageBits, parseMessages, hab.successor ⟨v.val - 1, by have := v.isLt; omega⟩ (.inr he)]
      · rfl
    · apply forall_congr'
      intro l
      simp [messageBits, parseMessages, (hab.sorting l).2]

/-- A site's validator is a function of its own header and incident bit vector.
Both the canonicality test and the call/sort checks satisfy this locality. -/
theorem bitValidator_congr (P : Program w C) (fuel : ℕ) (initial : Word w)
    {header header' : ℕ → Word w} (hw : 2 ≤ w) (hc : 2 ^ d * 2 ^ e < 2 ^ w)
    {a b : RawAssignment d e w} {v : Fin (2 ^ d)} (hh : header v = header' v)
    (hi : incidentBits a v = incidentBits b v) (rs : List (Report w)) :
    BitValidator P fuel initial header hw hc a v rs ↔ BitValidator P fuel initial header' hw hc b v rs := by
  have ha := agree_of_incident hi
  have hf := ha.formats hw hc
  exact and_congr (and_congr hf.1 hf.2) (validator_congr _ _ _ hh (ha.parsed hw hc) rs)

end BurstRAM

end VPVNP
end Computability
end OAI
