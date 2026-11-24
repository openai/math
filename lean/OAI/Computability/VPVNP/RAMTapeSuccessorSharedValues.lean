import OAI.Computability.VPVNP.RAMTapeSuccessorValues
import OAI.Computability.VPVNP.RAMValidatorSuccessor

/-!
# Successor registers on the shared bits of a RAM transcript

Each interior edge has one send array. The receiving site reads those same
bits at its incoming port. The two endpoints instead read an all-zero field.
Under the local canonicality checks, the physical registers therefore hold
the typed messages parsed from the adjacent send arrays.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Successors

open BurstRAM RAMSerialization RAMLayout

variable {d e w : ℕ}

/-- Read the outgoing or incoming successor field at a site's incident offset from the shared
send arrays. -/
def sharedField (a : SendArrays d (2^e) w) (v : Fin (2^d)) (dir : Fin 2) : Fin (8*w) → Bool :=
  fun j ↦ RAMLayout.incidentBits a v (offset d (2^e) w (.inl (dir, j)))

/-- Return the parsed outgoing message on an interior send edge, or no message at the last
site. -/
def sentMessage (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : SendArrays d (2^e) w)
    (v : Fin (2^d)) : Option (RAMSerialization.Successor w (2^d * 2^e)) :=
  if h : v.val + 1 < 2^d then some ((parseMessages hw hc a).1 ⟨v.val, by omega⟩) else none

/-- Return the preceding site's parsed send message on an interior receive edge, or no message
at the first site. -/
def receivedMessage (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : SendArrays d (2^e) w)
    (v : Fin (2^d)) : Option (RAMSerialization.Successor w (2^d * 2^e)) :=
  if h : 0 < v.val then some ((parseMessages hw hc a).1 ⟨v.val-1, by have := v.isLt; omega⟩) else none

@[simp] theorem sentMessage_isSome (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (a : SendArrays d (2^e) w) (v : Fin (2^d)) :
    (sentMessage hw hc a v).isSome = decide (v.val+1 < 2^d) := by
  by_cases h : v.val+1 < 2^d <;> simp [sentMessage, h]

@[simp] theorem receivedMessage_isSome (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (a : SendArrays d (2^e) w) (v : Fin (2^d)) :
    (receivedMessage hw hc a v).isSome = decide (0 < v.val) := by
  by_cases h : 0 < v.val <;> simp [receivedMessage, h]

theorem sentMessage_expectation (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (a : SendArrays d (2^e) w) (v : Fin (2^d)) (hs : SuccessorSendOK hw hc a v) :
    EdgeExpectation hw hc (sharedField a v 0) (sentMessage hw hc a v) := by
  by_cases h : v.val+1 < 2^d
  · let edge : Fin (2^d-1) := ⟨v.val, by omega⟩
    have he : a.1 edge = (successorFormat hw hc).encode ((parseMessages hw hc a).1 edge) := by
      simpa only [SuccessorSendOK, h, ↓reduceDIte, messageBits] using hs
    rw [sentMessage, dite_eq_left h]
    apply (successor_decode_iff hw hc _ _).mpr
    funext j
    exact ((incidentBits_offset ..).trans (incident_send a (.inl (edge, j)))).trans (congrFun he j)
  · rw [sentMessage, dite_eq_right h]
    funext j
    exact (incidentBits_offset ..).trans (incident_clamp a _
      (peer_send_end v (by have := v.isLt; omega) j))

theorem receivedMessage_expectation (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w)
    (a : SendArrays d (2^e) w) (v : Fin (2^d)) (hr : SuccessorReceiveOK hw hc a v) :
    EdgeExpectation hw hc (sharedField a v 1) (receivedMessage hw hc a v) := by
  by_cases h : 0 < v.val
  · let edge : Fin (2^d-1) := ⟨v.val-1, by have := v.isLt; omega⟩
    have he : a.1 edge = (successorFormat hw hc).encode ((parseMessages hw hc a).1 edge) := by
      simpa only [SuccessorReceiveOK, h, ↓reduceDIte, messageBits] using hr
    rw [receivedMessage, dite_eq_left h]
    apply (successor_decode_iff hw hc _ _).mpr
    funext j
    exact ((incidentBits_offset ..).trans (incident_receive_successor a v h j)).trans (congrFun he j)
  · rw [receivedMessage, dite_eq_right h]
    funext j
    exact (incidentBits_offset ..).trans (incident_clamp a _ (peer_receive_start v (by omega) j))

/-- The physical reader's final stacks on the full incident vector. Its
remaining input starts at the first sorting field. -/
def sharedFinish (hc : 2^d * 2^e < 2^w) (a : SendArrays d (2^e) w) (v : Fin (2^d))
    (s : Stacks Port) : Stacks Port :=
  finish s (decide (v.val+1 < 2^d)) (decide (0 < v.val)) (sharedField a v 0) (sharedField a v 1)
    ⟨2^d * 2^e, hc⟩ ((List.ofFn (RAMLayout.incidentBits a v)).drop (16*w))

theorem finish_shared_values (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : SendArrays d (2^e) w)
    (v : Fin (2^d)) (s : Stacks Port) (initial : Word w) (hi : s .initial = BurstRAM.wordBits initial)
    (hs : SuccessorSendOK hw hc a v) (hr : SuccessorReceiveOK hw hc a v) :
    Outputs s (sharedFinish hc a v s) hw hc initial (sentMessage hw hc a v) (receivedMessage hw hc a v)
      ((List.ofFn (RAMLayout.incidentBits a v)).drop (16*w)) := by
  simpa only [sharedFinish, sentMessage_isSome, receivedMessage_isSome] using
    finish_values hw hc s initial _ _ _ _ _ hi (sentMessage_expectation hw hc a v hs)
      (receivedMessage_expectation hw hc a v hr)

theorem guard_shared_values (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : SendArrays d (2^e) w)
    (v : Fin (2^d)) (s : Stacks Port) (initial : Word w) (hi : s .initial = BurstRAM.wordBits initial)
    (hs : SuccessorSendOK hw hc a v) (hr : SuccessorReceiveOK hw hc a v) :
    Outputs s (guardResult (sharedFinish hc a v s)) hw hc initial
      (sentMessage hw hc a v) (receivedMessage hw hc a v) ((List.ofFn (RAMLayout.incidentBits a v)).drop (16*w)) :=
  guardResult_values (finish_shared_values hw hc a v s initial hi hs hr)

end RAMTape.Successors

end VPVNP
end Computability
end OAI
