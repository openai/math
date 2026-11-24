import OAI.Computability.VPVNP.RAMTapeSuccessorEdgeValues
import OAI.Computability.VPVNP.RAMTapeSuccessorGuard

/-!
# Typed values of the two physical successor checks

An interior field carries a canonical typed message. A missing field carries
the zero clamp. Once both fields pass, the physical cost, state and record
stacks give the cuts and last records used by the call loop and boundary pass.
The first processor starts from the public initial word at cost zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Successors

open BurstRAM RAMSerialization

variable {w cap : ℕ}

/-- Match a physical field to a typed edge, with a zero clamp for a missing edge. -/
def EdgeExpectation (hw : 2 ≤ w) (hc : cap < 2^w) (bits : Fin (8*w) → Bool) :
    Option (RAMSerialization.Successor w cap) → Prop
  | some msg => (successorFormat hw hc).decode bits = some msg
  | none => bits = fun _ => false

/-- Select the optional outgoing or incoming typed successor message for the requested side. -/
def atSide (sent received : Option (RAMSerialization.Successor w cap)) :
    Side → Option (RAMSerialization.Successor w cap)
  | .send => sent
  | .receive => received

/-- The endpoint cost fits in one physical word even when it equals the cap. -/
def costWord (hc : cap < 2^w) : Option (RAMSerialization.Successor w cap) → Word w
  | some x => ⟨x.cost.val, (Nat.le_of_lt_succ x.cost.isLt).trans_lt hc⟩
  | none => 0

/-- A missing incoming edge installs the initial word. A missing outgoing
edge has no running target. A present edge takes its state from the message. -/
def savedState (initial : Word w) (side : Side) :
    Option (RAMSerialization.Successor w cap) → Option (Word w)
  | some x => x.state
  | none => match side with
    | .send => none
    | .receive => some initial

/-- The stacks consumed by the call and sorting passes, stated relative to
their caller so a saved flag or record may have a nonempty stack tail. -/
structure Outputs (base out : Stacks Port) (hw : 2 ≤ w) (hc : cap < 2^w) (initial : Word w)
    (sent received : Option (RAMSerialization.Successor w cap)) (suffix : List Bool) : Prop where
  outPresent : out .outPresent = sent.isSome :: base .outPresent
  incident : out .incident = suffix
  running : ∀ side, out (.running side) =
    (savedState initial side (atSide sent received side)).isSome :: base (.running side)
  cost : ∀ side, out (.word side 1) = BurstRAM.wordBits (costWord hc (atSide sent received side))
  state : ∀ side, out (.word side 2) =
    BurstRAM.wordBits ((savedState initial side (atSide sent received side)).getD 0)
  record : ∀ side, out (.record side) =
    List.ofFn ((recordFormat hw).encode ((atSide sent received side).bind (·.lastRecord))) ++
      base (.record side)

private theorem edge_values (hw : 2 ≤ w) (hc : cap < 2^w) (base : Stacks SuccessorEdge.Port)
    (bits : Fin (8*w) → Bool) (msg : Option (RAMSerialization.Successor w cap)) (tail : List Bool)
    (hm : EdgeExpectation hw hc bits msg) :
    let out := SuccessorEdge.edgeResult base msg.isSome bits ⟨cap, hc⟩ tail
    out .verdict = true :: base .verdict ∧
      out .running = (msg.bind (·.state)).isSome :: base .running ∧
      out (.word 1) = BurstRAM.wordBits (costWord hc msg) ∧
      out (.word 2) = BurstRAM.wordBits ((msg.bind (·.state)).getD 0) ∧
      out .record = List.ofFn ((recordFormat hw).encode (msg.bind (·.lastRecord))) ++ base .record := by
  cases msg with
  | some x => exact SuccessorEdge.present_values hw hc base bits tail x hm
  | none =>
    subst bits
    obtain ⟨hv, hr, hs, hp⟩ := SuccessorEdge.clamped_values base (⟨cap, hc⟩ : Word w) tail
    refine ⟨hv, hr, hs 1, hs 2, ?_⟩
    simpa only [Option.isSome_none, Option.bind_none, recordFormat_empty, List.ofFn_const] using hp

private theorem finish_spec (hw : 2 ≤ w) (hc : cap < 2^w) (s : Stacks Port) (initial : Word w)
    (sent received : Fin (8*w) → Bool) (sendMsg recvMsg : Option (RAMSerialization.Successor w cap))
    (suffix : List Bool) (hi : s .initial = BurstRAM.wordBits initial)
    (hs : EdgeExpectation hw hc sent sendMsg) (hr : EdgeExpectation hw hc received recvMsg) :
    let out := finish s sendMsg.isSome recvMsg.isSome sent received ⟨cap, hc⟩ suffix
    Outputs s out hw hc initial sendMsg recvMsg suffix ∧
      ∀ side, out (.verdict side) = true :: s (.verdict side) := by
  let a := afterEdge s .send sendMsg.isSome sent ⟨cap, hc⟩ (List.ofFn received ++ suffix)
  obtain ⟨sv, sr, sc, ss, sp⟩ := edge_values hw hc (s ∘ edgePorts .send) sent sendMsg
    (List.ofFn received ++ suffix) hs
  obtain ⟨rv, rr, rc, rs, rp⟩ := edge_values hw hc (a ∘ edgePorts .receive) received recvMsg suffix hr
  constructor
  · constructor
    · cases recvMsg <;> rfl
    · cases recvMsg <;> rfl
    · intro side
      cases side with
      | send => cases sendMsg <;> cases recvMsg <;> exact sr
      | receive => cases recvMsg with
        | none => rfl
        | some x => exact rr
    · intro side
      cases side with
      | send => cases recvMsg <;> exact sc
      | receive => cases recvMsg <;> exact rc
    · intro side
      cases side with
      | send => cases sendMsg <;> cases recvMsg <;> exact ss
      | receive => cases recvMsg with
        | none => exact hi
        | some x => exact rs
    · intro side
      cases side with
      | send => cases recvMsg <;> exact sp
      | receive => cases recvMsg <;> exact rp
  · intro side
    cases side with
    | send => cases recvMsg <;> exact sv
    | receive => cases recvMsg <;> exact rv

/-- All physical output values after both decoded fields, including the
initial cut and the missing target at the ends of the chain. -/
theorem finish_values (hw : 2 ≤ w) (hc : cap < 2^w) (s : Stacks Port) (initial : Word w)
    (sent received : Fin (8*w) → Bool) (sendMsg recvMsg : Option (RAMSerialization.Successor w cap))
    (suffix : List Bool) (hi : s .initial = BurstRAM.wordBits initial)
    (hs : EdgeExpectation hw hc sent sendMsg) (hr : EdgeExpectation hw hc received recvMsg) :
    Outputs s (finish s sendMsg.isSome recvMsg.isSome sent received ⟨cap, hc⟩ suffix)
      hw hc initial sendMsg recvMsg suffix :=
  (finish_spec hw hc s initial sent received sendMsg recvMsg suffix hi hs hr).1

/-- Both physical verdict bits are set when the fields match their typed edges. -/
theorem finish_verdicts (hw : 2 ≤ w) (hc : cap < 2^w) (s : Stacks Port) (initial : Word w)
    (sent received : Fin (8*w) → Bool) (sendMsg recvMsg : Option (RAMSerialization.Successor w cap))
    (suffix : List Bool) (hi : s .initial = BurstRAM.wordBits initial)
    (hs : EdgeExpectation hw hc sent sendMsg) (hr : EdgeExpectation hw hc received recvMsg) :
    ∀ side, finish s sendMsg.isSome recvMsg.isSome sent received ⟨cap, hc⟩ suffix (.verdict side) =
      true :: s (.verdict side) :=
  (finish_spec hw hc s initial sent received sendMsg recvMsg suffix hi hs hr).2

/-- The guard consumes the verdicts, preserving every register needed by the
processor's continuation. -/
theorem guardResult_values {s out : Stacks Port} {hw : 2 ≤ w} {hc : cap < 2^w} {initial : Word w}
    {sent received : Option (RAMSerialization.Successor w cap)} {suffix : List Bool}
    (h : Outputs s out hw hc initial sent received suffix) :
    Outputs s (guardResult out) hw hc initial sent received suffix :=
  ⟨h.outPresent, h.incident, h.running, h.cost, h.state, h.record⟩

end RAMTape.Successors

end VPVNP
end Computability
end OAI
