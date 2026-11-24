import OAI.Computability.VPVNP.RAMProcessorCallInvariant
import OAI.Computability.VPVNP.RAMProcessorPrelude
import OAI.Computability.VPVNP.RAMTapeSuccessorCuts
import OAI.Computability.VPVNP.RAMTapeSiteRecordWords
import OAI.Computability.VPVNP.RAMTapeSuccessorParameters

/-!
# Full-word inputs to the auxiliary site verifier

Section 12 places the auxiliary verifier at a cursor-zero vertex. Its header
may contain a full histogram word. Its site-address width, machine-word
width and private clock are independent public parameters of the virtual
network.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.VirtualSite

open BurstRAM PrivateRAM RAMLayout SiteProcessor

/-- Full-word virtual site input, including its independent clock and incident sends. -/
structure Input (d e w : ℕ) where
  /-- Private instruction limit for each call of the auxiliary RAM. -/
  fuel : ℕ
  /-- Address of the virtual site. -/
  v : Word d
  /-- Initial persistent state of the auxiliary machine. -/
  initialWord : Word w
  /-- Auxiliary memory word initially stored at this address. -/
  headerWord : Word w
  /-- All shared successor and sorting messages on the virtual RAM network. -/
  sends : SendArrays d (2^e) w
  hw : 2 ≤ w
  hc : 2^d*2^e < 2^w

variable {d e w p r k : ℕ} (x : Input d e w)

include x in
theorem Input.hcap : d+e < w := by
  have h := x.hc
  rw [← pow_add] at h
  exact (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp h

/-- Reconstructed incoming and outgoing cuts for the virtual site. -/
def Input.summary : SiteSuccessors w :=
  (scanSuccessors x.hw x.hc x.initialWord x.v (sortIncident x.sends x.v)).1

/-- Validity of the site's transmitted and received successor messages. -/
def Input.valid : Prop := SuccessorSendOK x.hw x.hc x.sends x.v ∧ SuccessorReceiveOK x.hw x.hc x.sends x.v

/-- Word encoding the cumulative cost of the chosen boundary cut. -/
def Input.sideWord (side : Successors.Side) : Word w := Fin.ofNat (2^w) (Successors.sideCut x.summary side).cost

/-- Zero-extended virtual site address in the auxiliary word format. -/
def Input.addrWord : Word w := SiteRecordWords.addressWord ((Nat.le_add_right d e).trans x.hcap.le) x.v

/-- Full interpreter snapshot before it emits the initialization record. -/
def Input.bare (T : Template p r k) (pub : Fin k → Word w) (bits : List Bool) :
    Snapshot w p r k where
  pub := pub
  cfg := ⟨T.entry, x.summary.input.state.getD 0, fun _ => 0, []⟩
  publicH := 2^e
  publicFuel := x.fuel
  fuel := 0
  callLeft := 0
  siteLeft := 2*2^e-1
  cap := SuccessorParameters.capWord d e w x.hcap
  globalLeft := 0
  cost := x.sideWord .receive
  savedStart := []
  ordinal := []
  lower := SiteEndpoints.startWord e w x.v x.hcap
  boundary := SiteEndpoints.endWord e w x.v x.hcap
  targetCost := x.sideWord .send
  targetState := (Successors.sideCut x.summary .send).state.getD 0
  running := x.summary.input.state.isSome
  hasTarget := x.summary.output.isSome
  targetRunning := (Successors.sideCut x.summary .send).state.isSome
  choices := bits
  tag := []
  address := BurstRAM.wordBits x.addrWord
  value := BurstRAM.wordBits x.headerWord
  remaining := List.replicate (4*2^e) true
  reverseBuffer := []
  output := []

theorem Input.sideWord_val (side : Successors.Side) : (x.sideWord side).val = (Successors.sideCut x.summary side).cost := by
  have hs := scanSuccessors_spec x.hw x.hc x.initialWord x.v (sortIncident x.sends x.v) x.sends (sortIncident_offset x.sends x.v)
  have hb : (Successors.sideCut x.summary side).cost ≤ 2^d*2^e := by
    cases side with
    | receive =>
      change (scanSuccessors x.hw x.hc x.initialWord x.v (sortIncident x.sends x.v)).1.input.cost ≤ _
      rw [hs.input_eq]
      unfold inputCut
      split <;> first | exact Nat.zero_le _ | exact Nat.le_of_lt_succ (Fin.isLt _)
    | send =>
      change ((scanSuccessors x.hw x.hc x.initialWord x.v (sortIncident x.sends x.v)).1.output.getD ⟨0,none⟩).cost ≤ _
      rw [hs.output_eq]
      unfold outputCut
      split <;> first | exact Nat.zero_le _ | exact Nat.le_of_lt_succ (Fin.isLt _)
  exact Nat.mod_eq_of_lt (hb.trans_lt x.hc)

theorem Input.bare_cut (T : Template p r k) (pub : Fin k → Word w) (bits : List Bool) :
    (x.bare T pub bits).tests.cut = x.summary.input := by
  apply Cut.ext
  · exact x.sideWord_val .receive
  · change (if x.summary.input.state.isSome then some (x.summary.input.state.getD 0) else none) = _
    cases x.summary.input.state <;> rfl

theorem Input.bare_target (T : Template p r k) (pub : Fin k → Word w) (bits : List Bool) :
    (x.bare T pub bits).tests.target = x.summary.output := by
  have hc := x.sideWord_val .send
  change (x.sideWord .send).val = (x.summary.output.getD ⟨0,none⟩).cost at hc
  change (if x.summary.output.isSome then some ⟨(x.sideWord .send).val,
    if (x.summary.output.getD ⟨0,none⟩).state.isSome then some ((x.summary.output.getD ⟨0,none⟩).state.getD 0)
    else none⟩ else none) = x.summary.output
  rw [hc]
  cases x.summary.output with
  | none => rfl
  | some c => obtain ⟨c,status⟩ := c; cases status <;> rfl

end RAMTape.VirtualSite

end VPVNP
end Computability
end OAI
