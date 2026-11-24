import OAI.Computability.VPVNP.PairShrinkRoleChildTyped
import OAI.Computability.VPVNP.PrimedInputRAMHeaders

/-!
# Reading the two independent arguments of a refresh node

The parent packet is read at its absolute DFS arena address. The unique old
half is parsed from the remaining choice tape in outgoing-then-incoming slot
order. Both operations use the state network's actual variable slot widths.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.RefreshHalfDecoder

open BurstRAM Compression LocalHistory NodeArguments NodeArguments.ChildScan DFS
open scoped Fin.CommRing

variable {w a g endAddr : ℕ} (X : State a g) (u : X.network.Site)

/-- Decode a half-wire assignment in outgoing slot order followed by incoming slot order, using
the state's payload widths. -/
noncomputable def reader := LocalHistory.half X.network u (outgoingOrder X u) (incomingOrder X u) (statePayload X)
/-- Total number of bits in the site's outgoing and incoming half-wire fields. -/
noncomputable def width := ∑ dir : Bool, ∑ j, X.halfWidth u dir j

theorem read_iff (bs : List Bool) (x : X.network.Half u) (tail : List Bool) :
    (reader X u).read bs = some (x,tail) ↔ bs = packed X u x ++ tail := by
  rw [packed_eq_encode]
  exact (reader X u).read_iff bs x tail

theorem none_iff (bs : List Bool) :
    (reader X u).read bs = none ↔ bs.length < width X u := by
  constructor
  · intro h
    by_contra! room
    let bits : X.network.Half u := (fun _ _ _ => false,fun _ _ _ => false)
    have eqn : ChildSlots.length X u (ChildSlots.slots (2^a)) = width X u := by
      exact (Child.payload_length X (Child.ofHalf X u bits)).symm.trans
        ((congrArg List.length (Child.payload_ofHalf X u bits)).trans (packed_length X u bits))
    obtain ⟨q,atSite,split⟩ := choose_payload X u bs (eqn ▸ room)
    rcases q with ⟨v,data⟩
    change v = u at atSite
    subst v
    let q : Child X := ⟨u,data⟩
    have eq := (read_iff X u bs (q.half X) (bs.drop (q.payload X).length)).mpr
      ((q.payload_eq_packed X) ▸ split.symm)
    rw [h] at eq; contradiction
  · intro short
    cases h : (reader X u).read bs with
    | none => rfl
    | some pair =>
      obtain ⟨x,tail⟩ := pair
      have len := congrArg List.length ((read_iff X u bs x tail).mp h)
      rw [List.length_append,packed_length] at len
      change bs.length < ∑ dir : Bool, ∑ j, X.halfWidth u dir j at short
      omega

variable (A : Arena) (node : ℕ) (s : Scratch w endAddr)

/-- Read the parent's packed argument from private scratch as bits, interpreting a stored word
equal to one as true. -/
noncomputable def packetBits : List Bool := List.ofFn fun i : Fin (width X u) =>
  decide (rawScratch s ((A.base node+i.val : ℕ) : Word w) = 1)

/-- Read the parent packet from its DFS arena and decode its local half-wire assignment. The
packet supplies exactly the required number of bits. -/
noncomputable def parent : Option (X.network.Half u) :=
  ((reader X u).read (packetBits X u A node s)).map Prod.fst

theorem packetBits_eq (x : X.network.Half u) (stored : (Packet.mk node (packed X u x)).Stored A s)
    (hw : 0 < w) : packetBits X u A node s = packed X u x := by
  apply List.ext_getElem
  · simp [packetBits,width,packed_length]
  · intro j hj hi
    have field := stored ⟨j,hi⟩
    simp only [packetBits,List.getElem_ofFn]
    rw [field]
    change decide (PrimedInputRAM.encodeBit w (packed X u x)[j] = 1) = _
    simp [PrimedInputRAM.encodeBit_eq_one hw]

theorem parent_eq (x : X.network.Half u) (stored : (Packet.mk node (packed X u x)).Stored A s)
    (hw : 0 < w) : parent X u A node s = some x := by
  unfold parent
  rw [packetBits_eq X u A node s x stored hw,
    (read_iff X u _ x []).mpr (List.append_nil _).symm]
  rfl

end PairSimulation.RefreshHalfDecoder

end VPVNP
end Computability
end OAI
