import OAI.Computability.VPVNP.RAMTapeSiteCutBank
import OAI.Computability.VPVNP.RAMTapeVirtualSite

/-!
# The site controller snapshot furnished by the physical parser

The incoming and outgoing cost words are read from the two successor fields.
Missing fields take their canonical endpoint values, and halted cuts carry a
zero state word. The other public words come from the computed site address,
bucket size, public call clock and packed header.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteCutBank

open BurstRAM PrivateRAM ProcessorInput SiteProcessor RAMLayout

variable {d e w p r k : ℕ} (x : Input d e w)

/-- Successor cuts reconstructed from the incident sort messages. -/
def Input.summary : SiteSuccessors w :=
  (scanSuccessors x.word_ge_two x.cap_lt x.initialWord x.v (sortIncident x.sends x.v)).1

/-- The cumulative cost word on the selected side of this site. -/
def Input.sideWord (side : Successors.Side) : Word w :=
  Fin.ofNat (2^w) (Successors.sideCut x.summary side).cost

theorem Input.sideWord_val (h : x.valid) (side : Successors.Side) :
    (x.sideWord side).val = (Successors.sideCut x.summary side).cost := by
  obtain ⟨z, _, hz⟩ := (guarded_registers x h).cost side
  exact Nat.mod_eq_of_lt (hz ▸ z.isLt)

theorem Input.guarded_cost (h : x.valid) (side : Successors.Side) :
    x.guarded (ports (.word side 1)) = BurstRAM.wordBits (x.sideWord side) := by
  obtain ⟨z, hz, he⟩ := (guarded_registers x h).cost side
  exact hz.trans (congrArg BurstRAM.wordBits (Fin.ext (he.trans (x.sideWord_val h side).symm)))

/-- The live site address in the RAM's full word format. -/
def Input.addrWord : Word w := SiteRecordWords.addressWord ((Nat.le_add_right d e).trans x.hcap.le) x.v

/-- The four physical header bits packed into one RAM word. -/
def Input.headerWord : Word w := ProcessorInput.headerWord x.hw x.hdr

/-- A four-bit live header supplies the same verifier as the auxiliary full-word
header once it has been packed in its prescribed RAM word. -/
def Input.asWordSite : VirtualSite.Input d e w where
  fuel := x.n^x.u
  v := x.v
  initialWord := x.initialWord
  headerWord := x.headerWord
  sends := x.sends
  hw := x.word_ge_two
  hc := x.cap_lt

/-- Initial interpreter snapshot for the selected program, operands and private choices. -/
def Input.bare (T : Template p r k) (pub : Fin k → Word w) (bits : List Bool) : Snapshot w p r k :=
  x.asWordSite.bare T pub bits

theorem Input.bare_cut (T : Template p r k) (pub : Fin k → Word w) (bits : List Bool) (h : x.valid) :
    (x.bare T pub bits).tests.cut = x.summary.input := by
  apply Cut.ext
  · exact x.sideWord_val h .receive
  · change (if x.summary.input.state.isSome then some (x.summary.input.state.getD 0) else none) = _
    cases x.summary.input.state <;> rfl

theorem Input.bare_target (T : Template p r k) (pub : Fin k → Word w) (bits : List Bool) (h : x.valid) :
    (x.bare T pub bits).tests.target = x.summary.output := by
  have hc := x.sideWord_val h .send
  change (x.sideWord .send).val = (x.summary.output.getD ⟨0,none⟩).cost at hc
  change (if x.summary.output.isSome then some ⟨(x.sideWord .send).val,
    if (x.summary.output.getD ⟨0,none⟩).state.isSome then some ((x.summary.output.getD ⟨0,none⟩).state.getD 0)
    else none⟩ else none) = x.summary.output
  rw [hc]
  cases x.summary.output with
  | none => rfl
  | some c => obtain ⟨c,status⟩ := c; cases status <;> rfl

theorem Input.bare_buffer (T : Template p r k) (pub : Fin k → Word w) (bits : List Bool) :
    RecordBuffer.Holds x.word_ge_two (2^e) [] (x.bare T pub bits).records :=
  ⟨Nat.zero_le _, rfl, rfl, rfl, rfl, rfl⟩

end RAMTape.SiteCutBank

end VPVNP
end Computability
end OAI
