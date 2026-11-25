import OAI.Computability.BorderVNP.FiniteScalarMacro
import OAI.Computability.BorderVNP.FiniteProcessorWeightEvents
import OAI.Computability.BorderVNP.RoutingISACompactFrame
import OAI.Computability.BorderVNP.FiniteCellCopiesScan

/-! # The scalar-power private call on a real word burst

The return is taken from an actual TeamOpcode event and its consumed choice
list. Its little-endian arguments are exactly the scalar subtotal bits used
by the cell's guard. Padding to the last addressed machine word does not
introduce a choice or alter a field output.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldScalar

open VPVNP.BurstRAM TeamPrivateTape FieldDirectory.Copies
open scoped BigOperators Classical
open private blocks unpack_blocks length_blocks from OAI.Computability.BorderVNP.RoutingISACompactFrame

variable (F : Type*) [Field F] [Fintype F]

/-- An unframed argument with an independently terminated field record for each
scalar. Only the final RAM word can contain unused padding. -/
def burst (w : ℕ) (counts : Index F → List Bool) : List (Word w) :=
  let raw := packet F counts (Fintype.card F) le_rfl
  let n := (raw.length+w-1)/w
  blocks w n (raw ++ List.replicate (n*w-raw.length) false)

private theorem room {w : ℕ} (hw : 0<w) (x : ℕ) :
    x ≤ (x+w-1)/w*w ∧ (x+w-1)/w*w < x+w := by
  have h := Nat.div_add_mod (x+w-1) w
  rw [Nat.mul_comm] at h
  have hm := Nat.mod_lt (x+w-1) hw
  omega

omit [Field F] in
/-- The exact packed RAM word count for the issued private instruction. -/
theorem length_burst (w : ℕ) (counts : Index F → List Bool) :
    (burst F w counts).length = ((packet F counts (Fintype.card F) le_rfl).length+w-1)/w :=
  length_blocks ..

omit [Field F] in
/-- Reading all old words from the burst gives the complete framed arguments
followed by fewer than a machine word of zero padding. -/
theorem input_burst {w : ℕ} (hw : 0<w) (counts : Index F → List Bool) :
    let raw := packet F counts (Fintype.card F) le_rfl
    ∃ p < w, TeamPrivateCall.inputBits (burst F w counts) = raw ++ List.replicate p false := by
  intro raw
  let n := (raw.length+w-1)/w
  obtain ⟨h₁,h₂⟩ := room hw raw.length
  change raw.length ≤ n*w at h₁
  change n*w < raw.length+w at h₂
  exact ⟨n*w-raw.length,by omega,unpack_blocks w n (raw++List.replicate (n*w-raw.length) false) (by rw [List.length_append,List.length_replicate];omega)⟩

/-- The genuine RAM private callback returns its field output if and only if
the event supplied its unique empty choice string. -/
theorem event_value {w : ℕ} (hw : 0<w) (counts : Index F → List Bool) (fuel : ℕ)
    (event : TeamRAM.Event w) (old : event.old = burst F w counts)
    (bound : (packet F counts (Fintype.card F) le_rfl).length + Fintype.card F < fuel) :
    FieldProcessor.returned (routine F) (output F) fuel event =
      if event.choices.isEmpty then some (∏ i, (Fintype.equivFin F).symm i ^ FieldPowers.digits (counts i)) else none := by
  let raw := packet F counts (Fintype.card F) le_rfl
  obtain ⟨p,_,hx⟩ := input_burst F hw counts
  have hf : fuel = raw.length+Fintype.card F+1 + (fuel-(raw.length+Fintype.card F+1)) := by
    change raw.length+Fintype.card F<fuel at bound
    omega
  unfold FieldProcessor.returned
  rw [old,hx,hf]
  exact native_value F counts (List.replicate p false) _ event.choices

omit [Field F] in
/-- At the rectangular count width, total burst size, including all fixed
headers and word padding, is linear in the count width and the RAM word width. -/
theorem burst_bit_budget {w d : ℕ} (hw : 0<w) (c : Index F → Fin d → Bool) :
    (burst F w (fun i => List.ofFn (c i))).length*w < Fintype.card F*(2*d+1)+w := by
  rw [length_burst]
  have hl := packet_length F (fun i => List.ofFn (c i)) d (by simp) (Fintype.card F) le_rfl
  rw [hl]
  exact (room hw _).2

end FieldScalar

end BorderVNP
end Computability
end OAI
