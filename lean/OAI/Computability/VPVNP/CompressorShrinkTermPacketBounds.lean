import OAI.Computability.VPVNP.CompressorShrinkTermPackets
import OAI.Computability.VPVNP.CompressorOrdinalProgress

/-!
# Work and data-arena bounds of the shrinking term packets

Both packets can be replayed under the online calendar. Every cursor
increment occurs before the exclusive motif stop. Their reads and
writes stay within the current shrinking arena, and each report obeys
the source instruction cap.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkTermPackets

open BurstRAM BlockPlanner Compression ShrinkBlockInputs ShrinkInput SourceOnline SourceTransport
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {i : Fin S.steps} {origin : PhaseRecipe.Expr}
variable {g w : ℕ} {X : State (a i) (packingLaneBits (a i) g)} {T : IncidenceDirectory w} {start cap : ℕ}
variable {s : X.ShrinkSelection B.shrink} {j : Stage} {m : Memory w} {rs : List (Report w)}

local notation "N" => ShrinkTermInputs.motifCount X
local notation "Z" => ShrinkInput.plan X start
local notation "q" => ShrinkRankSpace.Shape.collectBank (ShrinkInput.plan X start) w
local notation "W" => widthBase X start
local notation "K" => ShrinkTermSelection.bundles X*ShrinkTermSelection.ranks (a i)

/-- The two source rows already have the cursor progress, private cap and
external charge needed to construct their linked online rows. -/
theorem PacketRun.bounds (h : PacketRun B i origin X T start s cap j m rs) (stopFits : N < 2^w) :
    Progress (N : Word w) 0 rs ∧ (∀ r ∈ rs, r.events.length < cap) ∧
      RAMBuckets.cost Report.probes rs ≤ N * (1+probeRate B j) := by
  have he := Progress.ofOrdinals N 0 N stopFits (Nat.zero_add _) rs h.cursors
  have work := localSegment_event_bound ((runSegment_iff ..).mp h.run).1
  refine ⟨he,work,?_⟩
  rw [packet_cost,h.count,Nat.mul_add,Nat.mul_one]
  exact Nat.add_le_add_left h.probes N

/-- A data replay needs agreement only inside the allocated shrinking
level. In particular all locations before the level's start are excluded. -/
theorem PacketRun.arena (h : PacketRun B i origin X T start s cap j m rs)
    (room : termEnd X start 10 < 2^w) :
    Reads (fun x => start ≤ x ∧ x < termEnd X start 10) (eventLog rs) ∧
      Writes (fun x => start ≤ x ∧ x < termEnd X start 10) (eventLog rs) := by
  have count := ShrinkTermSelection.motifCount_eq X
  have endSpace : termEnd X start 10 = ShrinkInput.stop X start + 2*K+K*10 := rfl
  have stopEq : ShrinkInput.stop X start = W+6*K+2*(Z).B := rfl
  have hrank : (Z).stop < 2^w := by change W < _; omega
  have v := (Z).values T (placementBank X T start) Fintype.card_pos hrank
  have begin := ShrinkInput.range_bounds X start
  have first : start ≤ W := begin.1.trans (begin.2.1.trans begin.2.2.1)
  have dense : (demandHead (w := w) X start).val = ShrinkInput.stop X start := Nat.mod_eq_of_lt (by omega)
  have term : (termHead (w := w) X start).val = ShrinkInput.stop X start+2*K := Nat.mod_eq_of_lt (by omega)
  let bank := pairBank X T start
  have ab : (bank 3).val = W+4*K+2*(Z).B := by
    change (W+2*((Z).B*(q 4).val)+2*((Z).B*(q 4).val)+2*(Z).B)%(2^w) = _
    rw [v.stride]
    change (W+2*K+2*K+2*(Z).B)%(2^w) = _
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  have cd : (bank 4).val = W+K := by
    have word : (ShrinkRAM.word w W).val = W := Nat.mod_eq_of_lt hrank
    change ((ShrinkRAM.word w W).val+(Z).B*(q 4).val)%(2^w) = _
    rw [word,v.stride]; change (W+K)%(2^w) = W+K; apply Nat.mod_eq_of_lt; omega
  have ⟨_,earlier,_,_⟩ := termLayout X T start 10 room
  have topAB : (bank 3).val+(Z).B*(bank 1).val ≤ (demandHead (w := w) X start).val := earlier.abWidths
  have topCD : (bank 4).val+(Z).B*(bank 2).val ≤ (demandHead (w := w) X start).val := earlier.cdWidths
  cases j with
  | gather =>
    refine ⟨fun a v mem => ?_,fun a v mem => ?_⟩
    · rcases h.reads a v mem with hab|hcd
      · change (bank 3).val ≤ a.val ∧ a.val < (bank 3).val+(Z).B*(bank 1).val at hab
        omega
      · change (bank 4).val ≤ a.val ∧ a.val < (bank 4).val+(Z).B*(bank 2).val at hcd
        omega
    · have wr := h.writes a v mem
      change (demandHead (w := w) X start).val ≤ a.val ∧ a.val < (demandHead (w := w) X start).val+2*K at wr
      omega
  | select =>
    refine ⟨fun a v mem => ?_,fun a v mem => ?_⟩
    · have rd := h.reads a v mem
      change (demandHead (w := w) X start).val ≤ a.val ∧ a.val < (termHead (w := w) X start).val+N*10 at rd
      omega
    · have wr := h.writes a v mem
      change (termHead (w := w) X start).val ≤ a.val ∧ a.val < (termHead (w := w) X start).val+N*10 at wr
      omega

end CompressorRecords.ShrinkTermPackets

end VPVNP
end Computability
end OAI
