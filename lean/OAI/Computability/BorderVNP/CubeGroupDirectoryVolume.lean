import OAI.Computability.BorderVNP.CubeLabelProducerVolumes
import OAI.Computability.BorderVNP.PackedCableColumns

/-! # Incoming width in the published seven-word delivery directory

The group-weight pass reads the width at offset six in each compact row. These
widths account for the private tail and up to two live literal fields.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CableTriples

open Cube.LabelIndex RoutingISA VPVNP.BurstRAM
open scoped BigOperators

/-- Summing the actual width column over the published row count recovers the
total width of the compact list. -/
theorem published_deliveryWidth_eq {W : ℕ} (l : Cube.LabelIndex.Layout) (m : Memory W)
    (rows : List Directory.Row) (head : ℕ) (count : l.deliveryCount = rows.length)
    (before : head + 9 < l.deliveries)
    (fits : ∀ i : Fin rows.length, ∀ a ∈ rows[i.val].words, a < 2 ^ W) :
    let pub := Directory.ISA.publish m head l.deliveries rows
    (∑ j : Fin l.deliveryCount, (deliveryAt l (readings pub) j.val).2) =
      (rows.map Directory.Row.width).sum := by
  intro pub
  rw [count]
  have datum (i : Fin rows.length) : (deliveryAt l (readings pub) i.val).2 = (rows.get i).width :=
    congrArg Prod.snd (deliveryAt_publish m head l rows before i (fits i))
  simp only [datum]
  conv_rhs => rw [← List.ofFn_get rows, List.map_ofFn, List.sum_ofFn]
  rfl

/-- All incoming deliveries in the seven-word directory fit three literal
fields per processor when the live-field count is at most two. -/
theorem published_deliveryWidth_le {W : ℕ} (l : Cube.LabelIndex.Layout) (m : Memory W)
    (src : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (head : ℕ)
    (hp : 0 < src.processors) (hf : 0 < src.fields) (hb : 0 < src.block) (fields : src.fields ≤ 2)
    (tails : src.entries * src.description ≤ src.teams * src.processors * (src.literal / 2))
    (count : l.deliveryCount = (src.directory pp lp).length) (before : head + 9 < l.deliveries)
    (fits : ∀ i : Fin (src.directory pp lp).length,
      ∀ a ∈ (src.directory pp lp)[i.val].words, a < 2 ^ W) :
    let pub := Directory.ISA.publish m head l.deliveries (src.directory pp lp)
    (∑ j : Fin l.deliveryCount, (deliveryAt l (readings pub) j.val).2) ≤
      3 * src.teams * src.processors * src.literal := by
  intro pub
  calc
    _ = _ := published_deliveryWidth_eq l m (src.directory pp lp) head count before fits
    _ ≤ src.teams * ((src.fields + 1) * (src.processors * src.literal)) :=
      src.populated_width pp lp hp hf hb tails
    _ ≤ src.teams * (3 * (src.processors * src.literal)) := by
      gcongr
      omega
    _ = _ := by ring

end Packing.CableTriples

end BorderVNP
end Computability
end OAI
