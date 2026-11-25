import OAI.Computability.BorderVNP.CubeLabelProducerVolumes
import OAI.Computability.BorderVNP.PackedCableColumns
import OAI.Computability.BorderVNP.DiagonalExternalSewVolume

/-! # Reading the physical traffic volume after both sparse tables are published -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.CableTriples

open Crossing CellAddressCircuit CellAddressPhysical ParseBatchSort RoutingISA VPVNP.BurstRAM
open Cube.LabelIndex DiagonalResidueRAM
open scoped BigOperators Classical

/-- The three-word geometry output and the seven-word compact directory carry at
most the physical intercell wire volume plus the total delivery capacity. -/
theorem published_inputWidth {D s n C d k w b W : ℕ} (l : Cube.LabelIndex.Layout)
    {P : Type} {bits : P → ℕ} (N : Network D P bits) (cell : N.Site → Fin C) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin l.cableCount) (portID : P ↪ Fin n)
    {σ : Type*} [Fintype σ] (F : Fields s l.cableCount n C d k w σ) (x : σ → Bool)
    (physical : Represents N cell aux siteID edgeID portID F x) (code : ∀ c, (F.cells c).val = c.val)
    (hk : k ≤ b) (hw : w ≤ b) (wide : b ≤ W) (m : Memory W)
    (outputs : ∀ a : Fin (l.cableCount*3), m (l.cables+a.val) =
      word W (value fun j => (frame F hk hw).eval x (a,j)))
    (src : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (head : ℕ)
    (hp : 0 < src.processors) (hf : 0 < src.fields) (hb : 0 < src.block)
    (tails : src.entries*src.description ≤ src.teams*src.processors*(src.literal/2))
    (count : l.deliveryCount = (src.directory pp lp).length) (before : head+9 < l.deliveries)
    (hframe : head+9 < l.cables)
    (separate : l.cables+l.cableCount*3 ≤ l.deliveries ∨ l.deliveries+7*l.deliveryCount ≤ l.cables)
    (fits : ∀ i : Fin (src.directory pp lp).length, ∀ a ∈ (src.directory pp lp)[i.val].words, a < 2^W) :
    let rows := src.directory pp lp
    let pub := Directory.ISA.publish m head l.deliveries rows
    inputWidth l (readings pub) ≤ Diagonal.ExternalSew.intercellWidth N cell +
      src.teams*((src.fields+1)*(src.processors*src.literal)) := by
  intro rows pub
  change l.deliveryCount = rows.length at count
  have cables (i : Fin l.cableCount) : cableAt l (readings pub) i = row F x i :=
    (cableAt_publish m head l rows hframe (by simpa only [← count] using separate) i).trans
      (cableAt_outputs F hk hw wide x l m outputs i)
  have sumc : sumWidth (Cube.LabelIndex.Cable.width ∘ cableAt l (readings pub)) l.cableCount =
      Diagonal.ExternalSew.intercellWidth N cell := by
    rw [sumWidth_eq_fin]
    simp only [Function.comp_apply,cables,raw_width_sum N cell aux siteID edgeID portID F physical code]
    unfold Diagonal.ExternalSew.intercellWidth Shortening.testedWidth
    apply Fintype.sum_of_injective (fun e : N.CrossingEdge cell => e.val) Subtype.val_injective
    · intro e he
      have h : ¬ cell (N.src e) ≠ cell (N.dst e) := fun hc => he ⟨⟨e,hc⟩,rfl⟩
      simp [h]
    · intro e
      simp [e.property]
  have datum (i : Fin rows.length) : (deliveryAt l (readings pub) i).2 = (rows.get i).width :=
    congrArg Prod.snd (deliveryAt_publish m head l rows before i (fits i))
  have sumd : sumWidth (Prod.snd ∘ deliveryAt l (readings pub)) l.deliveryCount = (rows.map Directory.Row.width).sum := by
    rw [count,sumWidth_eq_fin]
    change (∑ i : Fin rows.length, (deliveryAt l (readings pub) i).2) = _
    simp only [datum]
    conv_rhs => rw [← List.ofFn_get rows,List.map_ofFn,List.sum_ofFn]
    rfl
  unfold inputWidth
  rw [sumc,sumd]
  exact Nat.add_le_add_left (src.populated_width pp lp hp hf hb tails) _

end Packing.CableTriples

end BorderVNP
end Computability
end OAI
