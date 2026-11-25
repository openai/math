import OAI.ThreeFlat.RAM.InitialRelayWidth
import OAI.ThreeFlat.Diagonal.SlotImage

namespace OAI
/-! # The six graph columns and the first width sweep form a stored lifted graph -/

namespace ThreeFlat.RAM.InitialRelayWidth

open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression Diagonal.SlotImage
open scoped Fin.CommRing

variable {W v lanes d : ℕ} {B L : Type*}

theorem stored (G : LiftedSlots B d L) (base : B ≃ Fin v) (lane : L ≃ Fin lanes)
    (C : Columns) (m : Memory W) (t : ℕ) (fit : t<2^W) (rows : C.rows=v*d)
    (graph : ∀ p back f, (m (cell C base p back f)).val=fields G base lane p back f)
    (apart : C.graph+6*C.rows≤C.widths ∨ C.widths+v*d*lanes≤C.graph) :
    Stored G base lane C (fun a => (image C.widths (v*d*lanes) t m a).val) (fun _ => t) := by
  let old := fun e : Edge B L d => (m (C.widths+edgeOrdinal base lane e)).val
  have before : Stored G base lane C (fun a => (m a).val) old := ⟨rows,graph,fun _ => rfl⟩
  refine ⟨rows,?_,?_⟩
  · intro p back f
    have h := cell_range before p back f
    rw [image_outside _ _ _ _ _ (by omega)]
    exact graph p back f
  · intro e
    let j : Fin (v*d*lanes) := ⟨edgeOrdinal base lane e,edgeOrdinal_lt base lane e⟩
    change (image _ _ _ m (C.widths+j.val)).val = t
    rw [image_word _ _ _ _ j,Fin.val_cast_of_lt fit]

end ThreeFlat.RAM.InitialRelayWidth

end OAI
