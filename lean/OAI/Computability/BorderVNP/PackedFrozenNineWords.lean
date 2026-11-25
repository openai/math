import OAI.Computability.BorderVNP.PackedFrozenTapeRows
import OAI.Computability.BorderVNP.PackedInheritedLayerFreeze

/-! # Nine-word interval commands as frozen site records -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.NineWords

open VPVNP.VerifierNetwork ParseBatchSort

variable {R σ : Type*} {d w : ℕ}

/-- The public source order and the nine static relocation roles of interval commands. -/
def schema (rows : List R) (w : ℕ) : Schema R (R × Fin 9 × Fin w) where
  rows := rows
  tags _ := List.ofFn Layer.kind
  width _ := w
  pin r i j := (r,i,j)

/-- Coordinate wiring from a frozen tape pin to its scalar, flag, or owner in the interval frame. -/
def pin : Pins R (R × Fin 9 × Fin w) d → R × Layer.Output d w
  | .inl (r,.inl ()) => (r,.inl ())
  | .inl (r,.inr j) => (r,.inr (.inl j))
  | .inr (r,i,j) => (r,.inr (.inr (i,j)))

variable [Fintype σ] [Fintype R] (f : Frame σ (R × Layer.Output d w))

/-- Present the nine-word emitter as a frozen tape without copying any gate. -/
noncomputable def adapt : Frame σ (Pins R (R × Fin 9 × Fin w) d) := f.select pin

/-- Relabeling the output pins adds no gates. -/
@[simp] theorem adapt_size : (adapt f).size = f.size := by simp [adapt]

/-- The frozen schema reads the nine emitted fields with their actual relocation roles. -/
theorem read (rows : List R) (x : σ → Bool) (r : R) :
    (schema rows w).read ((adapt f).eval x) r =
      List.ofFn (fun i => (Layer.kind i,value (fun j => f.eval x (r,.inr (.inr (i,j)))))) := by
  apply List.ext_getElem
  · simp only [Schema.read,schema,List.length_ofFn]
  · intro i _ _
    simp only [Schema.read,schema,List.getElem_ofFn,adapt,Frame.select_eval,pin]
    apply Prod.ext
    · change (List.ofFn Layer.kind)[i]'_ = _
      rw [List.getElem_ofFn]
    · rfl

private theorem filterRead {A B : Type*} (rows : List A) (en : A → Bool) (get : A → B) :
    (rows.filterMap fun r => if en r then some (get r) else none) = (rows.filter en).map get := by
  induction rows with
  | nil => rfl
  | cons r rows ih => cases h : en r <;> simp [h,ih]

/-- Filter the actual owner and enable pins and read every scalar of each resulting row.
The outer list retains all command boundaries. -/
theorem atSite (rows : List R) (x : σ → Bool) (key : ℕ) :
    (schema rows w).atSite ((adapt f).eval x) key =
      (rows.filter (fun r => f.eval x (r,.inl ()) &&
        decide (value (fun j => f.eval x (r,.inr (.inl j))) = key))).map
        (fun r => List.ofFn fun i => (Layer.kind i,value fun j => f.eval x (r,.inr (.inr (i,j))))) := by
  rw [← filterRead,Schema.atSite]
  apply List.filterMap_congr
  intro r _
  simp only [owner,adapt,Frame.select_eval,pin,Bool.and_eq_true,decide_eq_true_eq]
  congr 2
  exact read f rows x r

end Packing.Inherited.FrozenTape.NineWords

end BorderVNP
end Computability
end OAI
