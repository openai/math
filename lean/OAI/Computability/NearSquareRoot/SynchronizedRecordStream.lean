import OAI.Computability.NearSquareRoot.SynchronizedAddressOrder
import OAI.Computability.NearSquareRoot.BoxOrder
import OAI.Computability.NearSquareRoot.BoxMaskedRecords

/-! # Record streams for the padded tensor

The mask produced by the shape recursion agrees position by position with the
occupied tensor. The linear-time record expansion and compacting passes can
therefore consume and return the dense mixed-radix digit list in order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxFin

variable {box : List (ℕ × ℕ)} {k l : ℕ} (hb : BoxShape.Valid k l box)
    [∀ i, NeZero (modulus box i)]

/-- Test each bit field of the flat physical address against the axis bound. -/
def validSlot (t : Fin (2^k)) : Bool := decide (∀ i : Fin box.length,
    (t.val / 2^(offset i)) % 2^(box.get i).1 < modulus box i)

include hb in
theorem physical_mask :
    BoxOrder.expand (BoxOrder.shape box) = List.ofFn (validSlot (box := box) (k := k)) := by
  apply List.ext_getElem
  · simp [BoxOrder.length_shape hb]
  · intro i hi _
    let t : Fin (2^k) := ⟨i, by rwa [BoxOrder.length_shape hb] at hi⟩
    let u := (recordIndex hb).symm t
    let q (j : Fin box.length) := field hb j (u j)
    have hpos : CRT.rank (fun j => 2^(box.get j).1) (fun j => (q j).val) = i := by
      rw [CRT.rank_eq_finPiFinEquiv]
      change (recordIndex hb ((recordIndex hb).symm t)).val = i
      rw [Equiv.apply_symm_apply]
    have H := BoxOrder.at_rank_iff hb (fun j => (q j).val) (fun j => (q j).isLt)
    rw [hpos, List.getElem?_eq_getElem hi, Option.some.injEq] at H
    simp only [List.getElem_ofFn, validSlot]
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq, q, u, extract_field] using H

theorem validSlot_digitSlot (t : Fin (∏ i, modulus box i)) :
    validSlot (box := box) (digitSlot hb t) = true := by
  rw [validSlot, decide_eq_true_eq, ← occupied_iff hb]
  exact ⟨_, ((recordIndex hb).symm_apply_apply _).symm⟩

/-- Enumerate any physical array with its validity tags. -/
def tagged {A : Type} (g : Fin (2^k) → A) : List (Bool × A) :=
  (List.finRange (2^k)).map (fun t => (validSlot (box := box) t, g t))

include hb in
private theorem tagged_mask {A : Type} (g : Fin (2^k) → A) :
    (tagged (box := box) g).map Prod.fst = BoxOrder.expand (BoxOrder.shape box) := by
  rw [physical_mask hb, tagged, List.map_map, List.ofFn_eq_map]
  rfl

omit [∀ i, NeZero (modulus box i)] in
private theorem tagged_payload {A : Type} (g : Fin (2^k) → A) :
    (tagged (box := box) g).map Prod.snd = List.ofFn g := by
  rw [tagged, List.map_map, List.ofFn_eq_map]
  rfl

theorem selected_tagged {A : Type} (g : Fin (2^k) → A) :
    BoxMaskedRecords.selected (tagged (box := box) g) = List.ofFn (g ∘ digitSlot hb) := by
  simp only [BoxMaskedRecords.selected, tagged, List.filter_map, List.map_map]
  change ((List.finRange (2^k)).filter (validSlot (box := box))).map g = _
  rw [show (List.finRange (2^k)).filter (validSlot (box := box)) = List.ofFn (digitSlot hb) from
    filter_valid_slots hb, List.map_ofFn]

/-- Scatter dense digits to padded physical positions with a fixed fill record. -/
noncomputable def scatter {A : Type} (pad : A) (f : Fin (∏ i, modulus box i) → A) :
    Fin (2^k) → A := Function.extend (digitSlot hb) f (fun _ => pad)

theorem expand_dense {A : Type} (pad : A) (f : Fin (∏ i, modulus box i) → A) :
    BoxMaskedRecords.expand pad (BoxOrder.expand (BoxOrder.shape box), List.ofFn f) =
      List.ofFn (scatter hb pad f) := by
  let g := scatter hb pad f
  have left : g ∘ digitSlot hb = f := funext fun x =>
    (digitSlot_strictMono hb).injective.extend_apply f (fun _ => pad) x
  change BoxMaskedRecords.expand pad (_, List.ofFn f) = List.ofFn g
  conv_lhs => rw [← left]
  rw [← selected_tagged, ← tagged_mask hb g, BoxMaskedRecords.expand_tagged,
    tagged, List.map_map, List.ofFn_eq_map]
  apply List.map_congr_left
  intro x _
  by_cases hx : x ∈ Set.range (digitSlot hb)
  · obtain ⟨t,rfl⟩ := hx
    simp [validSlot_digitSlot hb]
  · have he : g x = pad := Function.extend_apply' _ _ _ hx
    change (bif validSlot (box := box) x then g x else pad) = g x
    rw [he]
    cases validSlot (box := box) x <;> rfl

/-- Compacting an arbitrary physical stream reads exactly the valid digit slots. -/
theorem compress_dense {A : Type} (dummy : A) (g : Fin (2^k) → A) :
    BoxMaskedRecords.compress dummy (BoxOrder.expand (BoxOrder.shape box), List.ofFn g) =
      List.ofFn (g ∘ digitSlot hb) := by
  rw [← tagged_mask hb g, ← tagged_payload (box := box) g, BoxMaskedRecords.compress_tagged,
    selected_tagged]

end BoxFin

end NearSquareRoot
end Computability
end OAI
