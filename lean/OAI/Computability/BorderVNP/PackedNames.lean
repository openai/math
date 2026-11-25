import OAI.Computability.BorderVNP.ShortenSeedDescriptorRanks
import OAI.Computability.BorderVNP.ShortenNetworkHost

/-! # Stable public cable numbers under adaptive replacement

The order used by the formal interval allocator is the one induced by `Fintype.equivFin`.
After each dynamic epoch we may choose any injective public row numbers, padding unoccupied rows
by zero-width loops. The construction below presents the same tensor with the requested *actual*
allocator order. No runtime lookup of a permutation depending on the chosen profile is required.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Names

open Crossing Shortening.SeedIntervals Epoch
open scoped Classical

variable {D M : ℕ} {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable (rows : N.Edge ↪ Fin M) (dummy : Fin M → N.Site)

private noncomputable def namePerm (M : ℕ) : Fin M ≃ Fin M :=
  (Fintype.equivFin (Fin M)).trans (finCongr (Fintype.card_fin M))

/-- Translate a public row number to the edge of the padded layout carrying that name. -/
noncomputable def rowSlot {M : ℕ} (r : Fin M) : Fin M := (namePerm M).symm r

/-- Physical edge in the padded layout whose allocator name is the assigned public row. -/
noncomputable def slot (e : N.Edge) : Fin M := rowSlot (rows e)

/-- Reindexing by a bijective row map uses every actual slot exactly once. -/
noncomputable def slotEquiv (number : N.Edge ≃ Fin M) : N.Edge ≃ Fin M :=
  number.trans (namePerm M).symm

/-- The bijective presentation uses the same slot convention as the padded presentation. -/
theorem slotEquiv_apply (number : N.Edge ≃ Fin M) (e : N.Edge) :
    slotEquiv N number e = slot N number.toEmbedding e := rfl

private noncomputable def decode (i : Fin M) : Option N.Edge :=
  if h : ∃ e, slot N rows e = i then some h.choose else none

private theorem decode_slot (e : N.Edge) : decode N rows (slot N rows e) = some e := by
  unfold decode
  rw [dite_eq_left ⟨e,rfl⟩]
  congr 1
  exact rows.injective ((namePerm M).symm.injective (Exists.choose_spec (show ∃ i, slot N rows i = slot N rows e from ⟨e,rfl⟩)))

private theorem slot_decode {i : Fin M} {e : N.Edge} (h : decode N rows i = some e) :
    slot N rows e = i := by
  unfold decode at h
  split at h
  · rename_i he
    have hx := Option.some.inj h
    exact hx ▸ he.choose_spec
  · contradiction

/-- A public array with one row per candidate cable. Unoccupied rows are harmless loops of
width zero, placed at the caller's own reserved site for that row. -/
noncomputable abbrev layout : Network D P bits where
  Site := N.Site
  Edge := Fin M
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src i := ((decode N rows i).map N.src).getD (dummy i)
  dst i := ((decode N rows i).map N.dst).getD (dummy i)
  width i := ((decode N rows i).map N.width).getD 0
  attach := N.attach
  position := N.position
  in_ball := N.in_ball

/-- The interval allocator reads exactly the assigned public name. -/
theorem cableName_slot (e : N.Edge) : cableName (layout N rows dummy) (slot N rows e) = (rows e).val :=
  congrArg Fin.val ((namePerm M).apply_symm_apply _)

/-- The allocator name also agrees with the requested row at unoccupied positions. -/
theorem cableName_rowSlot (r : Fin M) : cableName (layout N rows dummy) (rowSlot r) = r.val :=
  congrArg Fin.val ((namePerm M).apply_symm_apply r)

/-- An occupied public row retains the original cable width. -/
theorem width_slot (e : N.Edge) :
    (layout N rows dummy).width (slot N rows e) = N.width e := by simp [decode_slot]

/-- An occupied public row retains the original source site. -/
theorem src_slot (e : N.Edge) :
    (layout N rows dummy).src (slot N rows e) = N.src e := by simp [layout,decode_slot]

/-- An occupied public row retains the original destination site. -/
theorem dst_slot (e : N.Edge) :
    (layout N rows dummy).dst (slot N rows e) = N.dst e := by simp [layout,decode_slot]

/-- An unused public row has both endpoints at its reserved site and has width zero. -/
theorem unused_row (r : Fin M) (hr : r ∉ Set.range rows) :
    let i := rowSlot r
    (layout N rows dummy).src i = dummy i ∧ (layout N rows dummy).dst i = dummy i ∧
      (layout N rows dummy).width i = 0 := by
  have hn : ¬ ∃ e, slot N rows e = rowSlot r :=
    fun ⟨e,he⟩ => hr ⟨e, (namePerm M).symm.injective he⟩
  simp [layout,decode,hn]

/-- The original local tensors read only occupied row slots, at their own endpoints. -/
noncomputable def tables {R : Type*} (T : N.Tables R) : (layout N rows dummy).Tables R :=
  fun v a x => T v (fun e j => a ⟨slot N rows e.val, e.property.imp
    (fun h => (src_slot N rows dummy e.val).trans h) (fun h => (dst_slot N rows dummy e.val).trans h)⟩
    (Fin.cast (width_slot N rows dummy e.val).symm j)) x

private theorem same_bit {E : Type*} (width : E → ℕ) (a : ∀ e, Fin (width e) → Bool)
    {e e' : E} (he : e = e') (i : Fin (width e)) (j : Fin (width e')) (hi : i.val = j.val) :
    a e i = a e' j := by subst e'; exact congrArg (a e) (Fin.ext hi)

/-- Assigning all words on the public grid is equivalent to assigning the real wires. -/
noncomputable def assignmentEquiv : (layout N rows dummy).Assignment ≃ N.Assignment where
  toFun a e j := a (slot N rows e) (Fin.cast (width_slot N rows dummy e).symm j)
  invFun a i j := if h : ∃ e, slot N rows e = i then
      a h.choose ⟨j.val, by
        exact j.isLt.trans_eq ((congrArg (layout N rows dummy).width h.choose_spec).symm.trans (width_slot N rows dummy h.choose))⟩
    else false
  left_inv a := by
    funext i j
    by_cases h : ∃ e, slot N rows e = i
    · dsimp only
      rw [dite_eq_left h]
      exact same_bit (layout N rows dummy).width a h.choose_spec _ _ rfl
    · have hd : decode N rows i = none := by simp [decode,h]
      have : (layout N rows dummy).width i = 0 := by simp [hd]
      exact False.elim (Nat.not_lt_zero j.val (this ▸ j.isLt))
  right_inv a := by
    funext e j
    have h : ∃ i, slot N rows i = slot N rows e := ⟨e,rfl⟩
    dsimp only
    rw [dite_eq_left h]
    have hc : h.choose = e := rows.injective ((namePerm M).symm.injective h.choose_spec)
    exact same_bit N.width a hc _ _ rfl

set_option maxHeartbeats 1000000 in
/-- Re-presenting a pack in stable row order leaves its full tensor unchanged. -/
theorem value_layout {R : Type*} [CommSemiring R] (T : N.Tables R) (x : Ports bits) :
    (layout N rows dummy).value (tables N rows dummy T) x = N.value T x := by
  let _ : DecidableEq (layout N rows dummy).Edge := Classical.decEq _
  unfold Network.value
  refine @Fintype.sum_equiv (layout N rows dummy).Assignment N.Assignment R _ _ _
    (assignmentEquiv N rows dummy) (fun a => ∏ v, (layout N rows dummy).read (tables N rows dummy T) a x v)
    (fun a => ∏ v, N.read T a x v) ?_
  exact fun _ => rfl

/-- The lengths and concentration estimates can ignore unused rows; they have zero width. -/
theorem sum_rows {R : Type*} [AddCommMonoid R] (f : N.Edge → R) :
    (∑ i : Fin M, ((decode N rows i).map f).getD 0) = ∑ e, f e := by
  classical
  have per (i : Fin M) :
      ((decode N rows i).map f).getD 0 = ∑ e : N.Edge, if slot N rows e = i then f e else 0 := by
    cases h : decode N rows i with
    | none =>
      have hn : ∀ e, slot N rows e ≠ i := by intro e he; subst i; rw [decode_slot] at h; contradiction
      simp [hn]
    | some e =>
      have hs := slot_decode N rows h
      subst i
      have hinj : Function.Injective (slot N rows) := (namePerm M).symm.injective.comp rows.injective
      simp [hinj.eq_iff]
  simp_rw [per]
  rw [Finset.sum_comm]
  simp

/-- The charged bit length is identical on the padded public presentation. -/
theorem chargedLength_layout {H : Type*} [PseudoMetricSpace H] (place : N.Site → H)
    (charged : N.Edge → Bool) :
    chargedLength (layout N rows dummy) place (fun i => ((decode N rows i).map charged).getD false) =
      chargedLength N place charged := by
  let f := fun e : N.Edge => if charged e then (N.width e : ℝ) * dist (place (N.src e)) (place (N.dst e)) else 0
  apply Eq.trans _ (sum_rows N rows f)
  apply Finset.sum_congr rfl
  intro i _
  cases h : decode N rows i <;> simp [h,f]

end Packing.Names

end BorderVNP
end Computability
end OAI
