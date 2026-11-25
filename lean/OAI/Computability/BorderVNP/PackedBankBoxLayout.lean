import OAI.Computability.BorderVNP.CrossingCellBoxStaging
import OAI.Computability.BorderVNP.CrossingProfiles
import OAI.Computability.BorderVNP.CrossingDescent

/-! # Consecutive incident cable words at a paid-term site

The incident internal cables and terminal feeders each supply a consecutive word
with a fixed one-copy width. Their widths may differ. A single affine port per
one-copy lane reads all copies from this layout. The local staging array follows
the last input bit, including at sites with no copies or no lanes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.PaidBox

open CellSparse Crossing Crossing.CellBox
open scoped Classical

/-- Incident cable bundles of one local tensor, including its terminal feeders. -/
abbrev Bundle {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits) (v : N.Site) :=
  {u : N.Edge // N.src u = v ∨ N.dst u = v} ⊕ {u : P // N.attach u = v}

private def bundleWidth {D : ℕ} {P : Type} {bits : P → ℕ} (N : Network D P bits)
    (v : N.Site) : Bundle N v → ℕ := Sum.elim (fun u => N.width u.val) (fun u => bits u.val)

/-- Fixed one-copy widths in the public site's cable order. -/
noncomputable def widths {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (v : N.Site) (r : Fin (Fintype.card (Bundle N v))) : ℕ :=
  bundleWidth N v ((Fintype.equivFin (Bundle N v)).symm r)

/-- One-copy lane order in the staged private box. -/
noncomputable def laneOrder {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (v : N.Site) : Lane N v ≃ Fin (∑ r, widths N v r) :=
  ((Equiv.sumSigmaDistrib (fun r : Bundle N v => Fin (bundleWidth N v r))).symm.trans
    (Equiv.sigmaCongrLeft' (Fintype.equivFin (Bundle N v)))).trans finSigmaFinEquiv

variable {n : ℕ} (w : Fin n → ℕ)

/-- Fixed one-copy offset of a bundle, before scaling by the histogram multiplicity. -/
def start (r : Fin n) : ℕ := ∑ t : Fin r.val, w (Fin.castLE r.isLt.le t)

/-- Position of one one-copy lane within the concatenated input cables. -/
def src (copies : ℕ) (k : Fin (∑ r, w r)) : Port :=
  let b := (finSigmaFinEquiv (n := w)).symm k
  ⟨copies * start w b.1 + b.2.val, w b.1, 1⟩

private def inputSlot (copies : ℕ) (i : Fin copies) (k : Fin (∑ r, w r)) :
    Fin (∑ r, copies*w r) :=
  let b := (finSigmaFinEquiv (n := w)).symm k
  finSigmaFinEquiv ⟨b.1,finProdFinEquiv (i,b.2)⟩

private theorem slot_addr {copies : ℕ} (i : Fin copies) (k : Fin (∑ r, w r)) :
    (inputSlot w copies i k).val = (src w copies k).atBit i.val 0 := by
  simp only [inputSlot,finSigmaFinEquiv_apply,src,Port.atBit,start,Finset.mul_sum,
    finProdFinEquiv_apply_val,zero_mul,add_zero]
  ac_rfl

/-- Each source read fits strictly before the start of staging. -/
theorem src_lt {copies : ℕ} (i : Fin copies) (k : Fin (∑ r, w r)) :
    (src w copies k).atBit i.val 0 < copies * ∑ r, w r := by
  simpa only [← slot_addr,Finset.mul_sum] using (inputSlot w copies i k).isLt

/-- Input-cable storage of the stipulated copy and lane data, in cable-major order. -/
def inputBank {copies : ℕ} (data : Fin copies → Fin (∑ r, w r) → Bool) (t : ℕ) : Bool :=
  if h : t < ∑ r, copies*w r then
    let b := (finSigmaFinEquiv (n := fun r => copies*w r)).symm ⟨t,h⟩
    let l := (finProdFinEquiv (m := copies) (n := w b.1)).symm b.2
    data l.1 (finSigmaFinEquiv ⟨b.1,l.2⟩)
  else false

set_option backward.isDefEq.respectTransparency false in
/-- Each public affine source port reads precisely its copy and lane. -/
theorem inputBank_read {copies : ℕ} (data : Fin copies → Fin (∑ r, w r) → Bool)
    (i : Fin copies) (k : Fin (∑ r, w r)) :
    inputBank w data ((src w copies k).atBit i.val 0) = data i k := by
  rw [← slot_addr, inputBank, dite_eq_left (inputSlot w copies i k).isLt]
  let b := (finSigmaFinEquiv (n := w)).symm k
  let x : Σ r, Fin (copies*w r) := ⟨b.1,finProdFinEquiv (i,b.2)⟩
  have hx := (finSigmaFinEquiv (n := fun r => copies*w r)).symm_apply_apply x
  have hi := (finProdFinEquiv (m := copies) (n := w b.1)).symm_apply_apply (i,b.2)
  simp only [Fin.eta]
  change data (finProdFinEquiv.symm ((finSigmaFinEquiv.symm (finSigmaFinEquiv x)).2)).1
    (finSigmaFinEquiv ⟨(finSigmaFinEquiv.symm (finSigmaFinEquiv x)).1,
      (finProdFinEquiv.symm ((finSigmaFinEquiv.symm (finSigmaFinEquiv x)).2)).2⟩) = _
  rw [hx]
  change data (finProdFinEquiv.symm (finProdFinEquiv (i,b.2))).1
    (finSigmaFinEquiv ⟨b.1,(finProdFinEquiv.symm (finProdFinEquiv (i,b.2))).2⟩) = _
  rw [hi]
  exact congrArg (data i) ((finSigmaFinEquiv (n := w)).apply_symm_apply k)

set_option backward.isDefEq.respectTransparency false in
/-- Every bit in the input storage is some source bit, even with zero-width bundles. -/
theorem src_cover {copies t : ℕ} (ht : t < copies * ∑ r, w r) :
    ∃ (i : Fin copies) (k : Fin (∑ r, w r)), (src w copies k).atBit i.val 0 = t := by
  rw [Finset.mul_sum] at ht
  obtain ⟨⟨r,b⟩,hb⟩ := (finSigmaFinEquiv (n := fun r => copies*w r)).surjective (⟨t,ht⟩ : Fin _)
  obtain ⟨⟨i,l⟩,rfl⟩ := finProdFinEquiv.surjective b
  refine ⟨i, finSigmaFinEquiv ⟨r,l⟩, ?_⟩
  rw [← slot_addr]
  unfold inputSlot
  rw [(finSigmaFinEquiv (n := w)).symm_apply_apply ⟨r,l⟩]
  exact congrArg Fin.val hb

end Packing.PaidBox

end BorderVNP
end Computability
end OAI
