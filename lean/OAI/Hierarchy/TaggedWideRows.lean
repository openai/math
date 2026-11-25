import OAI.Hierarchy.TaggedWidePartialSlices
import OAI.Hierarchy.ProtocolRAMReportOrdinal
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # All actual link words from the stack labels of a heterogeneous menu -/

noncomputable section
namespace Hierarchy.Tagged.WideStack
open ProtocolRAMReportedPorts TaggedShorterFields TaggedShorterBudget
open scoped Classical BigOperators
variable {T F : Type*} [Fintype T] [CommSemiring F]
    {n : T → ℕ} (groups γ : T → ℕ) (rows : ∀ i,Fin (n i) → ProtocolRAMEmit.Row) (w m : ℕ)

abbrev Occ := (i : T) × (g : Fin (groups i)) × InGroup (rows i) w m (γ i) g.val
abbrev Lanes := ∀ i, ((g : Fin (groups i)) × Fin (count (rows i) w m (γ i) g.val)) →
  Fin ⌈dyadic (γ i)*w⌉₊ → Bool

variable (unique : ∀ t,Function.Injective (fun i => (rows t i).link))

/-- The native common ID is precisely the dense index of the selected link
and its subslot. This equivalence keeps all occurrences with the same site
distinct and works simultaneously with all candidate dimensions. -/
def rowLanes : Lanes groups γ rows w m ≃
    (∀ r : Occ groups γ rows w m, Fin (pieces (rows r.1) w r.2.2.val) → Fin ⌈dyadic (γ r.1)*w⌉₊ → Bool) where
  toFun := fun x r z => x r.1 ⟨r.2.1, common (rows r.1) w m (γ r.1) r.2.1.val (unique r.1) ⟨r.2.2,z⟩⟩
  invFun := fun y t p => let u := (common (rows t) w m (γ t) p.1.val (unique t)).symm p.2
                         y ⟨t,p.1,u.1⟩ u.2
  left_inv := by
    intro x
    funext t p
    obtain ⟨g,j⟩ := p
    let e := common (rows t) w m (γ t) g.val (unique t)
    change x t ⟨g,e ⟨(e.symm j).1,(e.symm j).2⟩⟩ = x t ⟨g,j⟩
    rw [Sigma.eta,Equiv.apply_symm_apply]
  right_inv := by
    intro y
    funext r j
    obtain ⟨t,g,i⟩ := r
    let e := common (rows t) w m (γ t) g.val (unique t)
    change y ⟨t,g,(e.symm (e ⟨i,j⟩)).1⟩ (e.symm (e ⟨i,j⟩)).2 = _
    rw [Equiv.symm_apply_apply]

/-- After the actual bank has checked the two half-edge placements, its
dense common labels range exactly over the true original link widths.
The per-terminal site weight can inspect the entire menu jointly. -/
theorem sum_row_words (hw : 0<w)
    (φ : (∀ r : Occ groups γ rows w m, Fin (pieces (rows r.1) w r.2.2.val) →
      Fin ⌈dyadic (γ r.1)*w⌉₊ → Bool) → F) :
    let bits := fun r : Occ groups γ rows w m => (rows r.1 r.2.2.val).width
    let width := fun r : Occ groups γ rows w m => ⌈dyadic (γ r.1)*w⌉₊
    let copies := fun r : Occ groups γ rows w m => pieces (rows r.1) w r.2.2.val
    let labels := rowLanes groups γ rows w m unique
    (∑ u,if highZeros bits width copies (labels u) then φ (labels u) else 0) =
      ∑ x : ∀ r, Fin (bits r) → Bool, φ (allSlices bits width copies x) := by
  intro bits width copies labels
  have enough (r : Occ groups γ rows w m) : bits r ≤ copies r * width r := by
    have h := rounded_room (rows r.1 r.2.2.val).width w m hw
    simpa only [bits,copies,width,pieces,r.2.2.property.2] using h
  let cost := fun y=>if highZeros bits width copies y then φ y else 0
  have sliced := sum_sliced bits width copies enough φ
  refine (labels.sum_comp cost).trans (Eq.trans ?_ (sliced.trans ?_))
  all_goals
    apply Finset.sum_congr _ (fun _ _=>rfl)
    ext y
    simp

/-- Expressing the remaining ordinary row bits in the original signed
kernel's basis uses the least significant bit order of its physical
prefix-width reads. -/
theorem sum_row_basis (hw : 0<w)
    (φ : (∀ r : Occ groups γ rows w m, Fin (pieces (rows r.1) w r.2.2.val) →
      Fin ⌈dyadic (γ r.1)*w⌉₊ → Bool) → F) :
    let bits := fun r : Occ groups γ rows w m => (rows r.1 r.2.2.val).width
    let width := fun r : Occ groups γ rows w m => ⌈dyadic (γ r.1)*w⌉₊
    let copies := fun r : Occ groups γ rows w m => pieces (rows r.1) w r.2.2.val
    let labels := rowLanes groups γ rows w m unique
    (∑ u,if highZeros bits width copies (labels u) then φ (labels u) else 0) =
      ∑ v : ∀ r, Fin (2^(bits r)), φ (allSlices bits width copies (fun r j=>(v r).val.testBit j.val)) := by
  intro bits width copies labels
  rw [sum_row_words groups γ rows w m unique hw]
  let e : (∀ r,Fin (2^(bits r))) ≃ (∀ r,Fin (bits r) → Bool) :=
    Equiv.piCongrRight fun r=>Computability.VPVNP.RAMSerialization.wordBits (bits r)
  let f := fun a=>φ (allSlices bits width copies a)
  calc
    _ = ∑ a,f (e a) := (e.sum_comp f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      apply congrArg φ
      apply congrArg (allSlices bits width copies)
      funext r j
      exact (Computability.VPVNP.LiveHeader.testBit_wordBits (v r) j).symm

end Hierarchy.Tagged.WideStack

end
end OAI
