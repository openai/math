import OAI.Hierarchy.ProtocolRAMPortRanks
import OAI.Hierarchy.ProtocolRAMEmit
import OAI.Hierarchy.TaggedShorterFields

namespace OAI
/-! # Enumerating actual reported occurrences at both sides of a shorter board -/

noncomputable section
namespace Hierarchy.ProtocolRAMReportedPorts
open ProtocolRAMPortRanks
open scoped Classical BigOperators

variable {n w q d D : ℕ}

abbrev Row := ProtocolRAMEmit.Row

/-- Rows of the given emitted group and dyadic width class. -/
abbrev InGroup (rows : Fin n → Row) (w m γ g : ℕ) :=
  {i : Fin n // (rows i).group=g ∧ TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ))=γ}

def pieces (rows : Fin n → Row) (w : ℕ) (i : Fin n) :=
  TaggedShorterBudget.copies ((rows i).width/(w:ℝ))

def count (rows : Fin n → Row) (w m γ g : ℕ) :=
  ∑ i : InGroup rows w m γ g, pieces rows w i.val

def sideSite (rows : Fin n → Row) (b : Bool) (i : Fin n) : ℕ :=
  if b then (rows i).opposite else (rows i).endpoint

def slotCount (rows : Fin n → Row) (w m γ g : ℕ) (j : InGroup rows w m γ g) :=
  pieces rows w j.val

abbrev Unit (rows : Fin n → Row) (w m γ g : ℕ) := Units (slotCount rows w m γ g)

/-- Dense common names are in the order of the actual global link IDs.
The unit ordinal is kept for links spanning several lane words. -/
def common (rows : Fin n → Row) (w m γ g : ℕ)
    (distinct : Function.Injective fun i => (rows i).link) :
    Unit rows w m γ g ≃ Fin (count rows w m γ g) :=
  enumerate (slotCount rows w m γ g) (fun j=> (rows j.val).link)
    (distinct.comp Subtype.val_injective)

/-- Host addresses use physical endpoint order. Repeated equal endpoints
reserve distinct intervals, ordered by original row ordinal. -/
def localPort (rows : Fin n → Row) (w m γ g : ℕ) (b : Bool) :
    Unit rows w m γ g ≃ Fin (count rows w m γ g) :=
  enumerate (slotCount rows w m γ g) (fun j=>bySite (sideSite rows b) j.val)
    ((bySite_injective _).comp Subtype.val_injective)

def place (rows : Fin n → Row) (w m γ g : ℕ)
    (distinct : Function.Injective fun i => (rows i).link)
    (capacity : count rows w m γ g≤D) (b : Bool) :
    Fin (count rows w m γ g) ↪ Fin D :=
  ((common rows w m γ g distinct).symm.trans (localPort rows w m γ g b)).toEmbedding.trans
    (Fin.castLEEmb capacity)

theorem read_place (rows : Fin n → Row) (w m γ g : ℕ)
    (distinct : Function.Injective fun i => (rows i).link)
    (capacity : count rows w m γ g≤D) (b : Bool) (u : Unit rows w m γ g) :
    (place rows w m γ g distinct capacity b ((common rows w m γ g distinct) u)).val =
      «prefix» (slotCount rows w m γ g) (fun j=>bySite (sideSite rows b) j.val) u.1+u.2.val := by
  simp only [place,Function.Embedding.trans_apply,Equiv.toEmbedding_apply,
    Equiv.trans_apply,Equiv.symm_apply_apply]; rfl

/-- The capacity consumed by this class is the sum of the rounded wire
multiplicities. The lane at each unit reads its padded part of the true
reported word. Checking all units is equivalent to checking the word. -/
theorem equality_of_units (rows : Fin n → Row) (m γ g : ℕ) (hw : 0<w)
    (i : InGroup rows w m γ g)
    (x y : Fin (rows i.val).width → Bool) :
    let width := ⌈TaggedShorterBudget.dyadic γ*w⌉₊
    (∀ z : Fin (pieces rows w i.val), TaggedShorterFields.slice width x z.val =
      TaggedShorterFields.slice width y z.val) ↔ x=y := by
  apply TaggedShorterFields.eq_iff_slices
  have room := TaggedShorterFields.rounded_room (rows i.val).width w m hw
  simpa only [pieces, i.property.2] using room

/-- Grouping cannot multiply the charged pool volume. Every occurrence
of the class is in precisely its emitted group. -/
theorem total_count (rows : Fin n → Row) (groups w m γ : ℕ)
    (room : ∀ i, (rows i).group<groups) :
    (∑ g : Fin groups, count rows w m γ g.val) =
      ∑ i : {i : Fin n // TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ))=γ},
        pieces rows w i.val := by
  let unpack : ((g : Fin groups) × InGroup rows w m γ g.val) ≃
      {i : Fin n // TaggedShorterBudget.widthIndex m ((rows i).width/(w:ℝ))=γ} :=
    { toFun := fun p => ⟨p.2.val,p.2.property.2⟩
      invFun := fun i => ⟨⟨(rows i.val).group,room i.val⟩,⟨i.val,rfl,i.property⟩⟩
      left_inv := by
        rintro ⟨g,i⟩
        obtain ⟨j,hg,hγ⟩ := i
        obtain ⟨g,hbound⟩ := g
        change (rows j).group=g at hg
        subst g
        rfl
      right_inv := fun _=>rfl }
  unfold count
  rw [←Fintype.sum_sigma']
  apply Fintype.sum_equiv unpack
  intros
  rfl

end Hierarchy.ProtocolRAMReportedPorts

end
end OAI
