import OAI.Computability.VPVNP.CursorNetwork
import OAI.Computability.VPVNP.SlotGraph

/-!
# Zero-width parallel slots of the cursor network

Section 12 pads the two original arcs to the compressor's prescribed degree
by making extra copies of the no-flip arc. Each copy carries a singleton
alphabet. Distinct copies retain distinct slot numbers at both endpoints.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CursorNetwork

open CursorRouting NetworkKernel

/-- Original cursor arcs together with the padding slots indexed by a position and a local
padding ordinal. -/
abbrev PaddedArc (D p : ℕ) := Arc D ⊕ (Position D × Fin p)

variable {S : Type} [Fintype S] {D p : ℕ}

open scoped Classical in
/-- Add one zero-width copy of the no-flip arc for each extra slot. -/
noncomputable def paddedNetwork (D p : ℕ) (bits : S → ℕ) : Network where
  Site := Position D
  Edge := PaddedArc D p
  src := Sum.elim (network D bits).src Prod.fst
  dst := Sum.elim head (fun e ↦ head (e.1.1, e.1.2, false))
  Payload := Sum.elim (fun _ ↦ Payload bits) (fun _ ↦ Unit)
  siteFintype := inferInstance
  edgeFintype := inferInstance
  payloadFintype e := by
    cases e with
    | inl _ => exact inferInstanceAs (Fintype (Payload bits))
    | inr _ => exact inferInstanceAs (Fintype Unit)

variable {bits : S → ℕ}

/-- The incident fields on the genuine arcs of a padded position. -/
def unpadHalf (p : ℕ) (v : Position D) (z : (paddedNetwork D p bits).Half v) :
    (network D bits).Half v :=
  (fun e h ↦ z.1 (.inl e) h, fun e h ↦ z.2 (.inl e) h)

/-- Evaluate each original tensor on the two genuine incoming and outgoing slots. -/
def paddedFactors {k : Type*} (p : ℕ) (F : Factors k (network D bits)) :
    Factors k (paddedNetwork D p bits) :=
  fun v z ↦ F v (unpadHalf p v z)

/-- Deleting the singleton fields is a bijection on shared-edge assignments. -/
def unpadFields (p : ℕ) :
    ((e : (paddedNetwork D p bits).Edge) → (paddedNetwork D p bits).Payload e) ≃
      ((e : (network D bits).Edge) → (network D bits).Payload e) where
  toFun z e := z (.inl e)
  invFun z
    | .inl e => z e
    | .inr _ => ()
  left_inv z := by funext e; cases e <;> rfl
  right_inv _ := rfl

open scoped Classical in
/-- Padding preserves the contraction for arbitrary factors on the original network. -/
theorem contract_padded {k : Type*} [CommSemiring k] (p : ℕ) (F : Factors k (network D bits)) :
    contract (paddedNetwork D p bits) (paddedFactors p F) = contract (network D bits) F := by
  rw [contract_edgeSum, contract_edgeSum]
  exact Fintype.sum_equiv (unpadFields p) _ _ fun _ ↦ rfl

/-- The first two slot numbers are the stay and flip arcs; padding follows them. -/
def paddingSlots (p : ℕ) : Bool ⊕ Fin p ≃ Fin (2 + p) :=
  (finTwoEquiv.symm.sumCongr (Equiv.refl _)).trans finSumFinEquiv

/-- Only the original flip arc changes the current address bit. -/
def slotSide {p : ℕ} (i : Fin (2 + p)) : Bool :=
  ((paddingSlots p).symm i).elim id (fun _ ↦ false)

@[simp] theorem slotSide_real (p : ℕ) (b : Bool) :
    slotSide (paddingSlots p (.inl b)) = b := by simp [slotSide]

@[simp] theorem slotSide_pad (u : Fin p) :
    slotSide (paddingSlots p (.inr u)) = false := by simp [slotSide]

/-- Number each physical edge by its source position and outgoing slot. -/
def paddedEdgeEquiv (D p : ℕ) : PaddedArc D p ≃ Position D × Fin (2 + p) where
  toFun
    | .inl (j, x, b) => ((j, x), paddingSlots p (.inl b))
    | .inr (v, i) => (v, paddingSlots p (.inr i))
  invFun vi := match (paddingSlots p).symm vi.2 with
    | .inl b => .inl (vi.1.1, vi.1.2, b)
    | .inr i => .inr (vi.1, i)
  left_inv e := by rcases e with ⟨j,x,b⟩ | ⟨v,i⟩ <;> simp
  right_inv vi := by
    rcases vi with ⟨⟨j,x⟩, i⟩
    obtain ⟨b | i, rfl⟩ := (paddingSlots p).surjective i <;> simp

private theorem rotate_ne_self (hD : 1 < D) (j : Fin D) : finRotate D j ≠ j := by
  have : NeZero D := ⟨by omega⟩
  rw [finRotate_apply]
  intro h
  have hz : (1 : Fin D) = 0 := add_left_cancel (a := j) (show j + 1 = j + 0 by simpa using h)
  have := congrArg Fin.val hz
  simp [Nat.mod_eq_of_lt hD] at this

/-- The slot permutation advances the cursor and preserves the slot number.
Thus incoming copies and outgoing copies are independently numbered at every site. -/
def paddedSlotGraph (D p : ℕ) (hD : 1 < D) : Compression.SlotGraph (Position D) (2 + p) where
  target :=
    { toFun := fun vi ↦ (head (vi.1.1, vi.1.2, slotSide vi.2), vi.2)
      invFun := fun vi ↦
        let e := incomingArc vi.1 (slotSide vi.2)
        ((e.1, e.2.1), vi.2)
      left_inv := by
        rintro ⟨⟨j,x⟩,i⟩
        have : NeZero D := ⟨by omega⟩
        have he := incomingArc_head (j,x,slotSide i)
        exact congrArg (fun e : Arc D ↦ ((e.1,e.2.1), i)) he
      right_inv := by
        rintro ⟨v,i⟩
        have : NeZero D := ⟨by omega⟩
        exact congrArg (fun u : Position D ↦ (u,i)) (head_incomingArc v (slotSide i)) }
  ends_ne := fun vi he ↦ rotate_ne_self hD vi.1.1 (congrArg Prod.fst he)

@[simp] theorem paddedSlotGraph_target (hD : 1 < D) (v : Position D) (i : Fin (2 + p)) :
    (paddedSlotGraph D p hD).target (v, i) = (head (v.1, v.2, slotSide i), i) := rfl

/-- The source endpoint of a numbered edge is its outgoing position. -/
theorem paddedEdge_source (bits : S → ℕ) (e : PaddedArc D p) :
    (paddedNetwork D p bits).src e = (paddedEdgeEquiv D p e).1 := by
  rcases e with ⟨j,x,b⟩ | ⟨v,i⟩ <;> rfl

/-- The target permutation gives the incoming position of every edge, retaining
the slot number even for parallel copies. -/
theorem paddedEdge_target (hD : 1 < D) (bits : S → ℕ) (e : PaddedArc D p) :
    (paddedSlotGraph D p hD).target (paddedEdgeEquiv D p e) =
      ((paddedNetwork D p bits).dst e, (paddedEdgeEquiv D p e).2) := by
  rcases e with ⟨j,x,b⟩ | ⟨v,i⟩ <;> simp [paddedEdgeEquiv, paddedNetwork]

end CursorNetwork

end VPVNP
end Computability
end OAI
