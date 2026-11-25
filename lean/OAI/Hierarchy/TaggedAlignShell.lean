import OAI.Hierarchy.TaggedOracleCut
import OAI.Hierarchy.TaggedRadixSort

namespace OAI
/-! # The two-terminal tagged alignment shell

All guessed tags are shared between the tagged transport and the linear row
checks. The transport's payload bits connect directly to the two endpoints.
-/

namespace Hierarchy.Tagged.AlignShell
open ThreeFlat Routing SortNetwork
open scoped BigOperators Classical
noncomputable section

abbrev Data (h w : ℕ) := Fin (Fintype.card (Payload h w))
abbrev Ends (h w : ℕ) := Data h w ⊕ Data h w
abbrev CheckPins (h w : ℕ) := Payload h w ⊕ Payload h h
abbrev Src (h w : ℕ) := BitSource (Fintype.card (Payload h h)) (Fintype.card (Ends h w))

private def sourceBit {h w : ℕ} (where_ : Bool) (i : Row h) (j : Fin w) : Src h w :=
  .pin (Fintype.equivFin _ ((if where_ then Sum.inr else Sum.inl) (Fintype.equivFin _ (i,j))))
private def guess {h w : ℕ} (i : Row h) (j : Fin h) : Src h w := .hidden (Fintype.equivFin _ (i,j))
private def checkWire {h w : ℕ} : CheckPins h w → Src h w
  | .inl (i,j) => sourceBit false i j
  | .inr (i,j) => guess i j
private def holeWire {h w : ℕ} : Port h w → Src h w
  | .inl (i,j) => sourceBit true (Radix.routeRow h i) j
  | .inr (.inl (i,j)) => guess i j
  | .inr (.inr (i,j)) => sourceBit false i j

def shell {F : Type*} [Zero F] [One F] {h w : ℕ}
    (W : BitNetwork F (Fintype.card (CheckPins h w))) :
    BitNetwork F (Fintype.card (Ends h w ⊕ Fin (pins h w))) :=
  OracleCut.network (fun _ : Unit => W) (fun _ i => checkWire ((Fintype.equivFin _).symm i))
    (fun j => holeWire ((portIndex h w).symm j))

def tagBits (h : ℕ) : (Row h → Row h) ≃ (Data h h → Bool) :=
  (((Equiv.refl _).arrowCongr (addressEquiv h).symm).trans (Equiv.curry _ _ _).symm).trans
    ((Fintype.equivFin _).arrowCongr (Equiv.refl _))

private theorem untag {h : ℕ} (g : Row h → Row h) (i : Row h) (j : Fin h) :
    tagBits h g (Fintype.equivFin _ (i,j)) = (addressEquiv h).symm (g i) j := by
  simp [tagBits, Equiv.arrowCongr, Equiv.curry]

private def switched {h w : ℕ} (input output : Records h w) (g : Row h → Row h) : SwitchPin h w → Bool
  | .inl (i,j) => (addressEquiv h).symm (g i) j
  | .inr (false,i,j) => input i j
  | .inr (true,i,j) => output i j

/-- The contracted rows multiply the chosen address checks by exactly one
ordinary tagged-permutation tensor. -/
theorem eval {F : Type*} [CommSemiring F] {h w : ℕ} (W : BitNetwork F (Fintype.card (CheckPins h w)))
    (input output : Records h w) :
    (∑ hole : Fin (pins h w) → Bool,
      TypedWiring.value (shell W) (Sum.elim (Sum.elim (pack input) (pack output)) hole) * coeff F h w hole) =
    ∑ g : Row h → Row h, TypedWiring.value W (Sum.elim (Function.uncurry input)
        (fun (i,j) => (addressEquiv h).symm (g i) j)) * taggedSwitch F g input output := by
  rw [shell, OracleCut.contract, ← (tagBits h).sum_comp]
  apply Finset.sum_congr rfl
  intro g _
  simp only [Fintype.prod_unique]
  have check (i : CheckPins h w) : (checkWire i).read (tagBits h g)
      (Sum.elim (pack input) (pack output) ∘ (Fintype.equivFin _).symm) =
      Sum.elim (Function.uncurry input) (fun (i,j) => (addressEquiv h).symm (g i) j) i := by
    rcases i with ⟨i,j⟩ | ⟨i,j⟩ <;> simp [checkWire, sourceBit, guess, untag, BitSource.read, pack]
  have exposed (i : Port h w) : (holeWire i).read (tagBits h g)
      (Sum.elim (pack input) (pack output) ∘ (Fintype.equivFin _).symm) =
      switched input output g (Radix.switchPort i) := by
    rcases i with ⟨i,j⟩ | (⟨i,j⟩ | ⟨i,j⟩) <;> simp [holeWire, sourceBit, guess, untag,
      BitSource.read, pack, switched, Radix.switchPort, SwitchPin.output, SwitchPin.input, SwitchPin.tag]
  simp_rw [check, exposed]
  rw [Radix.coeff_switch]
  simp only [SwitchPin.input, SwitchPin.output, SwitchPin.tag, switched, Equiv.apply_symm_apply]
  rfl

theorem size {F : Type*} [Zero F] [One F] {h w : ℕ} (W : BitNetwork F (Fintype.card (CheckPins h w))) :
    (shell W).cells+(shell W).internal = W.cells+W.internal+2^h*h+28*pins h w := by
  rw [shell, OracleCut.size]
  simp [Payload]

end
end Hierarchy.Tagged.AlignShell

end OAI
