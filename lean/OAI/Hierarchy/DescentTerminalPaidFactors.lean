import OAI.Hierarchy.DescentTerminalPaidMask
import OAI.Hierarchy.DescentTerminalPackedHost

namespace OAI
/-! # Paid terminal padding and frequency-selected field coefficients on a single graph -/

namespace Hierarchy.DescentTerminalPaidFactors
open ThreeFlat ThreeFlat.Routing
open CatalystSubstitution DescentTerminalPorts Computability.BorderVNP.Crossing ProtocolStackContraction
open scoped Classical BigOperators
noncomputable section

variable {F : Type} [Field F] {rows word W bins : ℕ}

abbrev Pin (rows word bins W : ℕ) := DescentTerminalPaidMask.Pin rows word ⊕ (Fin bins×Fin W)

private def scalarPin : DescentTerminalLocalFactors.Pin Empty bins W→Pin rows word bins W
  | .inl (_,e)=>nomatch e
  | .inr q=>.inr q

def factors (F : Type) [Field F] (rows word W : ℕ) (scalar : Fin bins→F) :
    BitNetwork F (Fintype.card (Pin rows word bins W)) :=
  plugPair (A:=DescentTerminalPaidMask.Pin rows word) (B:=DescentTerminalLocalFactors.Pin Empty bins W)
    (Y:=Pin rows word bins W) (H:=Empty) (DescentTerminalPaidMask.network F rows word)
    (DescentTerminalLocalFactors.network F Empty W scalar) (fun x=>.inl (.inl x)) (fun x=>.inl (scalarPin x))

def factorPins (cut : Fin rows→ℕ) (pay : RowBit rows word→Bool) (digit : Fin bins×Fin W→Bool) :
    Pin rows word bins W→Bool := Sum.elim (DescentTerminalPaidMask.pins cut pay) digit

theorem factors_size (F : Type) [Field F] (rows word W : ℕ) (scalar : Fin bins→F) (hw : 0<word) :
    (factors F rows word W scalar).cells+(factors F rows word W scalar).internal≤9*(rows*word)+bins*W := by
  have cap:=DescentTerminalPaidMask.network_size F rows word hw
  rw [factors,plugPair_cells,plugPair_internal,DescentTerminalLocalFactors.network_cells,
    DescentTerminalLocalFactors.network_internal,Fintype.card_empty]
  omega

theorem factors_read (scalar : Fin bins→F) (cut : Fin rows→ℕ) (pay : RowBit rows word→Bool)
    (digit : Fin bins×Fin W→Bool) (fits : ∀i,cut i≤word) :
    TypedWiring.value (factors F rows word W scalar) (factorPins cut pay digit)=
      if ∀x : RowBit rows word,cut x.1≤x.2.val→pay x=false then
        ∏b : Fin bins,∏ z : Fin W,if digit (b,z) then scalar b^(2^z.val) else 1 else 0 := by
  rw [factors,plugPair_value,Fintype.sum_unique]
  change TypedWiring.value (DescentTerminalPaidMask.network F rows word) (DescentTerminalPaidMask.pins cut pay) *
    TypedWiring.value (DescentTerminalLocalFactors.network F Empty W scalar)
      (factorPins cut pay digit ∘ scalarPin)=_
  have e : factorPins cut pay digit ∘ scalarPin=
      DescentTerminalLocalFactors.pins (fun t : Empty=>t.elim) (fun t : Empty=>t.elim) digit := by
    funext p
    rcases p with ⟨b,t⟩|t
    · exact t.elim
    · rfl
  rw [DescentTerminalPaidMask.network_value _ _ _ fits,e,DescentTerminalLocalFactors.network_value]
  simp only [IsEmpty.forall_iff,ite_true]
  split <;> simp

variable {D : ℕ} {P : Type} {bits : P→ℕ} (N : Network D P bits)

theorem factors_value (scalar : Fin bins→F) (code : N.Edge ↪ ℕ) (room : (∑e,N.width e)≤rows*word)
    (pay : RowBit rows word→Bool) {t : ℕ} (query : Fin t→Fin bins) (fit : t<2^W) :
    TypedWiring.value (factors F rows word W scalar)
      (factorPins (fun i=>DescentTerminalDenseMask.valid word (∑e,N.width e) i.val)
        pay (DescentTerminalHost.countDigit query)) =
      if ZeroUnused N (denseBits N code room) pay then ∏i : Fin t,scalar (query i) else 0 := by
  rw [factors_read (W:=W) scalar
    (fun i : Fin rows => DescentTerminalDenseMask.valid word (∑e,N.width e) i.val)
    pay (DescentTerminalHost.countDigit query) (fun _=>min_le_left ..)]
  apply if_congr _ _ rfl
  · rw [←mask_ok N (denseBits N code room) pay]
    refine forall_congr' fun x=>?_
    rw [DescentTerminalDenseMask.mask_read,decide_eq_true_eq]
  · convert (table_histogram_bits query scalar W (by simpa using fit)).symm using 1
    apply Finset.prod_congr rfl
    intro b _
    apply Finset.prod_congr rfl
    intro j _
    exact congrArg (fun s : Finset (Fin t) =>
      if s.card.testBit j.val then scalar b^(2^j.val) else 1)
      (@Finset.filter_congr_decidable _ Finset.univ (fun i => query i=b)
        (fun _ => inferInstance) (fun _ => Classical.propDecidable _))

end
end Hierarchy.DescentTerminalPaidFactors

end OAI
