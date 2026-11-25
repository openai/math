import OAI.Hierarchy.TaggedShorterHistoryScan
import OAI.Hierarchy.TaggedShorterControlSort
import OAI.Hierarchy.TaggedRadixPins

namespace OAI
/-! # The single opened tagged sort used by the physical RAM read audit -/

noncomputable section
namespace Hierarchy.TaggedShorterHistoryOrder
open ThreeFlat Routing Diagonal TraceAdjacent
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open Tagged
open scoped Classical BigOperators

variable {F : Type*} [CommRing F] {w m a : ℕ}

abbrev ArrayPins (m w : ℕ) := SortNetwork.Payload m (RecordWidth w)
abbrev CutPins (m w a : ℕ) := ArrayPins m w ⊕ ControlSort.Hole m a
private def scanWire (hw : 2≤w) (t : ScanPins m w) : ArrayPins m w ⊕ Bool :=
  Fin.cases (.inr (bits hw none t.2)) (fun i => .inl (i,t.2)) t.1

def predecessor (hw : 2≤w) : BitNetwork F (Fintype.card (ArrayPins m w)) :=
  RadixStage.pullPins (scan F m w) (scanWire hw)

theorem predecessor_eval (hw : 2≤w) (slots : Fin (2^m) → Option (WordRecord w)) :
    TypedWiring.value (predecessor (F:=F) hw) (Function.uncurry (bits hw ∘ slots)) =
      if PaddedCheck none (List.ofFn fun i => (slots i).map WordRecord.record) then 1 else 0 := by
  rw [predecessor,RadixStage.pullPins_value]
  calc
    _ = TypedWiring.value (scan F m w) (scanInput hw slots) := by
      apply congrArg (TypedWiring.value (scan F m w))
      funext ⟨i,j⟩
      induction i using Fin.cases <;> rfl
    _ = _ := scan_eval hw slots

private def Port (m w a : ℕ) : Bool → Type
  | false => ControlSort.Pin m (RecordWidth w) a
  | true => ArrayPins m w
private instance (b : Bool) : Fintype (Port m w a b) := by
  cases b
  · exact inferInstanceAs (Fintype (ControlSort.Pin m (RecordWidth w) a))
  · exact inferInstanceAs (Fintype (ArrayPins m w))
private def part (hw : 2≤w) : (b : Bool) → BitNetwork F (Fintype.card (Port m w a b))
  | false => ControlSort.cut F a id
  | true => predecessor hw
private def tap : (b : Bool) → Port m w a b → CutPins m w a ⊕ ArrayPins m w
  | false,.inl (.inl i) => .inl (.inl i)
  | false,.inl (.inr i) => .inr i
  | false,.inr i => .inl (.inr i)
  | true,i => .inr i

def audit (hw : 2≤w) : BitNetwork F (Fintype.card (CutPins m w a)) :=
  TypedWiring.glue (part hw) tap

theorem audit_eval (hw : 2≤w) (x : ArrayPins m w → Bool) (z : ControlSort.Hole m a → Bool) :
    TypedWiring.value (audit (F:=F) hw) (Sum.elim x z) = ∑ y : ArrayPins m w → Bool,
      TypedWiring.value (ControlSort.cut F a (id : Fin (RecordWidth w) → _)) (Sum.elim (Sum.elim x y) z) *
      TypedWiring.value (predecessor hw) y := by
  rw [audit,TypedWiring.glue_value]
  apply Finset.sum_congr (congrArg (@Finset.univ (ArrayPins m w → Bool)) (Subsingleton.elim _ _))
  intro y _
  rw [Fintype.prod_bool,mul_comm]
  apply congrArg₂ (·*·)
  · apply congrArg (TypedWiring.value (ControlSort.cut F a id))
    funext p; rcases p with (p|p)|p <;> rfl
  · rfl

/-- After the single product-hole contraction, only the unique stable output
array is charged to the predecessor scan. Its pins are all internal. -/
theorem contract (hw : 2≤w) (positive : 0<a) (room : RecordWidth w ≤ a*m) (x : ArrayPins m w → Bool) :
    (∑ z : ControlSort.Hole m a → Bool, TypedWiring.value (audit (F:=F) hw) (Sum.elim x z) *
      ∏ u : Fin a, Tagged.coeff F m m (fun j => z (u,j))) =
      TypedWiring.value (predecessor hw) (SortNetwork.sortedPins id x) := by
  simp_rw [audit_eval,Finset.sum_mul]
  rw [Finset.sum_comm]
  have reorder (y : ArrayPins m w → Bool) :
      (∑ z : ControlSort.Hole m a → Bool, TypedWiring.value (ControlSort.cut F a id) (Sum.elim (Sum.elim x y) z) *
        TypedWiring.value (predecessor hw) y * ∏ u : Fin a, Tagged.coeff F m m (fun j => z (u,j))) =
        (if SortNetwork.sortedPins id x = y then 1 else 0) * TypedWiring.value (predecessor hw) y := by
    rw [←ControlSort.contract (F:=F) positive room id x y,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    ac_rfl
  simp_rw [reorder]
  simp [ite_mul]

theorem checks (hw : 2≤w) (positive : 0<a) (room : RecordWidth w ≤ a*m)
    (S : ℕ) (header : ℕ → Word w) (es : List (Event w)) (fits : S+es.length≤2^m)
    (slots : Fin (2^m) → Option (WordRecord w))
    (chron : ∀ i, TraceSlots.toOrdered (slots i)=TraceRecordSort.inputWire S m header es i) :
    (∑ z : ControlSort.Hole m a → Bool,
      TypedWiring.value (audit (F:=F) hw) (Sum.elim (Function.uncurry (bits hw ∘ slots)) z) *
        ∏ u : Fin a, Tagged.coeff F m m (fun j => z (u,j))) =
      if Correct (initialMemory S header) es then 1 else 0 := by
  let ordered := fun i => slots (permutation hw slots i)
  calc
    _ = TypedWiring.value (predecessor hw)
        (SortNetwork.sortedPins id (Function.uncurry (bits hw ∘ slots))) := contract hw positive room _
    _ = TypedWiring.value (predecessor hw) (Function.uncurry (bits hw ∘ ordered)) :=
      congrArg (TypedWiring.value (predecessor (F:=F) hw)) (sort_pins hw slots)
    _ = (if PaddedCheck none (List.ofFn fun i => (ordered i).map WordRecord.record) then 1 else 0) :=
      predecessor_eval hw ordered
    _ = _ := by
      by_cases valid : Correct (initialMemory S header) es
      · have accepted : PaddedCheck none (List.ofFn fun i => (ordered i).map WordRecord.record) :=
          (scan_iff_correct hw S header es fits slots chron).mpr valid
        rw [ite_eq_left accepted,ite_eq_left valid]
      · have rejected : ¬ PaddedCheck none (List.ofFn fun i => (ordered i).map WordRecord.record) :=
          fun h => valid ((scan_iff_correct hw S header es fits slots chron).mp h)
        rw [ite_eq_right rejected,ite_eq_right valid]

end Hierarchy.TaggedShorterHistoryOrder

end
end OAI
