import OAI.Hierarchy.TaggedBlockRecords
import OAI.Hierarchy.TaggedOracleCut
import OAI.Hierarchy.TaggedRadixSort

namespace OAI
/-! # Two-terminal stable sorting with an exposed tag factor

The shell exposes both arrays and the tag occurrence. Its internal cells are
the adjacent lexicographic checks and one equality per output and oracle pin.
-/

namespace Hierarchy.Tagged.SortRelation

open ThreeFlat Routing SortNetwork Tagged.Radix
open scoped BigOperators Classical
noncomputable section

abbrev Ends (h w : ℕ) := Data h w ⊕ Data h w
abbrev Sites (h w : ℕ) := Edge h ⊕ Data h w

def lift {z h w : ℕ} (s : BitSource z (Fintype.card (Payload h w))) :
    BitSource z (Fintype.card (Ends h w)) :=
  match s with
  | .hidden i => .hidden i
  | .constant b => .constant b
  | .pin i => .pin (Fintype.equivFin _ (.inl i))

theorem lift_read {z h w : ℕ} (s : BitSource z (Fintype.card (Payload h w)))
    (a : Fin z → Bool) (x y : Data h w → Bool) :
    (lift s).read a (Sum.elim x y ∘ (Fintype.equivFin _).symm) = s.read a x := by
  cases s <;> simp [lift, BitSource.read]

abbrev ports {h w : ℕ} (d : ℕ) : Sites h w → ℕ := Sum.elim (fun _ => (h+d)+(h+d)) (fun _ => 2)

def modules (F : Type*) [Zero F] [One F] {h w : ℕ} (d : ℕ) :
    (i : Sites h w) → BitNetwork F (ports d i)
  | .inl _ => compareBits F (h+d)
  | .inr _ => TableCompiler.localTableNetwork fun (v : Fin 2 → Bool) => if v 0 = v 1 then (1:F) else 0

def siteWire {h w d : ℕ} (digit : Fin d → Fin w) :
    (i : Sites h w) → Fin (ports d i) → BitSource (Fintype.card (Hidden h w)) (Fintype.card (Ends h w))
  | .inl i, j => lift (wires digit (some (some i)) j)
  | .inr i, j => if j.val = 0 then lift (wires digit (some none) i) else .pin (Fintype.equivFin _ (.inr i))

def shell (F : Type*) [Zero F] [One F] {h w d : ℕ} (digit : Fin d → Fin w) :
    BitNetwork F (Fintype.card (Ends h w ⊕ Fin (pins h (h+w)))) :=
  OracleCut.network (modules F d) (siteWire digit) (fun j => lift (wires digit none (switchIndex h (h+w) j)))

/-- All comparator words and all exposed boundary ports are charged. -/
theorem size (F : Type*) [Zero F] [One F] {h w d : ℕ} (digit : Fin d → Fin w) :
    (shell (h := h) F digit).cells+(shell (h := h) F digit).internal ≤
      2^h*((h+h+w)+(h+d+1)+(h+d+2)*176+28*w) + 28*pins h (h+w) := by
  have e : Fintype.card (Edge h) ≤ 2^h := by
    simpa using Fintype.card_subtype_le (fun i : Fin (2^h) => i.val+1 < 2^h)
  let table := fun v : Fin 2 → Bool => if v 0 = v 1 then (1:F) else 0
  have outCells (i : Data h w) : ((modules (h := h) (w := w) F d) (.inr i)).cells = 16 :=
    TableCompiler.localTableNetwork_cells table
  have outHidden (i : Data h w) : ((modules (h := h) (w := w) F d) (.inr i)).internal = 12 :=
    TableCompiler.localTableNetwork_internal table
  have siteCells (i : Sites h w) : (modules F d i).cells =
      Sum.elim (fun _ => (h+d+2)*96) (fun _ => 16) i := by
    cases i with
    | inl e => exact compareBits_cells F (h+d)
    | inr u => exact outCells u
  have siteHidden (i : Sites h w) : (modules F d i).internal =
      Sum.elim (fun _ => (h+d+1)+(h+d+2)*80) (fun _ => 12) i := by
    cases i with
    | inl e => exact compareBits_internal F (h+d)
    | inr u => exact outHidden u
  rw [shell, OracleCut.size]
  simp_rw [siteCells,siteHidden]
  simp only [Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Hidden, Payload, Data, Fintype.card_fin,
    Fintype.card_sum, Fintype.card_prod, Nat.cast_id]
  calc
    _ ≤ 2^h*((h+d+2)*96) + _ + (2^h*((h+d+1)+(h+d+2)*80)+_) + _ + _ := by gcongr
    _ = _ := by ring

end
end Hierarchy.Tagged.SortRelation

end OAI
