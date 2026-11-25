import OAI.Computability.BorderVNP.CubePhysicalOperandLedger
import OAI.Computability.BorderVNP.PackedBankBoxTags

/-! # Constructing a routed cell readout from its actual original site directories

A stable physical site order fixes the prefix used to relocate each local box ordinal.
The selected merged box is the same original table and therefore the same observation
at every copy. The resulting CellRead supplies the exact reported count operand used
by the native tally program.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeLedger

open CellSparse
variable {Site : Type*} {count U : ℕ}

/-- Offset of a site's first box in the stable merged list of all original tables. -/
def boxOffset (order : Fin count ≃ Site) (source : Site → Directory) (v : Site) : ℕ :=
  (((List.ofFn order).take (order.symm v).val).flatMap fun j => (source j).boxes).length

private theorem split_site (order : Fin count ≃ Site) (v : Site) :
    List.ofFn order = (List.ofFn order).take (order.symm v).val ++ v ::
      (List.ofFn order).drop ((order.symm v).val+1) := by
  let i := order.symm v
  have hi : i.val < (List.ofFn order).length := by rw [List.length_ofFn]; exact i.isLt
  calc
    _ = (List.ofFn order).take i.val ++ (List.ofFn order).drop i.val := (List.take_append_drop ..).symm
    _ = _ := by rw [List.drop_eq_getElem_cons hi,List.getElem_ofFn]; simp [i]

/-- Reading a relocated local box ordinal in the physical merged table gives the
source site's original factors, at their original address within the site's box list. -/
theorem boxOffset_lookup (order : Fin count ≃ Site) (source : Site → Directory) (v : Site)
    (k : ℕ) (hk : k < (source v).boxes.length) :
    ((List.ofFn order).flatMap fun j => (source j).boxes).getD (boxOffset order source v+k) [] =
      (source v).boxes.getD k [] := by
  let before := ((List.ofFn order).take (order.symm v).val).flatMap fun j => (source j).boxes
  let after := ((List.ofFn order).drop ((order.symm v).val+1)).flatMap fun j => (source j).boxes
  have eq : (List.ofFn order).flatMap (fun j => (source j).boxes) = before ++ (source v).boxes ++ after := by
    conv_lhs => rw [split_site order v,List.flatMap_append,List.flatMap_cons]
    exact List.append_assoc .. |>.symm
  change ((List.ofFn order).flatMap fun j => (source j).boxes).getD (before.length+k) [] = _
  rw [eq,List.append_assoc,List.getD_append_right _ _ _ _ (Nat.le_add_right ..),
    Nat.add_sub_cancel_left,List.getD_append _ _ _ _ hk]

/-- Merge the per-site source tables and rows with all ordinal relocations calculated
from their actual order. The reported count words occur only once per whole cell. -/
def mergedReadDirectory (order : Fin count ≃ Site) (source : Site → Directory)
    (reports : Fin U → List ℕ) : Directory :=
  Directory.mergeSites (List.ofFn order) (fun j => (source j).boxes)
    (fun j => (source j).records.map (Record.rebaseBox (boxOffset order source j))) (List.ofFn reports)

/-- Original site readbacks construct the complete physical cell readout directly.
There is no assumed merged count or assumed equality of local versus merged box IDs. -/
def CellRead.ofMerged (order : Fin count ≃ Site) (source : Site → Directory)
    (reports : Fin U → List ℕ) (bank : ℕ → Bool) (observed : Site → List (Bool × Option ℕ))
    (localFit : ∀ v, ∀ r ∈ (source v).records, r.BoxRefFits (source v).boxes.length)
    (reads : ∀ v, (source v).observations bank = some (observed v))
    (passing : (mergedReadDirectory order source reports).weight bank ≠ 0)
    (zeroAddr : ℕ) (references : Fin U → ℕ) : CellRead Site U where
  count := count
  order := order
  directory := mergedReadDirectory order source reports
  bank := bank
  reportLength := List.length_ofFn
  observed := observed
  reads := Directory.mergeSites_observations (List.ofFn order) source (boxOffset order source)
    (List.ofFn reports) bank observed (fun v _ => localFit v)
    (fun v _ => boxOffset_lookup order source v) (fun v _ => reads v)
  pass := passing
  zeroAddr := zeroAddr
  references := references

/-- If the original site's factor consists of the paid-site reads, their physical
gadget frequencies coincide with its complete tagged product for every numbered ID. -/
theorem paid_readback {Param : Type*} {m : ℕ} (selected : Fin m → Fin U) (g : Fin U) :
    ((List.ofFn fun i => (false,some (selected i).val)).filterMap Prod.snd).count g.val =
      (Diagonal.CellEntries.counters (∏ i, Diagonal.CellEntries.gadget (Param := Param) (selected i))).2 g :=
  Packing.PaidPhysical.observed_count selected ⟨Fin.val,Fin.val_injective⟩ g

/-- For a successful merged call, the integer sign is the product of the physical
site signs. In particular the positive checks and scalar-position reads of the tagged
grid and paid sites leave the passing assignment weight equal to one. -/
theorem CellRead.weight_one {Site : Type*} {U : ℕ} (c : CellRead Site U)
    (positive : ∀ v, ((c.observed v).map Prod.fst).foldl Bool.xor false = false) :
    c.directory.weight c.bank = 1 := by
  have merged (sites : List Site) : ((sites.flatMap c.observed).map Prod.fst).foldl Bool.xor false = false := by
    induction sites with
    | nil => rfl
    | cons v vs ih => simp [List.flatMap_cons,positive,ih]
  have nonzero := c.pass
  unfold Directory.weight at nonzero ⊢
  rw [c.reads] at nonzero ⊢
  simp only [merged, Bool.false_eq_true, ite_false] at nonzero ⊢
  split <;> simp_all

end Cube.Physical.NativeLedger

end BorderVNP
end Computability
end OAI
