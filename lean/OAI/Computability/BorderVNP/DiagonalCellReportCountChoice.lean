import OAI.Computability.BorderVNP.DiagonalTallyReportBitsRead
import OAI.Computability.BorderVNP.DiagonalTallyReportChoices
import OAI.Computability.BorderVNP.CellGuardedObservations

/-! # The unique native little-endian count spelling in each physical report -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyCellReports

open CellSparse VPVNP.TapeWord VPVNP.BurstRAM
open private count_bits use_bits from OAI.Computability.BorderVNP.DiagonalTallyReportBitsRead
open private word_eq_value from OAI.Computability.BorderVNP.DiagonalTallyCountChecked
open scoped Classical

private theorem bank_words (pre tail : List Bool) :
    literalBitsAt (fun i => (lookup (pre++tail) i).toNat) pre.length tail := by
  intro i
  have hi : i.val < tail.length := by simpa using i.isLt
  simp [lookup,List.head?_drop,hi]

/-- Actual bit-bank readback of the supplemental count and use choices,
separating the RAM array address from the index in the private assignment. -/
theorem ReportCell.bankRead {l : ReportLayout} (c : ReportCell l) (pre : List Bool) :
    (∀ g j, lookup (pre++c.bits) (pre.length+g.val*l.countWidth+j.val) = c.counts g j) ∧
      useBitsAt (fun i => (lookup (pre++c.bits) i).toNat) (pre.length+l.gadgets*l.countWidth) c.bundles := by
  let m := fun i => (lookup (pre++c.bits) i).toNat
  have hh : literalBitsAt m pre.length c.bits := bank_words pre c.bits
  rw [literalBitsAt,ReportCell.bits,List.map_append] at hh
  refine ⟨fun g j => ?_,use_bits m _ _ ?_⟩
  · have b := count_bits m pre.length c.counts hh.left g j
    change (lookup (pre++c.bits) (pre.length+g.val*l.countWidth+j.val)).toNat = (c.counts g j).toNat at b
    cases hv : lookup (pre++c.bits) (pre.length+g.val*l.countWidth+j.val) <;>
      cases hf : c.counts g j <;> simp [hv,hf] at b ⊢
  · simpa [literalBitsAt,List.length_flatten,List.map_ofFn,Function.comp_def,List.ofFn_const] using hh.right

/-- The unique count spelling for every ID, including IDs occurring zero times. -/
noncomputable def observationCounts (obs : List (Bool × Option ℕ)) (g d : ℕ) : Fin g → Fin d → Bool :=
  fun i => VPVNP.RAMSerialization.wordBits d ⟨(obs.filterMap Prod.snd).count i.val % 2^d,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

private theorem count_value (obs : List (Bool × Option ℕ)) (g d : ℕ)
    (hfit : ∀ i : Fin g, (obs.filterMap Prod.snd).count i.val < 2^d) (i : Fin g) :
    value (List.ofFn (observationCounts obs g d i)) = (obs.filterMap Prod.snd).count i.val :=
  (value_wordBits ⟨_,Nat.mod_lt _ (Nat.two_pow_pos _)⟩).trans (Nat.mod_eq_of_lt (hfit i))

/-- At a fixed local observation the actual native count check passes exactly
on its canonical finite-width spelling. Range-checking includes zero-valued
gadget rows. -/
theorem ReportCell.checkedCounts {l : ReportLayout} (c : ReportCell l) (pre : List Bool)
    (obs : List (Bool × Option ℕ)) (range : ∀ i ∈ obs.filterMap Prod.snd, i < l.gadgets)
    (fit : ∀ i : Fin l.gadgets, (obs.filterMap Prod.snd).count i.val < 2^l.countWidth) :
    countsValid (lookup (pre++c.bits)) (countFields pre.length l.gadgets l.countWidth) obs ↔
      c.counts = observationCounts obs l.gadgets l.countWidth := by
  let fields := countFields pre.length l.gadgets l.countWidth
  have hlen : fields.length = l.gadgets := countFields_length ..
  have hd (i : Fin fields.length) : word (lookup (pre++c.bits)) fields[i] =
      value (List.ofFn (c.counts (Fin.cast hlen i))) := by
    have r : fields[i] = List.ofFn (fun j : Fin l.countWidth => pre.length+i.val*l.countWidth+j.val) := by
      change (List.ofFn (fun k : Fin l.gadgets => List.ofFn (fun j : Fin l.countWidth =>
        pre.length+k.val*l.countWidth+j.val)))[i.val] = _
      rw [List.getElem_ofFn]
    rw [r,word_eq_value,List.map_ofFn]
    exact congrArg value (congrArg List.ofFn (funext fun j => (c.bankRead pre).1 (Fin.cast hlen i) j))
  constructor
  · intro h
    funext i
    apply countBits_unique
    rw [count_value _ _ _ fit i]
    let z := Fin.cast hlen.symm i
    have eq := (hd z).symm.trans (h.2 z).symm
    have cast : Fin.cast hlen z = i := Fin.ext rfl
    rw [cast] at eq
    exact eq
  · intro h
    refine ⟨fun i hi => (range i hi).trans_eq hlen.symm,fun z => ?_⟩
    rw [hd z,h,count_value _ _ _ fit]
    rfl

end DiagonalTallyCellReports

end BorderVNP
end Computability
end OAI
