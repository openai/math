import OAI.Computability.BorderVNP.CubeGroupRawExact
import OAI.Computability.BorderVNP.CubePhysicalGroupLoad
import OAI.Computability.BorderVNP.CubeGroupWeightLayout
import OAI.Computability.BorderVNP.CubeISAOwnedPacketCount
import OAI.Computability.BorderVNP.CubeISALengthImage

/-! # Physical meaning of the native group-weight histogram

The native pass reads the crossing and selector lengths of every incident shared
list. A packed cell contributes its incoming data to its grouping symbol. The
raw term counts all original padded wires in packets and singletons meeting that
symbol, including the wires pinned to zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Physical RoutingISA.CubeLengths Finset

variable {l : Layout} {mem : ℕ → ℕ} {n blocks K h : ℕ}

/-- Public dimensions and table contents consumed by the three weight scans. -/
structure PhysicalImage (l : Layout) (mem : ℕ → ℕ) (blocks b K h : ℕ)
    (D : LengthDeclaration n l.groups) (label : Fin l.cells → Label (n+1) l.groups)
    {A : Type*} [Fintype A] (recv : A → Fin l.cells) (w : A → ℕ) : Prop where
  /-- Number of cube coordinates and the ordinal selected in the declaration. -/
  axes : l.axes = n+1
  axis : l.axis = D.1.val
  /-- The same crossing table as the physical length checks. -/
  rows : StoredRows mem l.rows D.2
  /-- Header length of the fixed-format selectors in one strict row. -/
  selectors : l.selectors = 2*blocks*(l.groups.choose 2)^n *
    VPVNP.MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h
  /-- Public padding dimensions. -/
  alphabet : l.alphabet = l.groups^(n+1)
  blockCount : l.blocks = blocks
  blockWidth : l.blockWidth = h*b
  /-- The actual little-endian product label of each packed cell. -/
  labels : ∀ c, mem (l.labels+c.val) = (finFunctionFinEquiv (label c)).val
  /-- Every incoming delivery contributes its actual width at its receiving cell. -/
  demands : ∀ c : Fin l.cells, mem (l.demands+c.val) = ∑ a, if recv a = c then w a else 0

variable {A : Type*} [Fintype A] {b : ℕ} {D : LengthDeclaration n l.groups}
variable {label : Fin l.cells → Label (n+1) l.groups} {recv : A → Fin l.cells} {w : A → ℕ}
variable (image : PhysicalImage l mem blocks b K h D label recv w)
include image

private theorem row_word (s t : Fin l.groups) :
    mem (l.rowAddr s.val t.val) = D.2 (Sym2.mk s t) D.1 := by
  by_cases he : s ≤ t
  · have eq := image.rows s t D.1
    rw [entryOrder_val,ite_eq_left he] at eq
    simpa only [Layout.rowAddr,Nat.add_assoc,image.axes,image.axis,min_eq_left (show s.val ≤ t.val from he),max_eq_right (show s.val ≤ t.val from he)] using eq
  · have hle := le_of_not_ge he
    have eq := image.rows t s D.1
    rw [entryOrder_val,ite_eq_left hle] at eq
    simpa only [Layout.rowAddr,Nat.add_assoc,image.axes,image.axis,min_eq_right (show t.val ≤ s.val from hle),max_eq_left (show t.val ≤ s.val from hle),
      (show Sym2.mk t s = Sym2.mk s t from Sym2.eq_swap)] using eq

private theorem selector_word (s t : Fin l.groups) (hne : s ≠ t) :
    l.selectors = rowSelectorBits n l.groups blocks K h D.1 (Sym2.mk s t) := by
  rw [image.selectors]
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact (Owned.strict_rowSelectorBits K h D.1 ⟨(s,t),hlt⟩).symm
  · rw [(show Sym2.mk s t = Sym2.mk t s from Sym2.eq_swap)]
    exact (Owned.strict_rowSelectorBits K h D.1 ⟨(t,s),hgt⟩).symm

/-- All ordered row reads directed into one symbol give exactly the incident lists. -/
theorem PhysicalImage.shared_eq (s : Fin l.groups) :
    l.sharedTotal mem (l.groups*l.groups) s.val = incidentWidth blocks K h D s := by
  let value := fun p : Fin l.groups × Fin l.groups => if p.1 = s ∧ s ≠ p.2 then
    D.2 (Sym2.mk s p.2) D.1 + rowSelectorBits n l.groups blocks K h D.1 (Sym2.mk s p.2) else 0
  have read (q : Fin (l.groups*l.groups)) :
      l.rowCharge mem q.val s.val = value (finProdFinEquiv.symm q) := by
    let p : Fin l.groups × Fin l.groups := finProdFinEquiv.symm q
    have hf : p.1.val = q.val / l.groups := rfl
    have hs : p.2.val = q.val % l.groups := rfl
    change _ = value p
    simp only [Layout.rowCharge,← hf,← hs,ne_eq,Fin.val_inj,value]
    split
    · exact congrArg₂ Nat.add (row_word image s p.2) (selector_word image s p.2 ‹_ ∧ _›.2)
    · rfl
  calc
    l.sharedTotal mem (l.groups*l.groups) s.val = ∑ q : Fin (l.groups*l.groups), l.rowCharge mem q.val s.val :=
      (Fin.sum_univ_eq_sum_range _ _).symm
    _ = ∑ p, value p := Fintype.sum_equiv finProdFinEquiv.symm _ _ read
    _ = incidentWidth blocks K h D s := by
      rw [Fintype.sum_prod_type, Fintype.sum_eq_single s]
      · apply sum_congr rfl
        intro t _
        by_cases hst : s = t <;> simp [value,hst]
      · intro t ht
        simp [value,ht]

/-- The native division and remainder read the chosen coordinate of the actual label. -/
theorem PhysicalImage.symbol_eq (c : Fin l.cells) :
    l.symbol mem c.val = (label c D.1).val := by
  rw [Layout.symbol,image.labels,Layout.place,image.axis]
  exact congrArg (fun f : Label (n+1) l.groups => (f D.1).val)
    (finFunctionFinEquiv.symm_apply_apply (label c))

/-- All cell-demand reads for a group count exactly the bits delivered to it. -/
theorem PhysicalImage.data_eq (s : Fin l.groups) :
    l.dataTotal mem l.cells s.val = incomingWidth label recv w D.1 s := by
  change (∑ c ∈ range l.cells, l.dataCharge mem c s.val) = _
  rw [← Fin.sum_univ_eq_sum_range]
  simp only [Layout.dataCharge,image.symbol_eq,Fin.val_inj,image.demands]
  have summands (c : Fin l.cells) :
      (if label c D.1 = s then ∑ a, if recv a = c then w a else 0 else 0) =
        ∑ a, if recv a = c then (if label (recv a) D.1 = s then w a else 0) else 0 := by
    by_cases hc : label c D.1 = s
    · rw [ite_eq_left hc]
      apply sum_congr rfl
      intro a _
      by_cases ha : recv a = c <;> simp [ha,hc]
    · rw [ite_eq_right hc]
      symm
      apply sum_eq_zero
      intro a _
      by_cases ha : recv a = c <;> simp [ha,hc]
  simp_rw [summands]
  rw [sum_comm]
  simp [incomingWidth]

/-- Closed header arithmetic counts the actual padded wires touching the symbol. -/
theorem PhysicalImage.raw_eq (s : Fin l.groups) :
    l.raw = groupRaw (blocks*(h*b)) D.1 s := by
  have hd : 0 < l.groups := Nat.zero_lt_of_lt s.isLt
  have cancel : l.groups^(n+1)/l.groups = l.groups^n := by
    rw [pow_succ, Nat.mul_div_cancel _ hd]
  rw [Layout.raw,image.alphabet,image.blockCount,image.blockWidth,cancel,groupRaw_eq]

/-- The millionfold native weight equals the paper's three actual costs. -/
theorem PhysicalImage.weight_eq (s : Fin l.groups) :
    l.weight mem s.val = TeamNative.scaledWeight (incidentWidth blocks K h D s)
      (incomingWidth label recv w D.1 s) (groupRaw (blocks*(h*b)) D.1 s) := by
  rw [Layout.weight,image.shared_eq,image.data_eq,image.raw_eq s]

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
