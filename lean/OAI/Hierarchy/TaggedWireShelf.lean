import OAI.Hierarchy.TaggedWireSelectors
import OAI.Hierarchy.ProtocolRAMAdmission

namespace OAI
/-! # Native histogram fields on the immutable selector shelf -/

noncomputable section
namespace Hierarchy.WireTelescope.HistogramShelf
open ThreeFlat.Diagonal.MotifOuterTerms
open ThreeFlat.RAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ProtocolRAM
open scoped BigOperators Classical Fin.CommRing

variable {W n q d : ℕ}

/-- Word columns store the actual concatenated bit input in row-major order. -/
def header (base : ℕ) (bits : Tagged.Bits ((n*q)*W)) (rest : Memory W) : Memory W :=
  fillSegment base (n*q) (fun a=>if j:a-base<n*q then (arrayBits (n*q) W).symm bits ⟨a-base,j⟩ else 0) rest

def cell (n q : ℕ) (i : Fin n) (j : Fin q) := (finProdFinEquiv (i,j)).val

theorem read_header (size base : ℕ) (bits : Tagged.Bits ((n*q)*W)) (rest : Memory W)
    (fit : base+n*q ≤ size) (i : Fin n) (j : Fin q) :
    Computability.VPVNP.RAMMemory.initialMemory size (header base bits rest) (base+cell n q i j) =
      (arrayBits (n*q) W).symm bits (finProdFinEquiv (i,j)) := by
  have h : cell n q i j<n*q := (finProdFinEquiv (i,j)).isLt
  have inside : base≤base+cell n q i j ∧ base+cell n q i j<base+n*q := by omega
  have allocated : base+cell n q i j< size:=by omega
  simp only [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left allocated,header,fillSegment,ite_eq_left inside,
    Nat.add_sub_cancel_left,dite_eq_left h]; rfl

/-- One fixed native expression per menu letter, shared by every candidate
row in the attempt. -/
def field (bank : Bank) (j : Fin q) : Expr :=
  .lookup bank (.op .add (scale q .row) (.lit j.val))

theorem read_field (bank : Bank) (m : Memory W) (i : Fin n) (j : Fin q)
    (fit : n*q≤bank.size) (room : n*q≤2^W) :
    (field bank j).eval m (i.val:Word W)=m (bank.base+cell n q i j) := by
  have size := (finProdFinEquiv (i,j)).isLt
  have ident : cell n q i j = q*i.val+j.val := Nat.add_comm ..
  have bound : (q*i.val+j.val)<n*q := by rw [←ident]; exact size
  simp only [field,Expr.eval,eval_scale,RowOp.opcode,BinaryOp.eval,←Nat.cast_mul,←Nat.cast_add,Bank.read,
    Fin.val_cast_of_lt (bound.trans_le room),Nat.mod_eq_of_lt (bound.trans_le fit),ident]

theorem encoded_words (letters copies : Fin n → ℕ) (width : ∀i,letters i≤q)
    (room : ∀i,copies i<2^W) (h : BallChoices letters copies) (i : Fin n) (j : Fin q) :
    (arrayBits (n*q) W).symm (selectorTable letters copies width room h) (finProdFinEquiv (i,j)) =
      counterRows letters copies h room i j := by
  apply (wordBits W).injective
  funext k
  rw [←arrayBits_at,Equiv.apply_symm_apply]
  let z : Fin ((n*q)*W):=finProdFinEquiv (finProdFinEquiv (i,j),k)
  let pair : Fin (n*q)×Fin W:=finProdFinEquiv.symm z
  let indices : Fin n×Fin q:=finProdFinEquiv.symm pair.1
  change (wordBits W) (counterRows letters copies h room indices.1 indices.2) pair.2=_
  simp only [indices,pair,z,Equiv.symm_apply_apply]

/-- The total of the padded (q) words equals the sum on the true alphabet. -/
private theorem padded_total {a : ℕ} (fit : a≤q) (f : Fin a→ℕ) :
    (∑ j : Fin q, if h:j.val<a then f ⟨j.val,h⟩ else 0) = ∑ j,f j := by
  let inc := Fin.castLEEmb fit
  let g (j : Fin q) := if h:j.val<a then f ⟨j.val,h⟩ else 0
  have all : (∑ j ∈ Finset.univ.map inc, g j) = ∑ j,g j := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro j _ missing
    have no : ¬j.val<a := fun h=>missing (Finset.mem_map.mpr ⟨⟨j.val,h⟩,Finset.mem_univ _,Fin.ext rfl⟩)
    simp [g,no]
  change (∑ j,g j)=∑ j,f j
  rw [←all]
  simp [g,inc,Fin.val_castLE]

/-- The exact set of accepted rectangular fields, read from the snapshot.
A skipped row has no free selector multiplicity. -/
theorem valid_iff_unique (b : Batch q d) (m : Memory W) (letters copies : Fin n→ℕ)
    (alphabet : ∀ i,letters i=(b.termCount.read m (b.packet.eval m (i.val:Word W))).val)
    (maxLetters : ∀i,letters i≤q) (room : ∀ i,copies i<2^W)
    (number : ∀ i,copies i=if b.selected m (i.val:Word W) then b.copies else 0) :
    (∀ i : Fin n,b.valid m (i.val:Word W)) ↔
      ∃! h : BallChoices letters copies, ∀ i j,
        (b.field j).eval m (i.val:Word W)=counterRows letters copies h room i j := by
  let r (i : Fin n) (j : Fin q) := ((b.field j).eval m (i.val:Word W)).val
  let bound (i : Fin n) := ∀ j : Fin q,r i j ≤ if j.val<letters i then copies i else 0
  have row (i : Fin n) : b.valid m (i.val:Word W) ↔ bound i ∧ (∑ j,r i j)=copies i := by
    by_cases sel : b.selected m (i.val:Word W)
    · simp only [Batch.valid,Batch.withinPacket,bound,r,alphabet,number,ite_eq_left sel]
    · simp only [Batch.valid,bound,r,number,ite_eq_right sel,ite_self,Nat.le_zero]
      constructor
      · intro h
        simp [h]
      · rintro ⟨h,_⟩ j
        exact Fin.ext (h j)
  have unique (h h' : BallChoices letters copies)
      (eq : ∀(i : Fin n) (j : Fin q),counterRows letters copies h room i j=counterRows letters copies h' room i j) : h=h' := by
    funext i
    apply Subtype.ext
    funext j
    apply Fin.ext
    simpa only [counter_of_active] using congrArg Fin.val (eq i (j.castLE (maxLetters i)))
  constructor
  · intro ok
    have lim (i) := ((row i).mp (ok i)).1
    have count (i) := ((row i).mp (ok i)).2
    let value (i : Fin n) (j : Fin (letters i)) : Fin (copies i+1) :=
      ⟨r i (j.castLE (maxLetters i)),Nat.lt_succ_of_le (by
        simpa only [Fin.val_castLE,dite_eq_left j.isLt,ite_eq_left j.isLt] using lim i (j.castLE (maxLetters i)))⟩
    have words (i : Fin n) (j : Fin q) : r i j=if hj:j.val<letters i then (value i ⟨j.val,hj⟩).val else 0 := by
      split_ifs with hj
      · rfl
      · exact Nat.eq_zero_of_le_zero (by simpa only [ite_eq_right hj] using lim i j)
    let h (i : Fin n) : Histogram (Fin (letters i)) (copies i) :=
      ⟨value i,((padded_total (maxLetters i) (fun j=>(value i j).val)).symm.trans
        ((Finset.sum_congr rfl (fun j _=>(words i j).symm)).trans (count i)))⟩
    have code (i : Fin n) (j : Fin q) : (b.field j).eval m (i.val:Word W)=counterRows letters copies h room i j := by
      apply Fin.ext
      change r i j=(counterRows letters copies h room i j).val
      by_cases hj : j.val<letters i
      · simpa only [counterRows,h,dite_eq_left hj] using words i j
      · simpa only [counterRows,dite_eq_right hj,Fin.val_zero] using words i j
    exact ⟨h,code,fun h' eq=>unique h' h (fun i j=>(eq i j).symm.trans (code i j))⟩
  · rintro ⟨h,eq,_⟩ i
    apply (row i).mpr
    have words (j : Fin q) : r i j=if hj:j.val<letters i then ((h i).val ⟨j.val,hj⟩).val else 0 := by
      change ((b.field j).eval m (i.val:Word W)).val=_
      rw [eq i j]
      by_cases hj : j.val<letters i
      · simp only [counterRows,dite_eq_left hj]
      · simp only [counterRows,dite_eq_right hj,Fin.val_zero]
    constructor
    · intro j
      rw [words]
      split_ifs with hj
      · exact Nat.lt_succ_iff.mp ((h i).val ⟨j.val,hj⟩).isLt
      · rfl
    · exact (Finset.sum_congr rfl (fun j _=>words j)).trans
        ((padded_total (maxLetters i) (fun j=>((h i).val j).val)).trans (h i).property)

end Hierarchy.WireTelescope.HistogramShelf

end
end OAI
