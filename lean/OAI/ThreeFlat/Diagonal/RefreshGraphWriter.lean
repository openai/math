import OAI.ThreeFlat.Diagonal.RefreshNeighborGraph
import OAI.ThreeFlat.Diagonal.CompressorSixColumns
import OAI.ThreeFlat.Diagonal.SlotImage

namespace OAI
/-! # All six native graph columns agree with the common numbered-slot image -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.Refresh

open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM.DescriptorExpr CompressorRefresh
open scoped Fin.CommRing

variable {w k v D a lanes : ℕ} {H L : Type} [Zero L]

def fieldOf : Fin 3 → Field := ![.neighbor,.matePort,.delta]

def graphField (back : Bool) (f : Fin 3) : Fin 6 :=
  ⟨SlotImage.column back f,by cases back <;> dsimp [SlotImage.column] <;> have := f.isLt <;> omega⟩

private theorem oriented_field (back : Bool) (f : Fin 3) :
    decide (3≤(graphField back f).val)=back ∧
    (![Field.neighbor,.matePort,.delta,.neighbor,.matePort,.delta] : Fin 6 → Field) (graphField back f)=fieldOf f := by
  cases back <;> fin_cases f <;> decide

/-- Native physical inputs needed by the adjacency scan after the three
split-displacement columns have been produced. -/
structure GraphInput (G : LiftedSlots (Fin v) D (H × L)) (lane : L ≃ Fin lanes)
    (old : Bool → OldColumns (Term w k 1)) (pub : Fin k → Word w) (mem : Memory w) (vs : Fin 1 → Word w) : Prop where
  neighbor : ∀ p back, mem (((old back).neighbor.eval pub mem vs)+(SlotImage.ordinal (Equiv.refl _) p:Word w)).val =
    (((step G back p).1.1.val:ℕ):Word w)
  mate : ∀ p back, mem (((old back).mate.eval pub mem vs)+(SlotImage.ordinal (Equiv.refl _) p:Word w)).val =
    (((step G back p).1.2.val:ℕ):Word w)
  remaining : ∀ p back, mem (((old back).remainingShift.eval pub mem vs)+(SlotImage.ordinal (Equiv.refl _) p:Word w)).val =
    (((lane (step G back p).2.2).val:ℕ):Word w)

theorem six_graph_read (G : LiftedSlots (Fin v) D (H × L)) (E : SlotGraph (Fin D) a) (hm : 2≤D)
    (lane : L ≃ Fin lanes) (zero : (lane 0).val=0) (pad : ℕ) (old : Bool → OldColumns (Term w k 1))
    (start size : Term w k 1) (pub : Fin k → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
    (st : GraphInput G lane old pub mem vs) (p : (Fin v × Fin D) × Fin (1+a+pad)) (back : Bool) (f : Fin 3)
    (lo : ℕ) (base : start.eval pub mem vs=(lo:Word w))
    (len : size.eval pub mem vs=((v*D*(1+a+pad):ℕ):Word w))
    (inside : lo+6*(v*D*(1+a+pad))<2^w) (hw : 6≤2^w) (deg : 1+a+pad<2^w)
    (hD : D<2^w) (rom : D*a≤2^w) (hrot : 2*D<2^w)
    (addr : vs 0=((SlotImage.cell ⟨lo,v*D*(1+a+pad),0⟩ finProdFinEquiv p back f:ℕ):Word w)) :
    (refreshColumns E pad old start size).eval pub mem vs=
      ((SlotImage.fields (graph G E hm pad) finProdFinEquiv lane p back f:ℕ):Word w) := by
  let idx := graphField back f
  let q := (p.1.1.val*D+p.1.2.val)*(1+a+pad)+p.2.val
  let n := v*D*(1+a+pad)
  have rep : SlotImage.ordinal finProdFinEquiv p=q := by
    change (p.1.2.val+D*p.1.1.val)*(1+a+pad)+p.2.val=_
    dsimp [q]; ac_rfl
  have hq : q<n := rep ▸ SlotImage.ordinal_lt finProdFinEquiv p
  have hstart : lo+idx.val*n+q<2^w := by
    have h := Nat.mul_le_mul_right n idx.isLt
    rw [Nat.succ_mul] at h
    omega
  have width : n<2^w := by omega
  have word : vs 0=((lo+idx.val*n+q:ℕ):Word w) := by
    rw [addr]; congr 1; unfold SlotImage.cell; rw [rep,Nat.mul_comm n]; rfl
  unfold refreshColumns
  rw [eval_sixColumns pub mem vs start size _ idx lo n q hw width hq hstart base len word]
  try dsimp only
  have direction := oriented_field back f
  rw [direction.1,direction.2]
  let out := Term.binary .add start (.binary .mul size (.literal (idx.val:Word w)))
  have shifted : vs 0=out.eval pub mem vs+(q:Word w) := by
    rw [word]; simp [out,base,len,BinaryOp.eval,n,Nat.mul_comm idx.val]
  rw [row_read E back pad (fieldOf f) (old back) out pub mem vs p.1.1.val p.1.2 p.2 shifted
    (hq.trans width) deg hD rom (by cases back <;> dsimp <;> have := p.1.2.isLt <;> omega)]
  try dsimp only
  have neighbor := st.neighbor p.1 back
  have mate := st.mate p.1 back
  have remaining := st.remaining p.1 back
  simp only [SlotImage.ordinal,Equiv.refl_apply] at neighbor mate remaining
  rw [neighbor,mate,remaining]
  let encode := fun l : L => ((lane l).val:Word w)
  have eq := fieldWord_graph G E hm pad back (fieldOf f) encode (by simp [encode,zero]) p
  refine eq.trans ?_
  cases back <;> fin_cases f <;>
    simp [fieldOf,step,SlotImage.fields,SlotImage.oriented,SlotImage.shift,encode,finProdFinEquiv,
      Nat.mul_comm,Nat.add_comm]

end ThreeFlat.Diagonal.CompressorPacking.Native.Refresh

end OAI
