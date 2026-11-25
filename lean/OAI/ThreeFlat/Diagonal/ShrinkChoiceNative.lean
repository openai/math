import OAI.ThreeFlat.Diagonal.ShrinkStageWordValues
import OAI.ThreeFlat.Diagonal.RefreshChoiceFits
import OAI.ThreeFlat.Diagonal.RefreshWidthFits
import OAI.ThreeFlat.Diagonal.RefreshSplitNative

namespace OAI
/-! # Exact native words at the shrink choice and supply scan entries -/

namespace ThreeFlat.Diagonal.ShrinkStageNav

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.MotifRows
open RefreshDemandRows RefreshStageNav MotifIntegerChoice
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {W k : ℕ} (cur : Word W) (mem : Memory W) (arg : Word W)
private abbrev nativeMemory (m : Memory W) (i : ℕ) : ℕ := (m i).val
private abbrev nativeInput (a : Word W) (_ : Fin 1) : ℕ := a.val
private abbrev nativeValue (m : Memory W) (a : Word W) (e : Formula 1) : ℕ :=
  Formula.natural W (fun _ : Param => 0) (nativeMemory m) (nativeInput a) e
private abbrev nativeFits (m : Memory W) (a : Word W) (e : Formula 1) : Prop :=
  Formula.Fits W (fun _ : Param => 0) (nativeMemory m) (nativeInput a) e

theorem ptr_fit (i : ℕ) (h : (mem cur.val).val+i<2^W) : nativeFits mem arg (ptr cur i) :=
  field_fit cur mem (fun _=>arg) i h

theorem rel_fit (i : ℕ) (h : (mem cur.val).val+i<2^W) : nativeFits mem arg (rel cur i) :=
  index_fit cur mem (fun _=>arg) i h

theorem parts (i d : ℕ) (j : Fin d) :
    (i*d+j.val)/d=i ∧ (i*d+j.val)%d=j.val := by
  constructor
  · rw [Nat.mul_comm i,Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  · rw [Nat.mul_comm i,Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]

def descriptor (base : Fin (k+1)→Fin 2→ℕ) (size : Fin (k+1)→ℕ) (demand : Fin 2→ℕ) (f : Fin 3) :=
  let j := tileNumber demand base
  if f.val=0 then score demand base j else if f.val=1 then j.val else size j

theorem choice_native (base : Fin (k+1)→Fin 2→ℕ) (size : Fin (k+1)→ℕ) (row : ℕ) (f : Fin 3)
    (demand : Fin 2→ℕ) (head : (mem cur.val).val+8<2^W) (three : 3<2^W) (table : k+1≤2^W)
    (atReg : arg.val=nativeValue mem arg (ptr cur 2)+(row*3+f.val))
    (src : nativeValue mem arg (ptr cur 8)+row*2+2≤2^W) (input : ∀ i : Fin 2,(nativeMemory mem) (nativeValue mem arg (ptr cur 8)+row*2+i.val)=demand i)
    (budget : ∀ j i,sentinel demand+base j i<2^W) :
    (HeaderScan.closed (choiceWords cur base size)).eval Fin.elim0 mem (fun _=>arg)=
      (descriptor base size demand f:Word W) := by
  let pos := rel cur 2
  let r := Formula.op .div pos (.lit 3)
  let col := Formula.op .mod pos (.lit 3)
  let b := fun i : Fin 2=>RAM.MotifRows.field (atRow (ptr cur 8) r 2) i.val
  let z := chooseFields b base
  have ip : nativeValue mem arg pos=row*3+f.val := by change arg.val-nativeValue mem arg (ptr cur 2)=_; omega
  have rv : nativeValue mem arg r=row := by change nativeValue mem arg pos/3=_; rw [ip,(parts row 3 f).1]
  have cv : nativeValue mem arg col=f.val := by change nativeValue mem arg pos%3=_; rw [ip,(parts row 3 f).2]
  have fpos : nativeFits mem arg pos := rel_fit cur mem arg 2 (by omega)
  have bp : nativeValue mem arg pos<2^W := (Nat.sub_le ..).trans_lt arg.isLt
  have fr : nativeFits mem arg r := ⟨fpos,trivial,bp,three⟩
  have fc : nativeFits mem arg col := ⟨fpos,trivial,bp,three⟩
  have fb (i : Fin 2) : nativeFits mem arg (b i) := by
    refine ⟨⟨⟨ptr_fit cur mem arg 8 head,⟨fr,trivial,trivial⟩,trivial⟩,trivial,trivial⟩,?_⟩
    change nativeValue mem arg (ptr cur 8)+nativeValue mem arg r*2+i.val<_
    rw [rv]
    have := i.isLt
    omega
  have values : (fun i=>nativeValue mem arg (b i))=demand := by
    funext i
    change (nativeMemory mem) (nativeValue mem arg (ptr cur 8)+nativeValue mem arg r*2+i.val)=_
    rw [rv,input]
  have fit := chooseFields_fits (fun _ : Param => 0) (nativeMemory mem) (nativeInput arg) b base fb (by rw [values]; have := budget 0 0; omega) (by rwa [values])
  have zz := congrArg Prod.snd (chooseFields_value W (fun _ : Param => 0) (nativeMemory mem) (nativeInput arg) b base)
  have zFit : nativeValue mem arg z.2 < 2^W :=
    lt_of_eq_of_lt zz ((tileNumber (fun i => nativeValue mem arg (b i)) base).isLt.trans_le table)
  have colFit : nativeValue mem arg col < 2^W := lt_of_eq_of_lt cv (f.isLt.trans three)
  apply closed_read mem (fun _=>arg)
  · refine ⟨fc,trivial,colFit,(by change 0<_; omega),?_⟩
    split
    · exact fit.1
    · refine ⟨fc,trivial,colFit,(by change 1<_; omega),?_⟩
      split
      · exact fit.2
      · exact rowAt_fit (fun _ : Param => 0) (nativeMemory mem) (nativeInput arg) _ _ fit.2 zFit table (fun _=>trivial)
  · rw [choiceWords_value]
    let observed : Fin 2 → ℕ := fun i => nativeValue mem arg (b i)
    have readRow : observed = demand := values
    change (if nativeValue mem arg col = 0 then score observed base (tileNumber observed base)
      else if nativeValue mem arg col = 1 then (tileNumber observed base).val
      else size (tileNumber observed base)) = descriptor base size demand f
    rw [cv, readRow]; rfl


end
end ThreeFlat.Diagonal.ShrinkStageNav

end OAI
