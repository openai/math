import OAI.ThreeFlat.Diagonal.ShrinkChoiceNative

namespace OAI
/-! # Issued natural widths, including selector bits, in the physical supply stream -/

namespace ThreeFlat.Diagonal.ShrinkStageNav

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.MotifRows
open RefreshDemandRows RefreshStageNav
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {W k : ℕ} (cur : Word W) (mem : Memory W) (arg : Word W)
open private nativeMemory nativeInput nativeValue nativeFits from
  OAI.ThreeFlat.Diagonal.ShrinkChoiceNative

theorem supply_native (K : ℕ) (size bits : Fin (k+1)→ℕ) (pool : ∀ j, Fin (size j)→Fin 8→ℕ)
    (row : ℕ) (j : Fin (k+1)) (e : Fin 8) (copies : ℕ) (hist : Fin (size j)→ℕ)
    (head : (mem cur.val).val+3<2^W) (eight : 8<2^W) (table : k+1≤2^W)
    (atReg : arg.val=nativeValue mem arg (ptr cur 3)+(row*8+e.val))
    (choice : nativeValue mem arg (ptr cur 2)+row*3+2≤2^W) (count : nativeValue mem arg (ptr cur 1)+row*K+K≤2^W)
    (alphabet : ∀ j,size j≤K) (chosen : (nativeMemory mem) (nativeValue mem arg (ptr cur 2)+row*3+1)=j.val)
    (copiesRead : (nativeMemory mem) (nativeValue mem arg (ptr cur 2)+row*3)=copies)
    (raw : ∀ i : Fin (size j),(nativeMemory mem) (nativeValue mem arg (ptr cur 1)+row*K+i.val)=hist i) :
    (HeaderScan.closed (widthWords cur K size bits pool)).eval Fin.elim0 mem (fun _=>arg)=
      ((copies*bits j+∑ i,hist i*pool j i e:ℕ):Word W) := by
  let pos := rel cur 3
  let owner := Formula.op .div pos (.lit 8)
  let port := Formula.op .mod pos (.lit 8)
  let desc := atRow (ptr cur 2) owner 3
  let counts := atRow (ptr cur 1) owner K
  have ip : nativeValue mem arg pos=row*8+e.val := by change arg.val-nativeValue mem arg (ptr cur 3)=_; omega
  have rd : nativeValue mem arg owner=row := by change nativeValue mem arg pos/8=_;rw [ip,(parts row 8 e).1]
  have ed : nativeValue mem arg port=e.val := by change nativeValue mem arg pos%8=_;rw [ip,(parts row 8 e).2]
  have fp : nativeFits mem arg pos := rel_fit cur mem arg 3 head
  have bp : nativeValue mem arg pos<2^W := (Nat.sub_le ..).trans_lt arg.isLt
  have fo : nativeFits mem arg owner := ⟨fp,trivial,bp,eight⟩
  have fe : nativeFits mem arg port := ⟨fp,trivial,bp,eight⟩
  have fd : nativeFits mem arg desc := ⟨ptr_fit cur mem arg 2 (by omega),⟨fo,trivial,trivial⟩,trivial⟩
  have fc : nativeFits mem arg counts := ⟨ptr_fit cur mem arg 1 (by omega),⟨fo,trivial,trivial⟩,trivial⟩
  have de : nativeValue mem arg desc=nativeValue mem arg (ptr cur 2)+row*3 := congrArg (fun r=>nativeValue mem arg (ptr cur 2)+r*3) rd
  have ce : nativeValue mem arg counts=nativeValue mem arg (ptr cur 1)+row*K := congrArg (fun r=>nativeValue mem arg (ptr cur 1)+r*K) rd
  have fs (i : Fin 2) : nativeFits mem arg (RAM.MotifRows.field desc i.val) := by
    refine ⟨⟨fd,trivial,trivial⟩,?_⟩
    change nativeValue mem arg desc+i.val<_
    rw [de]
    have := i.isLt
    omega
  have key : nativeValue mem arg (RAM.MotifRows.field desc 1)=j.val := by
    change (nativeMemory mem) (nativeValue mem arg desc+1)=_
    rwa [de]
  apply closed_read mem (fun _=>arg)
  · let supply (r : Fin (k+1)) (arc : Fin 8) : Formula 1 :=
      outputWidth (fun i => pool r i arc) counts (RAM.MotifRows.field desc 0) (bits r)
    change nativeFits mem arg (rowAt (k+1) (fun r => rowAt 8 (supply r) port) (RAM.MotifRows.field desc 1))
    refine rowAt_fit (fun _ : Param => 0) (nativeMemory mem) (nativeInput arg)
      (fun r => rowAt 8 (supply r) port) (RAM.MotifRows.field desc 1) (fs 1)
      (lt_of_eq_of_lt key (j.isLt.trans_le table)) table ?_
    intro r
    refine rowAt_fit (fun _ : Param => 0) (nativeMemory mem) (nativeInput arg)
      (supply r) port fe (lt_of_eq_of_lt ed (e.isLt.trans eight)) eight.le ?_
    intro arc
    exact outputWidth_fit (fun _ : Param => 0) (nativeMemory mem) (nativeInput arg)
      (fun i => pool r i arc) counts (RAM.MotifRows.field desc 0) (bits r) fc (fs 0)
      (by change nativeValue mem arg counts + size r ≤ 2^W
          rw [ce]
          exact (Nat.add_le_add_left (alphabet r) _).trans count)
  · refine (widthWords_value (fun _ : Param => 0) (nativeMemory mem) (nativeInput arg)
      cur K size bits pool row j e (ip.trans (by omega)) chosen).trans ?_
    simp only [copiesRead, raw]


end
end ThreeFlat.Diagonal.ShrinkStageNav

end OAI
