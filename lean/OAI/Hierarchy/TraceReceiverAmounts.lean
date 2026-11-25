import OAI.Hierarchy.TraceReceiverTasks

namespace OAI
/-! # Prefix offsets from the selected roots' actual S13 records -/
namespace Hierarchy.TraceReceiverTasks
open ThreeFlat RAM DescriptorExpr DescriptorScan
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators

variable {W : ℕ}

/-- S13 fields one, two and three contain local pins, rows and internal bits. -/
def amount (W dst selected first results : ℕ) (field : Fin 3) : Term W 0 1 :=
  let i := Term.binary .sub (.result 0) (.literal dst)
  let v := Term.load (.binary .add (.literal selected) i)
  let id := Term.binary .add (.load (.literal first)) v
  .load (.binary .add (.binary .add (.literal results) (.binary .mul (.literal 8) id))
    (.literal (field.val+1)))

def amountAddress (selected first results : ℕ) (field : Fin 3) (m : Memory W) (i : Word W) :=
  (results:Word W)+8*(m (first:Word W).val+m ((selected:Word W)+i).val)+((field.val+1:ℕ):Word W)

def amountImage (dst selected first results n : ℕ) (field : Fin 3) (m : Memory W) :=
  fillSegment dst n (fun a=>m (amountAddress selected first results field m ((a:Word W)-(dst:Word W))).val) m

theorem amount_eval (dst selected first results : ℕ) (field : Fin 3)
    (m : Memory W) (a : Word W) (pub : Fin 0 → Word W) :
    (amount W dst selected first results field).eval pub m (fun _=>a)
      =m (amountAddress selected first results field m (a-(dst:Word W))).val := by
  simp [amount,amountAddress,Term.eval,BinaryOp.eval]

def amountScan (W current dst selected first results : ℕ) (field : Fin 3) :=
  HeaderScan.procedure (current:Word W) 0 1 (amount W dst selected first results field)

theorem amount_run (current dst selected first results n : ℕ) (field : Fin 3) (m : Memory W)
    (fit : dst+n < 2^W)
    (base : m (m (current:Word W).val+0).val=(dst:Word W))
    (length : m (m (current:Word W).val+1).val=(n:Word W))
    (table : selected+n ≤ dst) (metaBefore : first < dst)
    (source : ∀ i : Fin n, let a := (amountAddress selected first results field m (i.val : Word W)).val
      a < dst ∨ dst+n ≤ a) :
    (amountScan W current dst selected first results field).Spec (·=m)
      (fun _ out=>out=amountImage dst selected first results n field m)
      (13+n*(2*(amount W dst selected first results field).binds+4)) := by
  intro P R K M pc reg pub exit installed data c state start entry
  subst state
  obtain ⟨t,tm,out,pc',go⟩ := HeaderScan.advance_block (amount W dst selected first results field)
    (current:Word W) 0 1 dst n fit pc reg pub exit M installed c m start
    (fun a=>m (amountAddress selected first results field m ((a:Word W)-(dst:Word W))).val)
    base length (by
      intro a mem lo hi same
      rw [amount_eval,Fin.cast_val_eq_self]
      have dstVal : (dst:Word W).val=dst := Fin.val_cast_of_lt (by omega)
      have ge : (dst:Word W) ≤ a := by
        change (dst:Word W).val ≤ a.val
        rwa [dstVal]
      have delta : (a-(dst:Word W)).val=a.val-dst :=
        (Fin.sub_val_of_le ge).trans (by rw [dstVal])
      let i : Fin n := ⟨a.val-dst,by omega⟩
      have id : (i.val : Word W)=a-(dst:Word W) :=
        Fin.ext (by rw [Fin.val_cast_of_lt (by dsimp [i]; omega),delta])
      have e : ((selected:Word W)+(a-(dst:Word W))).val=selected+i.val := by
        rw [←id,←Nat.cast_add,Fin.val_cast_of_lt (by dsimp [i]; omega)]
      have hfirst := same (first:Word W).val (Or.inl (by rw [Fin.val_cast_of_lt (by omega)]; exact metaBefore))
      have hselected := same ((selected:Word W)+(a-(dst:Word W))).val (Or.inl (by rw [e];have := i.isLt;omega))
      have src := source i
      rw [id] at src
      simp only [amountAddress,hfirst,hselected]
      exact same _ src)
  exact ⟨t,tm,out,_,go,pc',rfl⟩

theorem amount_at (dst selected first results n : ℕ) (field : Fin 3) (m : Memory W) (i : Fin n) :
    amountImage dst selected first results n field m (dst+i.val)
      =m (amountAddress selected first results field m (i.val : Word W)).val := by
  have inside : dst ≤ dst+i.val ∧ dst+i.val < dst+n := by have := i.isLt; omega
  simp [amountImage,fillSegment,inside,Nat.cast_add]

/-- A second native scan runs the exclusive prefix on the selected numeric
column. Both passes use the same underlying 64-word archive root numbering. -/
theorem amount_prefix (x : TerminalWireArchive.Layout) (m : Memory W)
    (selected first results : ℕ) (field : Fin 3) (space : TerminalWireArchive.Bounds x W)
    (capacity : ∑ i : Fin x.edges,(m (amountAddress selected first results field m (i.val:Word W)).val).val ≤ x.capacity)
    (i : ℕ) (hi : i ≤ x.edges) :
    let mid:=amountImage x.widthBase selected first results x.edges field m
    (TerminalWireArchive.image x mid (x.prefixBase+i)).val
      = ∑ j : Fin i,(m (amountAddress selected first results field m (j.val:Word W)).val).val := by
  apply TerminalWireArchive.image_exact x _ space
    (fun j : Fin x.edges=>(m (amountAddress selected first results field m (j.val:Word W)).val).val) rfl _ capacity i hi
  intro j
  rw [amount_at]

end Hierarchy.TraceReceiverTasks

end OAI
