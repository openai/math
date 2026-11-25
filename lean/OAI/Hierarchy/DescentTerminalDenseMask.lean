import OAI.Hierarchy.DescentTerminalPaidRows
import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # Native cutoff words for the single paid pool of terminal bits -/

namespace Hierarchy.DescentTerminalDenseMask
open Computability.BorderVNP.Crossing DescentTerminalPorts Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing Classical BigOperators
noncomputable section

variable {D W rows word : ℕ} {P : Type} {bits : P→ℕ} (N : Network D P bits)

def valid (word total i : ℕ) := min word (total-i*word)

theorem dense_range (code : N.Edge ↪ ℕ) (room : (∑e,N.width e)≤rows*word) (q : RowBit rows word) :
    q∈Set.range (denseBits N code room) ↔ q.1.val*word+q.2.val<∑e,N.width e := by
  let order:=ProtocolRAMPortRanks.enumerate N.width code code.injective
  have key : (finProdFinEquiv q).val=q.1.val*word+q.2.val := by change q.2.val+word*q.1.val=_;ac_rfl
  constructor
  · rintro ⟨i,rfl⟩
    rw [←key]
    change (finProdFinEquiv (finProdFinEquiv.symm ((order i).castLE room))).val<_
    simpa only [Equiv.apply_symm_apply,Fin.val_castLE] using (order i).isLt
  · intro h
    let j : Fin (∑e,N.width e):=⟨(finProdFinEquiv q).val,key.symm ▸ h⟩
    refine ⟨order.symm j,finProdFinEquiv.injective ?_⟩
    change finProdFinEquiv (finProdFinEquiv.symm ((order (order.symm j)).castLE room))=finProdFinEquiv q
    rw [Equiv.apply_symm_apply,Equiv.apply_symm_apply]
    exact Fin.ext rfl

theorem mask_read (code : N.Edge ↪ ℕ) (room : (∑e,N.width e)≤rows*word) (q : RowBit rows word) :
    zeroMask N (denseBits N code room) q=decide (valid word (∑e,N.width e) q.1.val≤q.2.val) := by
  simp only [zeroMask, decide_eq_decide, dense_range]
  have := q.2.isLt
  unfold valid
  omega

def expr (W word dst header : ℕ) : Term W 0 1 :=
  let start:=Term.binary .mul (.binary .sub (.result 0) (.literal dst)) (.literal word)
  let used:=Term.load (.literal header)
  let diff:=Term.binary .sub used start
  .select .lt start used (.select .lt diff (.literal word) diff (.literal word)) (.literal 0)

theorem expr_binds (W word dst header : ℕ) : (expr W word dst header).binds=25 := by
  simp only [expr, Term.select, Term.binary, Term.load, Term.literal,
    Term.binds_letThen, Term.binds_rename, Term.binds]

def procedure (W rows word dst header : ℕ) : Procedure W :=
  PhysicalInputPhases.writing (expr W word dst header) Fin.elim0 dst rows

/-- The sole input word is the charged end of the active dense bit array.
Each emitted word is the number of positions available in its physical row. -/
theorem run (total dst header : ℕ) (charge : total≤rows*word) (limit : rows*word<2^W)
    (wordFit : word<2^W) (dstFit : dst+rows<2^W) (headerFit : header<2^W)
    (away : header<dst ∨ dst+rows≤header) :
    (procedure W rows word dst header).Spec (fun m=>m header=(total:Word W))
      (fun m o=>o=fillSegment dst rows (fun a=>(valid word total (a-dst):Word W)) m)
      (4+54*rows) := by
  have rate : 4+54*rows=4+rows*(2*(expr W word dst header).binds+4) := by rw [expr_binds];omega
  rw [rate]
  apply PhysicalInputPhases.writing_spec _ _ _ _ dstFit
  intro original loaded a now lo hi frame
  let i:=a.val-dst
  have ei : i<rows:=by dsimp [i];omega
  have startFit : i*word<2^W := (Nat.mul_le_mul_right word ei.le).trans_lt limit
  have totalFit := charge.trans_lt limit
  have offset : a-(dst:Word W)=(i:Word W) := by
    dsimp [i];rw [Nat.cast_sub lo,Fin.cast_val_eq_self]
  have input : now (header:Word W).val=(total:Word W) := by rw [Fin.val_cast_of_lt headerFit];exact (frame header away).trans loaded
  simp only [expr,Term.eval_select,Term.eval_binary,Term.eval_literal,Term.eval_load,Term.eval,
    Comparison.test,BinaryOp.eval,input,offset,←Nat.cast_mul,decide_eq_true_eq]
  have first : ((i*word:ℕ):Word W)<(total:Word W) ↔ i*word<total := by
    change ((i*word:ℕ):Word W).val<(total:Word W).val ↔ _
    rw [Fin.val_cast_of_lt startFit,Fin.val_cast_of_lt totalFit]
  by_cases active : i*word<total
  · rw [ite_eq_left (first.2 active),←Nat.cast_sub active.le]
    have second : ((total-i*word:ℕ):Word W)<(word:Word W) ↔ total-i*word<word := by
      change ((total-i*word:ℕ):Word W).val<(word:Word W).val ↔ _
      rw [Fin.val_cast_of_lt ((Nat.sub_le ..).trans_lt totalFit),Fin.val_cast_of_lt wordFit]
    change (if _ then _ else _)=((min word (total-i*word):ℕ):Word W)
    by_cases small : total-i*word<word
    · rw [ite_eq_left (second.2 small)]
      exact congrArg (fun z : ℕ=>(z:Word W)) (min_eq_right small.le).symm
    · rw [ite_eq_right (fun h=>small (second.1 h))]
      exact congrArg (fun z : ℕ=>(z:Word W)) (min_eq_left (Nat.le_of_not_gt small)).symm
  · rw [ite_eq_right (fun h=>active (first.1 h))]
    change 0=((min word (total-i*word):ℕ):Word W)
    simp [Nat.sub_eq_zero_of_le (Nat.le_of_not_gt active)]

theorem cutoff_spec (code : N.Edge ↪ ℕ) (room : (∑e,N.width e)≤rows*word) (dst header : ℕ)
    (limit : rows*word<2^W) (wordFit : word<2^W) (dstFit : dst+rows<2^W)
    (headerFit : header<2^W) (away : header<dst ∨ dst+rows≤header) :
    (procedure W rows word dst header).Spec (fun m=>m header=((∑e,N.width e:ℕ):Word W))
      (fun _ o=>∀i : Fin rows,(o (dst+i.val)).val=valid word (∑e,N.width e) i.val ∧
        ∀j : Fin word,decide ((o (dst+i.val)).val≤j.val)=zeroMask N (denseBits N code room) (i,j))
      (4+54*rows) := by
  refine Procedure.Spec.mono (A:=procedure W rows word dst header)
    (run _ dst header room limit wordFit dstFit headerFit away) (fun _ h=>h) ?_ le_rfl
  rintro m _ rfl i
  have fit : valid word (∑e,N.width e) i.val<2^W := (min_le_left ..).trans_lt wordFit
  have value : (fillSegment dst rows (fun a=>(valid word (∑e,N.width e) (a-dst):Word W)) m
      (dst+i.val)).val=valid word (∑e,N.width e) i.val := by
    simp [fillSegment,show dst+i.val<dst+rows from Nat.add_lt_add_left i.isLt _,Fin.val_cast_of_lt fit]
  refine ⟨value,fun j=>?_⟩
  rw [value,mask_read]

end
end Hierarchy.DescentTerminalDenseMask

end OAI
