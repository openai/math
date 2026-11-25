import Mathlib.Algebra.Order.BigOperators.Group.Finset
import OAI.ThreeFlat.RAM.TraceBucketAtom

namespace OAI
/-! # Fixed instruction-text bound of the four-word initial bucket emitter -/

namespace ThreeFlat.RAM.TraceBucketAtom
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr
open private lit reg plus times sub quot modulo from OAI.ThreeFlat.RAM.TraceBucketAtom
open scoped Fin.CommRing

private theorem binary_binds {W K n : ℕ} (op : BinaryOp) (a b : Term W K n) :
    (Term.binary op a b).binds=a.binds+b.binds+1 := by simp [Term.binary,Term.binds]; omega
private theorem choice_binds {W K n : ℕ} (q : Comparison) (a b x y : Term W K n) :
    (Term.select q a b x y).binds=a.binds+b.binds+x.binds+y.binds+1 := by simp [Term.select,Term.binds]; omega
private theorem load_binds {W K n : ℕ} (a : Term W K n) :
    (Term.load a).binds=a.binds+1 := by simp [Term.load,Term.binds]

private theorem orig_bound (W : ℕ) (s : Layout) (i : Fin 13) : ((origArgs s i : Term W 1 4)).binds≤11000 := by
  have h := TraceOwnerFormula.work_le .owner
  fin_cases i <;> simp [origArgs,raw,ext,pinStart,laneBase,TraceOwnerFormula.direct_binds,binary_binds,
    choice_binds,load_binds,Term.literal,Term.binds]; omega

private theorem cmp_bound (W : ℕ) (s : Layout) (i : Fin 15) : ((cmpArgs s i : Term W 1 4)).binds≤22000 := by
  have h := TraceOwnerFormula.work_le .owner
  have hr := TraceOwnerFormula.work_le .row
  have hh := TraceOwnerFormula.work_le .slot
  fin_cases i <;> simp [cmpArgs,raw,ext,pinStart,laneBase,TraceOwnerFormula.direct_binds,binary_binds,
    choice_binds,load_binds,Term.literal,Term.binds] <;> omega

private theorem hole_bound (W : ℕ) (s : Layout) (i : Fin 7) : ((holeArgs s i : Term W 1 4)).binds≤61000 := by
  let q : Term W 1 4 := sub (reg 0) (lit (s.relays+s.gates+s.tags))
  let row : Term W 1 4 := plus (laneBase s) (quot q (lit s.shape.stride))
  let slot : Term W 1 4 := modulo q (lit s.shape.stride)
  have h := TraceOwnerFormula.validSlot_binds s.shape 1 row slot
  simp [q,row,slot,laneBase,binary_binds,Term.literal,Term.binds] at h
  fin_cases i <;> simp [holeArgs,ext,pinStart,laneBase,binary_binds,choice_binds,Term.literal,Term.binds]; omega

private theorem relay_bound (W : ℕ) (s : Layout) (i : Fin 10) : ((relayArgs s i : Term W 1 4)).binds≤100 := by
  fin_cases i <;> simp [relayArgs,ext,pinStart,laneBase,binary_binds,choice_binds,Term.literal,Term.binds]

private theorem sum_le {n W : ℕ} (s : Fin n → Term W 1 4) (h : ℕ) (hh : ∀ i, (s i).binds≤h) :
    (∑ i, (s i).binds) ≤ n*h := by simpa using Finset.sum_le_sum (s:=Finset.univ) (fun i _ => hh i)

theorem binds_le (W : ℕ) (s : Layout) : (program W s).binds≤1000000 := by
  have ho := sum_le (origArgs (W:=W) s) _ (orig_bound W s)
  have hc := sum_le (cmpArgs (W:=W) s) _ (cmp_bound W s)
  have hh := sum_le (holeArgs (W:=W) s) _ (hole_bound W s)
  have hr := sum_le (relayArgs (W:=W) s) _ (relay_bound W s)
  have ⟨to',tc,th⟩ := TraceBucketFields.costs (W:=W) (fun _ => (0:Fin 1))
  simp only [PhysicalPinsExpr.Formula.binds_compile] at to' tc th
  simp [program,choice_binds,Term.binds_instantiate,PhysicalPinsExpr.Formula.binds_compile,Diagonal.TraceBucketRelay.program,
    Diagonal.TraceBucketRelay.program_work,Term.literal,Term.binds]
  omega

end ThreeFlat.RAM.TraceBucketAtom

end OAI
