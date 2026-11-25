import OAI.ThreeFlat.Diagonal.RefreshStageDirectory
import OAI.ThreeFlat.RAM.HeaderPipeline
import OAI.ThreeFlat.RAM.PhysicalPinsNat

namespace OAI
/-! # Exact split-shift words read from predecessor adjacency columns -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.MotifRows RefreshDemandRows
open scoped Fin.CommRing

variable {W : ℕ} (current : Word W) (m : Memory W) (vs : Fin 1 → Word W)
set_option quotPrecheck false
local notation "N" => fun i => (m i).val
local notation "U" => fun (i : Fin 1) => (vs i).val
local notation "V" => Formula.natural W (fun _ => 0) N U
local notation "Fit" => Formula.Fits W (fun _ => 0) N U

/-- A closed row descriptor reads its ordinary natural value whenever
the addresses and bitwise operands used by that row fit in the machine. -/
theorem closed_read (f : Formula 1) (ok : Fit f) {answer : ℕ} (read : V f=answer) :
    (closed f).eval Fin.elim0 m vs = (answer : Word W) := by
  rw [eval_closed]
  have h := Formula.value_eq_natural f (fun _=>0) N U ok
  simpa only [Nat.cast_zero,Fin.cast_val_eq_self,read] using h

theorem field_fit (off : ℕ) (header : (m current.val).val+off < 2^W) :
    Fit (field current off) :=
  ⟨⟨⟨trivial,current.isLt⟩,trivial,trivial⟩,header⟩

theorem index_fit (off : ℕ) (header : (m current.val).val+off < 2^W) :
    Fit (index current off) :=
  ⟨trivial,field_fit current m vs off header,(vs 0).isLt,(m _).isLt⟩

theorem split_fit (radix : ℕ) (width : radix<2^W)
    (header : (m current.val).val+12 < 2^W)
    (span : info N current 10+6*info N current 11 ≤ 2^W)
    (lo : info N current 12≤(vs 0).val) (hi : (vs 0).val < info N current 12+3*info N current 11) :
    Fit (splitShifts radix current) := by
  let idx := index current 12
  let len := field current 11
  let r := Formula.op .mod idx len
  let col := Formula.op .div idx len
  have ix := index_fit current m vs 12 header
  have fl := field_fit current m vs 11 (by omega)
  have fi : V idx < 2^W := lt_of_le_of_lt (Nat.sub_le _ _) (vs 0).isLt
  have size : V len < 2^W := (m _).isLt
  have pos : 0 < V len := by change 0< info N current 11; omega
  have rr : Fit r := ⟨ix,fl,fi,size⟩
  have cc : Fit col := ⟨ix,fl,fi,size⟩
  have ir : V r < V len := Nat.mod_lt _ pos
  have ic : V col < 2^W := (Nat.div_le_self ..).trans_lt fi
  have lit1 : 1 < 2^W := lt_of_lt_of_le (by omega : 1 < 6*V len) (by
    change info N current 10+6*V len≤_ at span
    omega)
  have orig (c : ℕ) (hc : c≤5) :
      Fit (readColumn (oldColumn current c) r) := by
    refine ⟨⟨⟨field_fit current m vs 10 (by omega),⟨fl,trivial,trivial⟩,trivial⟩,rr,trivial⟩,?_⟩
    change info N current 10+V len*c+V r < 2^W
    have b := Nat.mul_le_mul_left (V len) hc
    change info N current 10+6*V len≤_ at span
    omega
  have value (c : ℕ) : V (readColumn (oldColumn current c) r)<2^W := (m _).isLt
  let out := readColumn (oldColumn current 2) r
  let rev := readColumn (oldColumn current 5) r
  have front : Fit (.op .div out (.lit radix)) := ⟨orig 2 (by decide),trivial,value 2,width⟩
  have rear : Fit (.op .div rev (.lit radix)) := ⟨orig 5 (by decide),trivial,value 5,width⟩
  have rem : Fit (.op .mod rev (.lit radix)) := ⟨orig 5 (by decide),trivial,value 5,width⟩
  refine ⟨cc,trivial,ic,Nat.two_pow_pos _,?_⟩
  split
  · exact front
  · refine ⟨cc,trivial,ic,lit1,?_⟩
    split <;> assumption

/-- Native modular execution for each one of the three concrete shift
columns, including the reverse source's low port bits. -/
theorem split_native (radix len : ℕ) (p : Fin len) (c : Fin 3)
    (radixFit : radix < 2^W) (header : (m current.val).val+12 < 2^W)
    (hlen : info N current 11=len) (span : info N current 10+6*len ≤ 2^W)
    (address : (vs 0).val=info N current 12+c.val*len+p.val) :
    (closed (splitShifts radix current)).eval Fin.elim0 m vs =
      ((if c.val=2 then
        (m (info N current 10+5*len+p.val)).val%radix else
        (m (info N current 10+(if c.val=0 then 2 else 5)*len+p.val)).val/radix : ℕ) : Word W) := by
  apply closed_read m vs
  · apply split_fit current m vs radix radixFit header
    · simpa only [hlen] using span
    · omega
    · have room : (c.val+1)*len≤3*len := Nat.mul_le_mul_right len c.isLt
      rw [Nat.add_mul,one_mul] at room
      have bit := p.isLt
      omega
  · have h := split_read current (fun _=>0) N U radix len p c hlen address
    fin_cases c <;> simpa using h

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
