import OAI.ThreeFlat.Diagonal.RefreshSplitNative
import OAI.ThreeFlat.Diagonal.RefreshDenseAddress
import OAI.ThreeFlat.Diagonal.RefreshWidthPhysical

namespace OAI
/-! # Canonical block-major sparse output words after a refresh -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalPinsExpr RAM.MotifRows
open RefreshDemandRows RefreshTies CompressorPacking.Native
open scoped Fin.CommRing BigOperators

variable {W v t m h pad : ℕ} (current : Word W) (memory : Memory W) (regs : Fin 1 → Word W)
set_option quotPrecheck false

local notation "N" => fun i => (memory i).val
local notation "U" => fun (i : Fin 1) => (regs i).val
local notation "V" => Formula.natural W (fun _ => 0) N U
local notation "Fit" => Formula.Fits W (fun _ => 0) N U

def sparseSlot (z : Block v t) (p : Fin m) (s : Fin h) : LiveSlot (Fin v) (BitWord t) m (1+h+pad) :=
  (((z.1,p),⟨1+s.val,by omega⟩),z.2)

private theorem digits (q : ℕ) {j : ℕ} (i : Fin j) :
    (q*j+i.val)/j=q ∧ (q*j+i.val)%j=i.val := by
  constructor
  · rw [Nat.mul_comm q,Nat.mul_add_div (Nat.zero_lt_of_lt i.isLt),Nat.div_eq_of_lt i.isLt,Nat.add_zero]
  · rw [Nat.mul_comm q,Nat.mul_add_mod,Nat.mod_eq_of_lt i.isLt]

theorem sparse_native (z : Block v t) (p : Fin m) (s : Fin h)
    (head : (memory current.val).val+19<2^W) (mf : m<2^W) (hf : h<2^W)
    (remain : info N current 8=2^t)
    (pos : (regs 0).val=info N current 3+(blockId z*m+p.val)*h+s.val)
    (physical : info N current 19 + v*m*(1+h+pad)*2^t≤2^W) :
    (closed (sparseCopy m h pad current)).eval Fin.elim0 memory regs =
      memory (info N current 19 + nextIndex (sparseSlot (pad:=pad) z p s)) := by
  let i := index current 3
  let atPort := Formula.op .div i (.lit h)
  let block := Formula.op .div atPort (.lit m)
  let lanes := field current 8
  have ix : V i=(blockId z*m+p.val)*h+s.val := by change (regs 0).val-info N current 3=_; omega
  have fI : Fit i := index_fit current memory regs _ (by omega)
  have bI : V i < 2^W := (Nat.sub_le _ _).trans_lt (regs 0).isLt
  have fA : Fit atPort := ⟨fI,trivial,bI,hf⟩
  have bA : V atPort<2^W := (Nat.div_le_self ..).trans_lt bI
  have fB : Fit block := ⟨fA,trivial,bA,mf⟩
  have bB : V block<2^W := (Nat.div_le_self ..).trans_lt bA
  have fl : Fit lanes := field_fit current memory regs _ (by omega)
  have bl : V lanes<2^W := (memory _).isLt
  have dl : Fit (.op .div block lanes) := ⟨fB,fl,bB,bl⟩
  have ml : Fit (.op .mod block lanes) := ⟨fB,fl,bB,bl⟩
  have cp : Fit (.op .mod atPort (.lit m)) := ⟨fA,trivial,bA,mf⟩
  have cs : Fit (.op .mod i (.lit h)) := ⟨fI,trivial,bI,hf⟩
  let e := sparseSlot (pad:=pad) z p s
  have address : V (field current 19)+
      ((V block/V lanes*m+V atPort%m)*(1+h+pad)+(1+V i%h))*V lanes+V block%V lanes =
      info N current 19+nextIndex e := by
    have q := digits (blockId z*m+p.val) s
    have r := digits (blockId z) p
    have l := digits z.1.val (tagOrdinal t z.2)
    change V lanes=2^t at remain
    have aa : V atPort=blockId z*m+p.val := by change V i/h=_; rw [ix,q.1]
    have bb : V block=blockId z := by change V atPort/m=_; rw [aa,r.1]
    change blockId z/2^t=z.1.val ∧ blockId z%2^t=(tagOrdinal t z.2).val at l
    rw [bb,aa,ix,remain,r.2,q.2,l.1,l.2]
    dsimp [e,sparseSlot,nextIndex,field_read]
    omega
  have addrFits : V (field current 19)+
      (((V block/V lanes*m+V atPort%m)*(1+h+pad)+(1+V i%h))*V lanes+V block%V lanes)<2^W := by
    have b := nextIndex_lt e
    omega
  rw [←Fin.cast_val_eq_self (memory (info N current 19+nextIndex e))]
  apply closed_read memory regs
  · refine ⟨⟨field_fit current memory regs 19 head,⟨⟨⟨⟨⟨⟨dl,trivial,trivial⟩,cp,trivial⟩,
      trivial,trivial⟩,⟨trivial,cs,trivial⟩,trivial⟩,fl,trivial⟩,ml,trivial⟩,trivial⟩,addrFits⟩
  · change (memory (V (field current 19)+
      (((V block/V lanes*m+V atPort%m)*(1+h+pad)+(1+V i%h))*V lanes+V block%V lanes))).val=_
    congr 2
    omega

theorem sparse_width (c : Fin m → Fin m → ℕ) (rows : ∀ i,∑ j,c i j=h)
    (w : RefreshTies.Address (Fin v × BitWord t) m → ℕ)
    (sp : Block v t → Expander.Arc c → ℕ) (z : Block v t) (p : Fin m) (s : Fin h) :
    freshWidth c rows (termWidth c w sp) pad (sparseSlot z p s)=sp z ((numbering c rows).symm (p,s)) := by
  rw [←numbered_width_eq]
  change numberedWidth p (1+s.val) _ _=_
  have sub : 1+s.val-1=s.val := by omega
  simp [numberedWidth,sub,s.isLt,sparseSlot]

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
