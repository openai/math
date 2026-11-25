import OAI.ThreeFlat.Diagonal.RefreshSplitNative
import OAI.ThreeFlat.Diagonal.SlotImageViews
import OAI.ThreeFlat.RAM.SweepSegment

namespace OAI
/-! # The first refresh scan materializes all three separated shift columns -/

namespace ThreeFlat.Diagonal.RefreshStageNav

open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.DescriptorScan CompressorPacking.Native
open scoped Fin.CommRing

variable {W v a : ℕ} (current : Word W) (initial : Memory W)
local notation "N" => fun i => Fin.val (initial i)

/-- Row evaluator for the actual first stage procedure, with no graph oracle. -/
def separated (m : Memory W) (C : SlotImage.Columns) (split radix x : ℕ) : Word W :=
  let i := x-split
  let c := i/C.rows
  let p := i%C.rows
  let z := (m (C.graph+(if c=0 then 2 else 5)*C.rows+p)).val
  ((if c=2 then z%radix else z/radix : ℕ) : Word W)

private theorem separated_row (m : Memory W) (C : SlotImage.Columns) (split radix : ℕ)
    (p : Fin C.rows) (c : Fin 3) :
    separated m C split radix (split+c.val*C.rows+p.val)=
      ((if c.val=2 then (m (C.graph+5*C.rows+p.val)).val%radix else
        (m (C.graph+(if c.val=0 then 2 else 5)*C.rows+p.val)).val/radix : ℕ) : Word W) := by
  have lo : split+c.val*C.rows+p.val-split=c.val*C.rows+p.val := by omega
  have q : (c.val*C.rows+p.val)/C.rows=c.val := by
    rw [Nat.mul_comm c.val,Nat.mul_add_div (Nat.zero_lt_of_lt p.isLt),Nat.div_eq_of_lt p.isLt,Nat.add_zero]
  have r : (c.val*C.rows+p.val)%C.rows=p.val := by
    rw [Nat.mul_comm c.val,Nat.mul_add_mod,Nat.mod_eq_of_lt p.isLt]
  simp only [separated,lo,q,r]
  fin_cases c <;> rfl

theorem split_run (C : SlotImage.Columns) (split radix : ℕ) (radixFit : radix<2^W)
    (header : (initial current.val).val+13<2^W)
    (g : info N current 10=C.graph) (r : info N current 11=C.rows)
    (s : info N current 12=split) (n : info N current 13=3*C.rows)
    (graphCap : C.graph+6*C.rows≤2^W) (splitCap : split+3*C.rows<2^W)
    (protect : ∀ i, (i=current.val ∨ (initial current.val).val≤ i ∧ i≤(initial current.val).val+13 ∨
      C.graph≤ i ∧ i<C.graph+6*C.rows) → i<split ∨ split+3*C.rows≤ i) :
    (Pipeline.scan current 12 13 (closed (splitShifts radix current))).run initial =
      fillSegment split (3*C.rows) (separated initial C split radix) initial := by
  let lo := headerWord initial current 12
  let count := headerWord initial current 13
  have hword (off : ℕ) (h : off≤13) : (headerWord initial current off).val=info N current off := by
    change (initial (initial current.val+(off:Word W)).val).val=(initial ((initial current.val).val+off)).val
    have address : (initial current.val+(off:Word W)).val=(initial current.val).val+off := by
      calc
        _ = (((((initial current.val).val+off : ℕ) : Word W))).val := by
          rw [Nat.cast_add,Fin.cast_val_eq_self]
        _ = _ := Fin.val_cast_of_lt (by omega)
    exact congrArg (fun a=>(initial a).val) address
  have hl : lo.val=split := (hword 12 (by decide)).trans s
  have hc : count.val=3*C.rows := (hword 13 (by decide)).trans n
  change sweep _ count.val lo initial=_
  rw [hc]
  calc
    _ = fillSegment lo.val (3*C.rows) (separated initial C split radix) initial := by
      apply sweep_segment _ split (split+3*C.rows) initial _ _ lo _ initial
        (le_of_eq hl.symm) (by omega) splitCap (fun _ _=>rfl)
      intro b lb ub m frame
      let i := b.val-split
      have ir : i<3*C.rows := by dsimp [i]; omega
      have rowPos : 0<C.rows := by omega
      let c : Fin 3 := ⟨i/C.rows,(Nat.div_lt_iff_lt_mul rowPos).mpr ir⟩
      let p : Fin C.rows := ⟨i%C.rows,Nat.mod_lt _ rowPos⟩
      have pos : b.val=split+c.val*C.rows+p.val := by
        have dec := Nat.div_add_mod i C.rows
        rw [Nat.mul_comm C.rows] at dec
        change b.val=split+(i/C.rows)*C.rows+i%C.rows
        have lb' : split+i=b.val := by dsimp [i]; omega
        omega
      have key : m current.val=initial current.val := frame _ (protect _ (Or.inl rfl))
      have head (off : ℕ) (h : off≤13) :
          info (fun z=>(m z).val) current off=info N current off := by
        dsimp only [info]
        rw [key,frame _ (protect _ (Or.inr (Or.inl ⟨by omega,by omega⟩)))]
      have old (k : ℕ) (hk : k≤5) :
          m (C.graph+k*C.rows+p.val)=initial (C.graph+k*C.rows+p.val) := by
        apply frame _ (protect _ (Or.inr (Or.inr ⟨by omega,?_⟩)))
        have bound := Nat.mul_le_mul_right C.rows hk
        omega
      have native := split_native current m (fun _=>b) radix C.rows p c radixFit
        (by rw [key]; omega) ((head 11 (by decide)).trans r) (by rw [head 10 (by decide),g]; exact graphCap)
        (by rw [head 12 (by decide),s,pos])
      rw [native,pos,separated_row]
      simp only [head 10 (by decide),g,old 5 (by decide),old (if c.val=0 then 2 else 5) (by split <;> decide)]
    _ = _ := by rw [hl]

open Computability.VPVNP.Compression in
/-- A materialized image supplies all three hypotheses on the low and high
parts of old shifts required by the refresh choice and graph programs. -/
theorem split_image {t : ℕ} {G : Computability.VPVNP.Compression.LiftedSlots (Fin v) (2^a) (BitWord a × BitWord t)}
    {C : SlotImage.Columns} {w : SlotImage.RefreshInput v a t → ℕ} {split : ℕ}
    (image : SlotImage.Stored G (Equiv.refl _) (SlotImage.pairLane (tagOrdinal a) (tagOrdinal t)) C N w)
    (apart : ∀ i, C.graph≤ i → i<C.graph+6*C.rows → i<split ∨ split+3*C.rows≤ i) :
    let o := fillSegment split (3*C.rows) (separated initial C split (2^a)) initial
    SlotImage.SplitColumns C split (fun z=>(o z).val) v a := by
  intro o
  have old (p : Fin v × Fin (2^a)) (b : Bool) :
      o (SlotImage.cell C (Equiv.refl _) p b 2)=initial (SlotImage.cell C (Equiv.refl _) p b 2) := by
    let atCell:=SlotImage.cell C (Equiv.refl (Fin v)) p b 2
    obtain ⟨l,h⟩:=SlotImage.cell_range (base:=Equiv.refl (Fin v)) image p b 2
    have disjoint:=apart atCell l h
    change (if split≤atCell ∧ atCell<split+3*C.rows then _ else _)=_
    rw [ite_eq_right (by omega : ¬(split≤atCell ∧ atCell<split+3*C.rows))]
  have val (p : Fin v × Fin (2^a)) (c : Fin 3) :
      o (split+c.val*C.rows+SlotImage.ordinal (Equiv.refl _) p) =
      ((if c.val=2 then (initial (C.graph+5*C.rows+SlotImage.ordinal (Equiv.refl _) p)).val%2^a
        else (initial (C.graph+(if c.val=0 then 2 else 5)*C.rows+SlotImage.ordinal (Equiv.refl _) p)).val/2^a
        : ℕ) : Word W) := by
    let j : Fin C.rows := ⟨SlotImage.ordinal (Equiv.refl _) p,by rw [image.rowCount]; exact SlotImage.ordinal_lt _ _⟩
    have b := Nat.mul_le_mul_right C.rows c.isLt
    rw [Nat.succ_mul] at b
    change fillSegment _ _ _ _ (split+c.val*C.rows+j.val)=_
    rw [fillSegment,ite_eq_left ⟨by omega,by omega⟩,separated_row initial C split (2^a) j c]
  have divFit (x : Word W) : x.val/2^a<2^W := (Nat.div_le_self ..).trans_lt x.isLt
  have modFit (x : Word W) : x.val%2^a<2^W := (Nat.mod_le ..).trans_lt x.isLt
  constructor
  · intro p
    rw [old p false]
    simpa [SlotImage.cell,SlotImage.column,Fin.val_cast_of_lt (divFit _),Nat.mul_comm C.rows 2]
      using congrArg Fin.val (val p 0)
  · intro p
    rw [old p true]
    simpa [SlotImage.cell,SlotImage.column,Fin.val_cast_of_lt (divFit _),Nat.mul_comm C.rows 5]
      using congrArg Fin.val (val p 1)
  · intro p
    rw [old p true]
    simpa [SlotImage.cell,SlotImage.column,Fin.val_cast_of_lt (modFit _),Nat.mul_comm C.rows 5,Nat.mul_comm C.rows 2]
      using congrArg Fin.val (val p 2)

end ThreeFlat.Diagonal.RefreshStageNav

end OAI
