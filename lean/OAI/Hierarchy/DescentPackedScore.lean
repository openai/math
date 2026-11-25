import OAI.Hierarchy.DescentSIMDLookup
import OAI.Hierarchy.ProtocolRAMSumScores

namespace OAI
/-! # A single packed-word lookup and native addition per chunk of occurrence scores -/

namespace Hierarchy.DescentPackedScore
open DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure
open ThreeFlat.Routing
open scoped Fin.CommRing Classical BigOperators
noncomputable section
variable {a M H r w : ℕ}

def chunkScore (f : Cell a→ℕ) (key : Cell (a*M)) : ℕ :=
  ∑l : Fin M,f ((encode a M).symm key l)

def terms (f : Cell a→ℕ) (x : Fin H→Fin r→Cell a) (i : Fin (H*chunks r M)) :=
  chunkScore f (data x ((row H r M).symm i))

private theorem sum_padded {R r : ℕ} (le : r≤R) (v : Fin r→ℕ) :
    (∑i : Fin R,if h : i.val<r then v ⟨i.val,h⟩ else 0)=∑j,v j := by
  let e : Fin r↪Fin R := ⟨Fin.castLE le,Fin.castLE_injective le⟩
  let val (i : Fin R) := if h : i.val<r then v ⟨i.val,h⟩ else 0
  have off (i : Fin R) (_ : i∈Finset.univ) (no : i∉Finset.univ.map e) : val i=0 := by
    have gone : ¬i.val<r := fun h=>no (Finset.mem_map.mpr ⟨⟨i.val,h⟩,Finset.mem_univ _,Fin.ext rfl⟩)
    simp [val,gone]
  change (∑i,val i)=_
  rw [←Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) off,Finset.sum_map]
  exact Finset.sum_congr rfl (fun i _=>by simp [e,val,i.isLt])

/-- The incomplete final word of every host contributes its genuine occupied lanes. -/
theorem total (f : Cell a→ℕ) (zero : f 0=0) (x : Fin H→Fin r→Cell a) (positive : 0<M) :
    (∑i,terms (M:=M) f x i)=∑v,∑j,f (x v j) := by
  rw [←(row H r M).sum_comp]
  simp only [terms,Equiv.symm_apply_apply,Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro v _
  let cost (y : Fin (chunks r M*M)) := if h : y.val<r then f (x v ⟨_,h⟩) else 0
  have equal (i : Fin (chunks r M)) (j : Fin M) :
      f ((encode a M).symm (data x (v,i)) j)=cost (finProdFinEquiv (i,j)) := by
    simp only [data,Equiv.symm_apply_apply]
    have index : (finProdFinEquiv (i,j)).val=i.val*M+j.val := by
      change j.val+M*i.val=_;ring
    unfold cost
    simp only [index]
    split <;> simp_all
  change (∑i : Fin (chunks r M),∑j : Fin M,f ((encode a M).symm (data x (v,i)) j))=_
  simp_rw [equal]
  rw [←Fintype.sum_prod_type (f:=fun p : Fin (chunks r M) × Fin M=>cost (finProdFinEquiv p))]
  exact (finProdFinEquiv.sum_comp cost).trans (sum_padded (show r≤chunks r M*M by simpa [chunks,Nat.mul_comm] using CallPool.count_le_batches_mul r M positive) (fun j=>f (x v j)))

def read (src rom : Bank) : Expr := .lookup rom (.lookup src .row)

def raw (src rom : Bank) (out bound H r M w : ℕ) :=
  SumScores.procedure w out (H*chunks r M) bound (read src rom)

structure Input (src rom : Bank) (f : Cell a→ℕ) (x : Fin H→Fin r→Cell a) (m : Memory w) : Prop where
  input : ∀p : Row H r M,m (src.base+(row H r M p).val)=((data x p).val:Word w)
  table : ∀key : Cell (a*M),m (rom.base+key.val)=(chunkScore f key:Word w)

theorem expr_reads (src rom : Bank) (out : ℕ) (f : Cell a→ℕ) (x : Fin H→Fin r→Cell a) (m : Memory w)
    (sf : src.Fits w out) (rf : rom.Fits w out) (rows : H*chunks r M ≤ src.size) (width : rom.bits=a*M)
    (ready : Input (M:=M) src rom f x m) : SumScores.Reads m (read src rom) (terms (M:=M) f x) := by
  intro i
  let p:=(row H r M).symm i
  have first := ready.input p
  rw [show row H r M p=i from (row H r M).apply_symm_apply i] at first
  have address : (data x p).val<rom.size := by simp [Bank.size,width]
  change rom.read m (src.read m (i.val:Word w))=_
  rw [show src.read m (i.val:Word w)=m (src.base+i.val) by
    simp [Bank.read,Fin.val_cast_of_lt ((i.isLt.trans_le rows).trans sf.2.1),Nat.mod_eq_of_lt (i.isLt.trans_le rows)], first]
  rw [show rom.read m ((data x p).val:Word w)=m (rom.base+(data x p).val) by
    simp [Bank.read,Fin.val_cast_of_lt (address.trans rf.2.1),Nat.mod_eq_of_lt address]]
  exact ready.table _

theorem run (src rom : Bank) (out bound : ℕ) (f : Cell a→ℕ) (x : Fin H→Fin r→Cell a) (m : Memory w)
    (zero : f 0=0) (positive : 0<M) (sf : src.Fits w out) (rf : rom.Fits w out)
    (rows : H*chunks r M ≤ src.size) (width : rom.bits=a*M)
    (room : out+(H*chunks r M+1)<2^w) (threshold : bound<2^w) (sumFits : (∑v,∑j,f (x v j))<2^w)
    (ready : Input (M:=M) src rom f x m) :
    (raw src rom out bound H r M w).Exec m
      (fillSegment out (H*chunks r M+1) (SumScores.word out bound (terms (M:=M) f x)) m)
      (4+(H*chunks r M+1)*66) := by
  have scan : (raw src rom out bound H r M w).Spec (fun m=>SumScores.Reads m (read src rom) (terms (M:=M) f x))
      (fun before after=>after=fillSegment out (H*chunks r M+1) (SumScores.word out bound (terms (M:=M) f x)) before)
      (4+(H*chunks r M+1)*(42+2*(read src rom).work)) := SumScores.run out bound (read src rom) (terms (M:=M) f x)
    (show (read src rom).Fits w out from ⟨rf,sf,trivial⟩) room threshold
    (by rw [total f zero x positive];exact sumFits)
  intro P R K machine pc reg pub exit installed params cfg actual entry eqm
  subst actual
  exact scan machine pc reg pub exit installed params cfg m entry (expr_reads src rom out f x m sf rf rows width ready)

theorem flag (out bound : ℕ) (f : Cell a→ℕ) (zero : f 0=0) (x : Fin H→Fin r→Cell a)
    (m : Memory w) (positive : 0<M) :
    fillSegment out (H*chunks r M+1) (SumScores.word out bound (terms (M:=M) f x)) m (out+H*chunks r M)=
      if bound≤∑v,∑j,f (x v j) then 1 else 0 := by
  rw [SumScores.read_flag,total f zero x positive]

theorem zero_check (out : ℕ) (f : Cell a→ℕ) (zero : f 0=0) (x : Fin H→Fin r→Cell a) (m : Memory w) (positive : 0<M) :
    fillSegment out (H*chunks r M+1) (SumScores.word out 1 (terms (M:=M) f x)) m (out+H*chunks r M)=
        if ∀v j,f (x v j)=0 then 0 else 1 := by
  rw [flag out 1 f zero x m positive]
  by_cases h : ∀v j,f (x v j)=0
  · simp [h]
  · have hit : 0<∑v,∑j,f (x v j) := by
      by_contra! no
      have all : ∀v j,f (x v j)=0 := by
        intro v j
        have inner:=Finset.single_le_sum (s:=Finset.univ) (f:=fun j=>f (x v j)) (fun _ _=>Nat.zero_le _) (Finset.mem_univ j)
        have outer:=Finset.single_le_sum (s:=Finset.univ) (f:=fun v=>∑j,f (x v j)) (fun _ _=>Nat.zero_le _) (Finset.mem_univ v)
        omega
      exact h all
    simp [h]

theorem invoice (H r w a : ℕ) (ha : 0<a) (wide : 2*a≤w) :
    (4+(H*chunks r (lanes w a)+1)*66)*w≤70*(w+H*w+4*H*r*a) ∧
      2^(a*lanes w a)≤2^(w/2) := by
  have size:=volume H r w a ha wide
  refine ⟨?_,?_⟩
  · calc
      _ = 70*w+66*(H*chunks r (lanes w a)*w) := by ring
      _ ≤ 70*w+66*(H*w+4*H*r*a) := Nat.add_le_add_left (Nat.mul_le_mul_left 66 size) _
      _ ≤ 70*w+70*(H*w+4*H*r*a) := Nat.add_le_add_left (Nat.mul_le_mul_right _ (by decide : 66≤70)) _
      _ = _ := by ring
  · apply Nat.pow_le_pow_right (by decide)
    simpa [Nat.mul_comm] using lanes_fit w a

end
end Hierarchy.DescentPackedScore

end OAI
