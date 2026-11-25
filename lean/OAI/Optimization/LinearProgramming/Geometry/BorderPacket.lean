import OAI.Optimization.LinearProgramming.Geometry.BorderPacketColumns
import OAI.Optimization.LinearProgramming.Geometry.BorderPacketHeader
import OAI.Optimization.LinearProgramming.Geometry.BorderWire
import OAI.Optimization.LinearProgramming.Geometry.PowerRAM

/-! Decode what the fixed prefix-minor request writer actually leaves on the request tape. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Block Matrix Contraction.Machine

variable {r s n k : ℕ}

theorem columnNumbers_of_tape (m : Memory ℚ) (J : Fin k → Fin n) (j : Fin n)
    (hk : m.index 128=k) (hj : m.index 90=j.val)
    (hJ : ∀ i : Fin k, m.index (m.index 136+i.val)=(J i).val) :
    columnNumbers m n = ((List.finRange n).filter fun t => t ∈ (prefixMinorKey J j).2).map Fin.val := by
  have hnum : (List.finRange n).map Fin.val = List.range n := by apply List.ext_getElem <;> simp
  unfold columnNumbers
  rw [← hnum,List.filter_map]
  congr 2
  funext u
  apply Bool.eq_iff_iff.mpr
  change selected m u.val = true ↔ decide (u ∈ (prefixMinorKey J j).2) = true
  rw [selected_iff,hj,hk,decide_eq_true_eq]
  simp only [prefixMinorKey,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro (he | ⟨a,ha,he⟩)
    · exact Or.inl (Fin.ext he.symm)
    · exact Or.inr ⟨⟨a,ha⟩,Fin.ext ((hJ ⟨a,ha⟩).symm.trans he)⟩
  · rintro (rfl | ⟨a,he⟩)
    · exact Or.inl rfl
    · exact Or.inr ⟨a.val,a.isLt,(hJ a).trans (congrArg Fin.val he)⟩

/-- Emit a complete comparator-compatible request at the designated contiguous tape. -/
def packetBlock : Block := .seq BorderPacketHeader.block columnsBlock

structure PacketOutput (m t : Memory ℚ) (J : Fin k → Fin n) (j : Fin n) (base : ℕ) : Prop where
  source : t.index 80=base
  destination : t.index 82=base
  message : registerPacket (t.atPC 0) 80 81=(prefixWords J j).map Nat.cast
  data (p) : 2 ≤ p → (p<30 ∨ 31<p) → p < base → t.data p=m.data p
  index (p) : p≠80 → p≠81 → p≠82 → (p<91 ∨ 99<p) → t.index p=m.index p

private theorem header_get (i k : ℕ) (hi : i<k+3) :
    ([0,k+1]++List.range (k+1))[i]'(by simp; omega) =
    if i=0 then 0 else if i=1 then k+1 else i-2 := by
  rcases i with _ | i
  · simp
  rcases i with _ | i
  · simp
  · simp

/-- The writer preserves a signed raw value and its price in scalars 27 and 28, the
scan cursors in address registers 84–90, and complete arrays below the packet scratch. -/
theorem packetBlock_eval (m : Memory ℚ) (P : ℚ → Prop) (J : Fin k → Fin n) (j : Fin n)
    (base : ℕ) (hk : m.index 128=k) (hn : m.index 130=n) (hj : m.index 90=j.val)
    (hp : m.index 144=base) (hbase : 256 ≤ base) (hpiv : 128 ≤ m.index 136)
    (hJ : ∀ i : Fin k, m.index (m.index 136+i.val)=(J i).val)
    (hkn : k+1 ≤ n) (hm : ∀ a,P (m.data a)) (hnum : ∀ a ≤ n,P (a:ℚ)) :
    ∃ t cost, cost ≤ 6*k+26+n*(8*k+16) ∧ Eval (fun u => ∀ a,P (u.data a)) packetBlock m cost t ∧
      PacketOutput m t J j base := by
  obtain ⟨b,eb,bo⟩ := BorderPacketHeader.run_block m k base hk hp hbase P hm (fun a h => hnum a (h.trans hkn))
  obtain ⟨bs,bf⟩ := eb.safe_end
  have bi (a : ℕ) (ha : a<80 ∨ (82<a ∧ a<96) ∨ 99<a) : b.index a=m.index a :=
    bf.index a (by unfold BorderPacketHeader.addressScratch; omega)
  have bk := (bi 128 (by decide)).trans hk
  have bn := (bi 130 (by decide)).trans hn
  have bp := bi 136 (by decide)
  have bb := bo.cursor
  obtain ⟨t,c,hc,ec,o⟩ := columnsBlock_eval b P bs (by rw [bp]; exact hpiv)
    (by rw [bb]; omega) (fun a ha => hnum a (bn ▸ ha)) (by simpa using hnum 1 (by omega))
  have bJ (i : Fin k) : b.index (b.index 136+i.val)=(J i).val := by rw [bp,bi _ (by omega),hJ]
  have nums := columnNumbers_of_tape b J j bk ((bi 90 (by decide)).trans hj) bJ
  let head := [0,k+1]++List.range (k+1)
  let cols := columnNumbers b n
  have headSize : head.length=k+3 := by simp [head]
  have allWords : prefixWords J j = head++cols := congrArg (head++·) nums.symm
  have src := (o.addressFrame 80 (by decide) (by decide)).trans bo.packet
  have dst := (o.addressFrame 82 (by decide) (by decide)).trans bo.start
  have size : t.index 81=head.length+cols.length := by simp [o.length,bo.length,headSize,bn,cols]
  refine ⟨t,6*k+21+c,by rw [bk,bn] at hc; omega,(PowerRAM.weaken eb (fun _ h => h.1)).seq ec,src,dst,?_,?_,?_⟩
  · apply List.ext_getElem
    · simp [registerPacket,Memory.atPC,allWords,size]
    · intro i hi _
      simp only [registerPacket,List.getElem_ofFn,Memory.atPC,allWords,List.getElem_map]
      rw [src]
      by_cases h : i<head.length
      · have a : base+i < b.index 96 := by rw [bb]; omega
        rw [o.scalarFrame (base+i) (Or.inr (by omega)) (Or.inl a),List.getElem_append_left h]
        have he := bo.word i (headSize ▸ h)
        simpa only [head,header_get i k (headSize ▸ h),Nat.cast_ite,Nat.cast_zero] using he
      · have size' : i<head.length+cols.length := by simpa [registerPacket,Memory.atPC,size] using hi
        have hq : i-head.length < (columnNumbers b (b.index 130)).length := by rw [bn]; change i-head.length<cols.length; omega
        have a : base+i = b.index 96+(i-head.length) := by rw [bb,headSize]; omega
        rw [a,o.words ⟨_,hq⟩,List.getElem_append_right (by omega : head.length ≤ i)]
        simp [cols,bn]
  · intro q hq htemp hbefore
    exact (o.scalarFrame q htemp (Or.inl (by rw [bb]; omega))).trans (bf.data q hq (Or.inl hbefore))
  · intro q q80 q81 q82 qrange
    exact (o.addressFrame q q81 (by omega)).trans (bi q (by omega))

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
