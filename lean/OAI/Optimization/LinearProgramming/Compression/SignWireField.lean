import OAI.Optimization.LinearProgramming.NativePrice.NatRAM
import OAI.Optimization.LinearProgramming.Lattice.QueryWire

/-! Reading the canonical signed integer fields used by the lattice sign
oracle. All bits are ordinary scalar zeroes or ones in consecutive cells. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace SignWire
open RAM NativePrice OracleSpec

def fieldWord (z : ℤ) : Word := decide (z < 0) :: encodeNat z.natAbs

/-- Address 3 is the bit cursor. Scalar register 8 is zero, and scalar
register 7 saves the sign while the framed magnitude is read. -/
def signedFieldBlock : Block :=
  .seq (.straight [.load 7 3,.incr 3 3]) (.seq natBlock
    (.branch (.scalarLT 8 7) (.op (.sub 3 8 3)) .skip))

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem signedFieldBlock_spec (P : K → Prop) (z : ℤ) (m : Memory K) (c : ℕ)
    (hm : m.AllData P) (hc : m.index 3=c) (hbase : 9 ≤ c) (hzero : m.data 8=0)
    (hw : WordAt m c (fieldWord z)) (hP : ∀ v : ℕ, v ≤ 2^z.natAbs.bits.length → P (v:K))
    (hz : P (z:K)) :
    ∃ s steps, steps ≤ 16*(fieldWord z).length+8 ∧ Block.Eval (Memory.AllData P) signedFieldBlock m steps s ∧
      s.data 3=(z:K) ∧ s.index 3=c+(fieldWord z).length ∧
      (∀ i, i < 3 ∨ 7 < i → s.data i=m.data i) ∧
      (∀ i, i < 3 ∨ 6 < i → s.index i=m.index i) := by
  obtain ⟨signBit,mag⟩ := wordAt_cons.mp hw
  let u := m.putData 7 (m.data (m.index 3))
  let v := u.putIndex 3 (u.index 3+1)
  have hu : u.AllData P := hm.putData _ (hm _)
  have hv : v.AllData P := hu
  have eu := Block.Eval.op_load m 7 3 hm hu
  have ev := Block.Eval.op_incr u 3 3 hu hv
  have hmag : WordAt v (c+1) (encodeNat z.natAbs) := mag.of_data (by
    intro i hlo _; simp [v,u,show i ≠ 7 by omega])
  obtain ⟨t,k,hk,et,mt,cursor,td,ti⟩ := natBlock_spec P z.natAbs v (c+1)
    (by simp [v,u,hc]) (by omega) hmag hv hP
  have h8 : t.data 8=0 := by simpa [v,u] using (td 8 (by decide)).trans hzero
  have h7 : t.data 7=((decide (z < 0)).toNat:K) := by
    simpa [v,u,hc] using (td 7 (by decide)).trans (by simpa [v,u,hc] using signBit)
  have finish : ∃ s j, j ≤ 3 ∧ Block.Eval (Memory.AllData P)
      (.branch (.scalarLT 8 7) (.op (.sub 3 8 3)) .skip) t j s ∧ s.data 3=(z:K) ∧
      (∀ i, i ≠ 3 → s.data i=t.data i) ∧ s.index=t.index := by
    by_cases hn : z < 0
    · have hab : (z.natAbs:K)=-(z:K) := by
        simpa only [Int.cast_natCast,Int.cast_neg] using
          congrArg (fun x : ℤ => (x:K)) (Int.ofNat_natAbs_of_nonpos hn.le)
      have value : t.data 8-t.data 3=(z:K) := by rw [h8,mt,hab];ring
      let s := t.putData 3 (t.data 8-t.data 3)
      have hs : s.AllData P := et.safe_end.putData _ (value ▸ hz)
      have cond : (Cond.scalarLT 8 7).test t=true := by simp [Cond.test,h8,h7,hn]
      refine ⟨s,3,le_rfl,Block.Eval.branchTrue (k:=1) cond (Block.Eval.op_sub t 3 8 3 et.safe_end hs),
        by simpa [s] using value,?_,rfl⟩
      intro i hi; simp [s,hi]
    · have hab : (z.natAbs:K)=(z:K) := by
        simpa only [Int.cast_natCast] using congrArg (fun x : ℤ => (x:K))
          (Int.natAbs_of_nonneg (le_of_not_gt hn))
      have cond : (Cond.scalarLT 8 7).test t=false := by simp [Cond.test,h8,h7,hn]
      exact ⟨t,1,by decide,Block.Eval.branchFalse (k:=0) cond (.skip et.safe_end),
        mt.trans hab,fun _ _ => rfl,rfl⟩
  obtain ⟨s,j,hj,ef,val,fd,fi⟩ := finish
  refine ⟨s,2+(k+j),?_,(eu.seq (ev.seq (.skip hv))).seq (et.seq ef),val,?_,?_,?_⟩
  · simp only [fieldWord,List.length_cons];omega
  · rw [fi,cursor];simp only [fieldWord,List.length_cons];omega
  · intro i hi
    rw [fd _ (by omega),td _ (by omega)]
    simp [v,u,show i ≠ 7 by omega]
  · intro i hi
    rw [fi,ti _ hi]
    simp [v,u,show i ≠ 3 by omega]

end SignWire
end Compression
end LinearProgramming
end Optimization
end OAI
