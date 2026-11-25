import OAI.Optimization.LinearProgramming.RAM.CallablePrepareBase

/-! Counted address arithmetic for the persistent symbolic-workspace allocator. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM RAM.Callable

def addAddressLoop (dest cursor count scale : ℕ) : Block :=
  .forRange cursor count (bumpIndex dest scale)

structure AddressLoopPost {K : Type*} (m t : Memory K) (dest cursor count scale : ℕ) : Prop where
  data : t.data=m.data
  value : t.index dest=m.index dest+m.index count*scale
  frame : ∀ i, i ≠ dest → i ≠ cursor → t.index i=m.index i

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

theorem addAddressLoop_eval (m : Memory K) (dest cursor count scale : ℕ) (hm : m.AllData P)
    (dc : dest ≠ cursor) (ds : count ≠ dest) (cs : count ≠ cursor) :
    ∃ t, Block.Eval (Memory.AllData P) (addAddressLoop dest cursor count scale) m
      (m.index count*(scale+3)+2) t ∧ AddressLoopPost m t dest cursor count scale := by
  let I (j : ℕ) (s : Memory K) := s.data=m.data ∧ s.index cursor=j ∧
    s.index dest=m.index dest+j*scale ∧ ∀ i, i ≠ dest → i ≠ cursor → s.index i=m.index i
  have start : I 0 (m.putIndex cursor 0) := by
    refine ⟨rfl,Memory.putIndex_same ..,?_,fun i _ hi => Memory.putIndex_ne _ hi _⟩
    simpa using Memory.putIndex_ne m dc 0
  obtain ⟨t,run,hd,_,hv,hf⟩ := Block.Eval.forRange_invariant_exact
    (safe := Memory.AllData P) (body := bumpIndex dest scale) cursor count (m.index count) scale I m hm start
    (fun _ s hs => ⟨fun k => by rw [hs.1]; exact hm k,hs.2.1,hs.2.2.2 count ds cs⟩) (by
      intro j _ s hs
      obtain ⟨hd,hj,hval,frame⟩ := hs
      have safe : s.AllData P := fun k => by rw [hd]; exact hm k
      let v := s.putIndex dest (s.index dest+scale)
      have e := bumpIndex_spec s dest scale safe
      have cur : v.index cursor=j := (Memory.putIndex_ne _ dc.symm _).trans hj
      refine ⟨v,e,hd,by rw [Memory.putIndex_same,cur],?_,?_⟩
      · rw [Memory.putIndex_ne _ dc]
        change (s.putIndex dest _).index dest = _
        rw [Memory.putIndex_same,hval,Nat.succ_mul]
        omega
      · intro i hd' hc'
        exact (Memory.putIndex_ne _ hc' _).trans ((Memory.putIndex_ne _ hd' _).trans (frame i hd' hc')))
  exact ⟨t,run,hd,hv,hf⟩

/-- Per outer iteration the address moves by `10+4*fuel`. The outer count is
`n+1` from 71, and the fixed fuel header is 84. -/
def addSymbolicTokenSpan : Block :=
  .forRange 70 71 (.seq (bumpIndex 90 10) (addAddressLoop 90 72 84 4))

theorem addSymbolicTokenSpan_eval (m : Memory K) (hm : m.AllData P) :
    ∃ t, Block.Eval (Memory.AllData P) addSymbolicTokenSpan m
      (m.index 71*(7*m.index 84+15)+2) t ∧
      t.data=m.data ∧ t.index 90=m.index 90+m.index 71*(10+4*m.index 84) ∧
      ∀ i, i ≠ 70 → i ≠ 72 → i ≠ 90 → t.index i=m.index i := by
  let I (j : ℕ) (s : Memory K) := s.data=m.data ∧ s.index 70=j ∧
    s.index 90=m.index 90+j*(10+4*m.index 84) ∧
    ∀ i, i ≠ 70 → i ≠ 72 → i ≠ 90 → s.index i=m.index i
  have start : I 0 (m.putIndex 70 0) := by
    refine ⟨rfl,Memory.putIndex_same ..,by simp,fun i hi _ _ => Memory.putIndex_ne _ hi _⟩
  obtain ⟨t,run,hd,_,hv,hf⟩ := Block.Eval.forRange_invariant_exact (safe := Memory.AllData P)
    (body := .seq (bumpIndex 90 10) (addAddressLoop 90 72 84 4)) 70 71 (m.index 71)
    (10+(m.index 84*(4+3)+2)) I m hm start
    (fun _ s hs => ⟨fun k => by rw [hs.1];exact hm k,hs.2.1,hs.2.2.2 71 (by decide) (by decide) (by decide)⟩)
    (by
      intro j _ s hs
      obtain ⟨hd,hj,h90,keep⟩ := hs
      have safe : s.AllData P := fun k => by rw [hd]; exact hm k
      let v := s.putIndex 90 (s.index 90+10)
      have fuel : v.index 84=m.index 84 := (Memory.putIndex_ne _ (by decide : 84 ≠ 90) _).trans
        (keep 84 (by decide) (by decide) (by decide))
      obtain ⟨u,inner,after⟩ := addAddressLoop_eval v 90 72 84 4 (show v.AllData P from safe)
        (by decide) (by decide) (by decide)
      rw [fuel] at inner
      have c70 : u.index 70=j := (after.frame 70 (by decide) (by decide)).trans
        ((Memory.putIndex_ne _ (by decide : 70 ≠ 90) _).trans hj)
      have v90 : v.index 90=s.index 90+10 := Memory.putIndex_same ..
      have next : u.index 90=m.index 90+(j+1)*(10+4*m.index 84) := calc
        u.index 90 = v.index 90+v.index 84*4 := after.value
        _ = (s.index 90+10)+m.index 84*4 := by rw [v90,fuel]
        _ = m.index 90+(j+1)*(10+4*m.index 84) := by rw [h90]; ring
      refine ⟨u,(bumpIndex_spec s 90 10 safe).seq inner,after.data.trans hd,by rw [Memory.putIndex_same,c70],?_,?_⟩
      · exact (Memory.putIndex_ne _ (by decide : 90 ≠ 70) _).trans next
      · intro i h70 h72 h90'
        exact (Memory.putIndex_ne _ h70 _).trans ((after.frame i h90' h72).trans
          ((Memory.putIndex_ne _ h90' _).trans (keep i h70 h72 h90'))))
  have clock : 10+(m.index 84*(4+3)+2)+3=7*m.index 84+15 := by ring
  rw [clock] at run
  exact ⟨t,run,hd,hv,hf⟩

end Compression
end LinearProgramming
end Optimization
end OAI
