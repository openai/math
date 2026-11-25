import OAI.Optimization.LinearProgramming.Geometry.VMPacketPhysical
import OAI.Optimization.LinearProgramming.RAM.CallableOddBase
import OAI.Optimization.LinearProgramming.RAM.CallableBase
import OAI.Optimization.LinearProgramming.BitRAM.PacketLayout

/-! Transfer a BitRAM query to the isolated geometry machine at logical address 256,
retaining the nested minor machine exactly and reconstructing both encoded address banks. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace VMPacketCopy

open RAM RAM.Callable OracleSpec

private abbrev banks {K : Type} (minor geom vm : Memory K) := Odd.memory (Odd.memory minor geom) vm

private theorem vmDataAt {K : Type} (minor geom vm : Memory K) (j : ℕ) :
    (banks minor geom vm).data (2*j+1)=vm.data j := Odd.data_slot ..

private theorem vmIndexAt {K : Type} (minor geom vm : Memory K) (j : ℕ) :
    (banks minor geom vm).index (2*j+1)=2*vm.index j+1 := Odd.index_slot ..

private theorem geoDataAt {K : Type} (minor geom vm : Memory K) (j : ℕ) :
    (banks minor geom vm).data (4*j+2)=geom.data j := by
  change (Odd.memory (Odd.memory minor geom) vm).data _=_
  rw [show 4*j+2=2*Odd.slot j by unfold Odd.slot; omega,Odd.data_even,Odd.data_slot]

private theorem geoIndexAt {K : Type} (minor geom vm : Memory K) (j : ℕ) :
    (banks minor geom vm).index (4*j+2)=4*geom.index j+2 := by
  change (Odd.memory (Odd.memory minor geom) vm).index _=_
  rw [show 4*j+2=2*Odd.slot j by unfold Odd.slot; omega,Odd.index_even,Odd.index_slot]
  unfold Odd.slot
  omega

private theorem minDataAt {K : Type} (minor geom vm : Memory K) (j : ℕ) :
    (banks minor geom vm).data (4*j)=minor.data j := by
  change (Odd.memory (Odd.memory minor geom) vm).data _=_
  rw [show 4*j=2*(2*j) by omega,Odd.data_even,Odd.data_even]

private theorem minIndexAt {K : Type} (minor geom vm : Memory K) (j : ℕ) :
    (banks minor geom vm).index (4*j)=4*minor.index j := by
  change (Odd.memory (Odd.memory minor geom) vm).index _=_
  rw [show 4*j=2*(2*j) by omega,Odd.index_even,Odd.index_even]
  omega

private theorem residues (P : ℕ → Prop) (minor : ∀ j, P (4*j)) (geom : ∀ j, P (4*j+2))
    (vm : ∀ j, P (2*j+1)) (q : ℕ) : P q := by
  by_cases odd : q%2=1
  · exact (show 2*(q/2)+1=q by omega) ▸ vm (q/2)
  by_cases zero : q%4=0
  · exact (show 4*(q/4)=q by omega) ▸ minor (q/4)
  exact (show 4*(q/4)+2=q by omega) ▸ geom (q/4)

private theorem memory_ext {K : Type} {s t : Memory K} (hd : ∀j,s.data j=t.data j)
    (hi : ∀j,s.index j=t.index j) : s=t := by
  cases s
  cases t
  exact congrArg₂ Memory.mk (funext hd) (funext hi)

structure Output {K : Type} [Zero K] [One K] (w : Word) (geom vm gout vout : Memory K) : Prop where
  packet : BitRAM.ScalarPacket gout 256 w
  length : gout.index 37=w.length
  base : gout.index 43=256
  geomData : ∀ j, j<256 ∨ 256+w.length ≤ j → gout.data j=geom.data j
  geomIndex : ∀ j, j≠37 → j≠43 → gout.index j=geom.index j
  vmData : ∀ j, j≠0 → vout.data j=vm.data j
  vmIndex : ∀ j, 5 ≤ j → vout.index j=vm.index j
  reset : ∀ j, j<5 → vout.index j=0

private def geometryView {K : Type} (geom t : Memory K) (L : ℕ) : Memory K :=
  ⟨fun j => t.data (4*j+2),fun j => if j=37 then L else if j=43 then 256 else geom.index j⟩

private def vmView {K : Type} (vm t : Memory K) : Memory K :=
  ⟨fun j => t.data (2*j+1),fun j => if j<5 then 0 else vm.index j⟩

private theorem reassemble {K : Type} (minor geom vm t : Memory K) (L B : ℕ)
    (h : Physical L B (banks minor geom vm) t) :
    t=banks minor (geometryView geom t L) (vmView vm t) := by
  apply memory_ext
  · apply residues
    · intro j
      rw [minDataAt]
      exact (h.data _ (by omega) (fun k _ => by omega)).trans (minDataAt minor geom vm j)
    · intro j
      exact (geoDataAt minor (geometryView geom t L) (vmView vm t) j).symm
    · intro j
      exact (vmDataAt minor (geometryView geom t L) (vmView vm t) j).symm
  · apply residues
    · intro j
      rw [minIndexAt]
      apply (h.index _ ?_).trans (minIndexAt minor geom vm j)
      simp only [List.mem_cons,List.mem_nil_iff,or_false]
      omega
    · intro j
      rw [geoIndexAt]
      by_cases h37 : j=37
      · subst j
        simpa [geometryView] using h.length
      by_cases h43 : j=43
      · subst j
        simpa [geometryView] using h.base
      have fr := h.index (4*j+2) (by
        simp only [List.mem_cons,List.mem_nil_iff,or_false]
        omega)
      simpa [geometryView,h37,h43] using fr.trans (geoIndexAt minor geom vm j)
    · intro j
      rw [vmIndexAt]
      by_cases lo : j<5
      · have reset := h.reset (2*j+1) (by
          simp only [List.mem_cons,List.mem_nil_iff,or_false]
          omega)
        simpa [vmView,lo] using reset
      have fr := h.index (2*j+1) (by
        simp only [List.mem_cons,List.mem_nil_iff,or_false]
        omega)
      simpa [vmView,lo] using fr.trans (vmIndexAt minor geom vm j)
variable {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem block_spec (P : K → Prop) (minor geom vm : Memory K) (w : Word)
    (hMinor : minor.AllData P) (hGeom : geom.AllData P) (hVM : vm.AllData P)
    (len : vm.index 37=w.length) (base : 3 ≤ vm.index 43)
    (word : BitRAM.ScalarPacket vm (vm.index 43) w) :
    ∃ gout vout, Block.Eval (Memory.AllData P) block (Odd.memory (Odd.memory minor geom) vm)
        (20*w.length+14) (Odd.memory (Odd.memory minor gout) vout) ∧
      Output w geom vm gout vout ∧ gout.AllData P ∧ vout.AllData P := by
  let s := banks minor geom vm
  have safe : s.AllData P := Odd.allData _ _ (Odd.allData _ _ hMinor hGeom) hVM
  have hlen : s.index 75=2*w.length+1 := (vmIndexAt minor geom vm 37).trans (by rw [len])
  obtain ⟨t,e,h⟩ := physical_spec P s w.length (vm.index 43) safe base hlen (vmIndexAt minor geom vm 43)
  let gout := geometryView geom t w.length
  let vout := vmView vm t
  have endAt := reassemble minor geom vm t _ _ h
  have moved := (congrArg (fun y => Block.Eval (Memory.AllData P) block s (20*w.length+14) y) endAt).mp e
  refine ⟨gout,vout,moved,?_,
    fun j => e.safe_end (4*j+2),fun j => e.safe_end (2*j+1)⟩
  constructor
  · intro j hj
    exact (h.copied j hj).trans ((vmDataAt minor geom vm (vm.index 43+j)).trans (word j hj))
  · simp [gout,geometryView]
  · simp [gout,geometryView]
  · intro j outside
    exact (h.data (4*j+2) (by omega) (fun k hk => by omega)).trans (geoDataAt minor geom vm j)
  · intro j j37 j43
    simp [gout,geometryView,j37,j43]
  · intro j hj
    exact (h.data (2*j+1) (by omega) (fun k _ => by omega)).trans (vmDataAt minor geom vm j)
  · intro j hj
    simp [vout,vmView,show ¬j<5 by omega]
  · intro j hj
    simp [vout,vmView,hj]

def fragment : Fragment := Fragment.ofBlock block

theorem fragment_spec (P : K → Prop) (minor geom vm : Memory K) (w : Word)
    (hMinor : minor.AllData P) (hGeom : geom.AllData P) (hVM : vm.AllData P)
    (len : vm.index 37=w.length) (base : 3 ≤ vm.index 43)
    (word : BitRAM.ScalarPacket vm (vm.index 43) w) :
    ∃ gout vout, fragment.Run P (Odd.memory (Odd.memory minor geom) vm)
        (20*w.length+14) (Odd.memory (Odd.memory minor gout) vout) ∧
      Output w geom vm gout vout ∧ gout.AllData P ∧ vout.AllData P := by
  obtain ⟨g,v,run,out,hg,hv⟩ := block_spec P minor geom vm w hMinor hGeom hVM len base word
  exact ⟨g,v,Fragment.Run.ofBlock run,out,hg,hv⟩

end VMPacketCopy
end Geometry
end LinearProgramming
end Optimization
end OAI
