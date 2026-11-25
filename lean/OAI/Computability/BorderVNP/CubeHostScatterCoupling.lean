import OAI.Computability.BorderVNP.CubeHostScatterLayout
import OAI.Computability.BorderVNP.CubeCableHostScatter

/-! # The checked bit loop reads the actual directed-bin and endpoint descriptors -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- The concrete field values for a cable end in the real directory. -/
def Layout.cached (l : Layout) (before : ℕ → ℕ) (i : ℕ) (side : Bool) : BitFields :=
  let k := l.key before i
  let a := l.pairs+3*k
  ⟨l.width before i,k,before (l.ordinals+i),before a,before (a+1),before (a+2),side.toNat,
    l.dest before i side,l.singles,l.packets,l.blocks,l.bc,l.bankWidth,l.selectorWidth⟩

/-- Each cached source address is exactly the singleton or packet address of the real bit. -/
theorem Layout.cached_source (l : Layout) (m : ℕ → ℕ) (i : ℕ) (side : Bool) (j : ℕ) :
    (l.cached m i side).source j = l.source m i side j := rfl

/-- The word bounds for the native inner loop follow from the actual allocated addresses. -/
theorem Layout.Fits.cached {l : Layout} {before : ℕ → ℕ} {w i : ℕ} (fit : l.Fits w before)
    (hi : i < l.count) {side : Bool} (owned : l.Owned before i side) : (l.cached before i side).Fits w := by
  let f := l.cached before i side
  have room (j : ℕ) (hj : j < f.width) : f.source j < 2^w := fit.sourceFit i hi side owned j hj
  have pos : 0 < f.bankWidth := fit.positive.2
  have bc : 0 < f.bc := fit.positive.1
  change f.Fits w
  refine ⟨(fit.ordFit i hi side owned).trans fit.stride.le,fit.destFit i hi side owned,
    fun _ => fit.stride,fun _ _ => bc,?_,?_,room⟩
  · intro j hj hk
    have h := room j hj
    simp only [BitFields.source,ite_eq_right hk] at h
    have hle := Nat.le_mul_of_pos_right (f.first+(f.start+j)/f.bc) pos
    omega
  · intro hk hw
    have h := room 0 hw
    simp only [BitFields.source,ite_eq_right hk] at h
    have hle := Nat.le_mul_of_pos_right (2*f.vertex+f.side) bc
    omega

/-- Sources are outside this owned write interval. -/
theorem Layout.Fits.source_outside {l : Layout} {before : ℕ → ℕ} {w i : ℕ} (fit : l.Fits w before)
    (hi : i < l.count) {side : Bool} (owned : l.Owned before i side) (j : ℕ) (hj : j < l.width before i) :
    l.source before i side j < l.dest before i side ∨
      l.dest before i side+l.width before i ≤ l.source before i side j :=
  fit.disjoint i hi side owned _ ⟨i,hi,side,Or.inr ⟨owned,j,hj,rfl⟩⟩

/-- The image of an owned native bit copy restores the original sources, including
after previous cells have already populated their own external banks. -/
theorem Layout.Frozen.image_eq {l : Layout} {before mem : ℕ → ℕ} {i : ℕ} {side : Bool}
    (frozen : l.Frozen before mem) (hi : i < l.count) (owned : l.Owned before i side) :
    (l.cached before i side).image mem (l.width before i) = l.copyEnd before mem i side := by
  funext a
  simp only [BitFields.image,Layout.copyEnd,owned,true_and]
  change (if l.dest before i side ≤ a ∧ a < l.dest before i side+l.width before i then
    mem (l.source before i side (a-l.dest before i side)) else mem a) = _
  split_ifs with hx
  · have hj : a-l.dest before i side < l.width before i := by omega
    exact frozen _ ⟨i,hi,side,Or.inr ⟨owned,_,hj,rfl⟩⟩
  · rfl

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
