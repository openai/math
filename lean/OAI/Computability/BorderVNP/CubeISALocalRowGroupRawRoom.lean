import OAI.Computability.BorderVNP.CubeISALocalRowGroupRoom

/-! # Histogram bounds before the physical row checks

Every ordered symbol pair can charge at most one group, and every delivery
charges exactly one group. These facts give a uniform upper bound for all
in-range declaration streams, including those rejected by the later row checks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

open Finset

private theorem rowCharge_sum_le (l : Layout) (mem : ℕ → ℕ) (cap q : ℕ)
    (positive : 0 < l.groups) (hq : q < l.groups*l.groups)
    (row : ∀ s < l.groups, ∀ t < l.groups, mem (l.rowAddr s t) ≤ cap) :
    ∑ s ∈ range l.groups, l.rowCharge mem q s ≤ cap+l.selectors := by
  have hs := (Nat.div_lt_iff_lt_mul positive).mpr hq
  have ht := Nat.mod_lt q positive
  rw [sum_eq_single_of_mem (q/l.groups) (mem_range.mpr hs)]
  · unfold Layout.rowCharge
    split
    · exact Nat.add_le_add_right (row _ hs _ ht) _
    · exact Nat.zero_le _
  · intro s _ diff
    simp [Layout.rowCharge,Ne.symm diff]

private theorem dataCharge_sum (l : Layout) (mem : ℕ → ℕ) (c : ℕ) (positive : 0 < l.groups) :
    ∑ s ∈ range l.groups, l.dataCharge mem c s = mem (l.demands+c) := by
  have pos : l.symbol mem c < l.groups := Nat.mod_lt _ positive
  rw [sum_eq_single_of_mem (l.symbol mem c) (mem_range.mpr pos)]
  · simp [Layout.dataCharge]
  · intro s _ diff
    simp [Layout.dataCharge,Ne.symm diff]

/-- A legal but incorrect declaration can change each incident row word by at
most the cap. It cannot duplicate a cell's incoming demand across groups. -/
theorem histogram_mass_le (l : Layout) (mem : ℕ → ℕ) (cap : ℕ)
    (positive : 0 < l.groups) (row : ∀ s < l.groups, ∀ t < l.groups, mem (l.rowAddr s t) ≤ cap) :
    ∑ s ∈ range l.groups, l.weight mem s ≤
      1000000*(l.groups*l.groups*(cap+l.selectors) + ∑ c ∈ range l.cells, mem (l.demands+c)) + l.groups*l.raw := by
  have shared : ∑ s ∈ range l.groups, l.sharedTotal mem (l.groups*l.groups) s ≤
      l.groups*l.groups*(cap+l.selectors) := by
    unfold Layout.sharedTotal
    rw [sum_comm]
    simpa only [sum_const,card_range,nsmul_eq_mul,Nat.cast_id] using
      (sum_le_sum (fun q hq => rowCharge_sum_le l mem cap q positive (mem_range.mp hq) row))
  have data : ∑ s ∈ range l.groups, l.dataTotal mem l.cells s = ∑ c ∈ range l.cells, mem (l.demands+c) := by
    unfold Layout.dataTotal
    rw [sum_comm]
    exact sum_congr rfl (fun c _ => dataCharge_sum l mem c positive)
  simp only [Layout.weight,TeamNative.scaledWeight,sum_add_distrib,← mul_sum,sum_const,card_range,nsmul_eq_mul,Nat.cast_id,data]
  omega

end Cube.GroupWeights

namespace RoutingISA.LocalRow

open BorderVNP.Cube BorderVNP.Cube.Physical Finset

/-- The actual accepted bit decoder places in-range row values at the exact
addresses used by the histogram's sorted-pair reads. -/
theorem histogramRow_le (a : CubeArena.Layout) (pub : Arg → ℕ) (saved frame axis : ℕ)
    (decl : Broadcast a.n a.header.d a.header.cap) (before : ℕ → ℕ) (z : NatState)
    (decoded : DecodedRows a pub saved decl before z) (rangeOk : declarationInRange decl)
    (valid : axis < a.n+1) (s : ℕ) (hs : s < a.header.d) (t : ℕ) (ht : t < a.header.d) :
    z.mem ((weightLayout a frame axis).rowAddr s t) ≤ a.header.cap := by
  let i : Fin (a.n+1) := ⟨axis,valid⟩
  let u : Fin a.header.d := ⟨min s t,(min_le_left s t).trans_lt hs⟩
  let v : Fin a.header.d := ⟨max s t,max_lt hs ht⟩
  have order : u ≤ v := (min_le_left s t).trans (le_max_left s t)
  have rows := decoded.2.2.2.2.2.1 u v i
  rw [CubeLengths.entryOrder_val,ite_eq_left order] at rows
  have word := rangeOk.2 (Sym2.mk u v) i
  have eq : z.mem ((weightLayout a frame axis).rowAddr s t) = readCode (a.header.cap+1) (decl.2 (Sym2.mk u v) i) := by
    simpa only [weightLayout,GroupWeights.Layout.rowAddr,CubeHeaderInstall.Inputs.decoder,u,v,i,Nat.add_assoc] using rows
  omega

/-- The reserved pair views dominate every in-range row and selector word.
The two raw endpoints of an ordered wire contribute to at most two groups.
Consequently the full histogram fits a fixed multiple of the actual allocation
plus its incoming demand, independent of the correctness of the claimed lengths. -/
theorem rawHistogram_le (a : CubeArena.Layout) (pub : Arg → ℕ) (saved frame axis : ℕ)
    (decl : Broadcast a.n a.header.d a.header.cap) (before : ℕ → ℕ) (z : NatState)
    (decoded : DecodedRows a pub saved decl before z) (rangeOk : declarationInRange decl)
    (valid : axis < a.n+1) (positive : 0 < a.header.d) :
    ∑ s ∈ range a.header.d, (weightLayout a frame axis).weight z.mem s ≤
      1000000*(a.stop+∑ c ∈ range a.cells, z.mem (a.demands+c)) + 2*a.stop := by
  let l := weightLayout a frame axis
  have sum := GroupWeights.histogram_mass_le l z.mem a.header.cap positive
    (histogramRow_le a pub saved frame axis decl before z decoded rangeOk valid)
  have ⟨_,_,vertex,publicLe,views,endCell⟩ := a.separated
  have stride : a.header.cap+l.selectors ≤ a.pairStride := by
    unfold CubeArena.Layout.pairStride
    dsimp only [l,weightLayout]
    omega
  have shared := Nat.mul_le_mul_left (a.header.d*a.header.d) stride
  rw [pow_two] at views
  have bound : a.header.d*a.header.d*(a.header.cap+l.selectors) ≤ a.stop := by omega
  let bc := a.header.blocks*(a.h*a.b)
  let q := a.alphabet/a.header.d
  have first : a.header.d*q ≤ a.alphabet := by rw [Nat.mul_comm]; exact Nat.div_mul_le_self ..
  have raw : a.header.d*l.raw ≤ 2*a.stop := calc
    _ = bc*((a.header.d*q)*(2*a.alphabet-q)) := by
      dsimp only [l,weightLayout,GroupWeights.Layout.raw,bc,q]
      ring
    _ ≤ bc*(a.alphabet*(2*a.alphabet)) :=
      Nat.mul_le_mul_left bc (Nat.mul_le_mul first (Nat.sub_le ..))
    _ = 2*(a.alphabet^2*bc) := by ring
    _ ≤ 2*a.stop := by
      have reserve : a.alphabet^2*bc ≤ a.vertexBase := Nat.le_add_left ..
      exact Nat.mul_le_mul_left 2 (by omega)
  change _ ≤ 1000000*(a.header.d*a.header.d*(a.header.cap+l.selectors)+
    ∑ c ∈ range a.cells, z.mem (a.demands+c)) + a.header.d*l.raw at sum
  exact sum.trans (Nat.add_le_add (Nat.mul_le_mul_left _ (Nat.add_le_add_right bound _)) raw)

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
