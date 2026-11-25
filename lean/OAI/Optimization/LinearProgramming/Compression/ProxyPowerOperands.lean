import OAI.Optimization.LinearProgramming.Compression.PowerTapeBuild

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM
open scoped BigOperators

/-- An arbitrary enumeration of the queried large indices can be used. -/
def proxyPowerOperands {ι : Type*} (indices : List ι) (offset : ℤ) (D : ℕ)
    (a : ι → ℤ) (mag : ι → ℚ) : List (ℚ × ℤ) :=
  (2,offset) :: indices.map fun i => (mag i,(D : ℤ) * a i)

theorem proxyOperands_value {ι : Type*} [Fintype ι] [DecidableEq ι]
    (large : Finset ι) (indices : List ι) (hindices : indices.Perm large.toList)
    (D : ℕ) (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℚ) :
    ((proxyPowerOperands indices (clearedProxyOffset large D c a grid) D a mag).map
      fun p => p.1 ^ p.2).prod = proxyProduct large D c a grid mag := by
  let f i := (mag i)^((D : ℤ)*a i)
  have h := (hindices.map f).prod_eq
  change (indices.map f).prod = (large.toList.map f).prod at h
  simp only [proxyPowerOperands, List.map_cons, List.map_map, Function.comp_def, List.prod_cons,
    proxyProduct]
  exact congrArg (_ * ·) (h.trans (Finset.prod_map_toList large f))

theorem proxyProductTag {ι : Type*} [Fintype ι] [DecidableEq ι] (large : Finset ι)
    (hlarge : large.Nonempty) (D : ℕ) (hD : 0 < D) (c : ℤ) (a grid : ι → ℤ) (mag : ι → ℚ)
    (hmag : ∀ i ∈ large, 0 < mag i) :
    let x := proxyProduct large D c a grid mag
    let y := proxyAffine large D c a grid mag
    (if x < 1 then 0 else if 1 < x then 2 else 1 : ℕ) =
      (if y < 0 then 0 else if 0 < y then 2 else 1) := by
  dsimp only
  have h := compareProxyAffine_correct large D hD c a grid mag hmag
  rw [compareProxyAffine, ite_eq_left hlarge] at h
  change (if proxyProduct large D c a grid mag < 1 then Ordering.lt
    else if 1 < proxyProduct large D c a grid mag then .gt else .eq) = _ at h
  split_ifs at h ⊢ <;> rfl

theorem proxyPowerOperands_legal {ι : Type*} (large : Finset ι) (indices : List ι)
    (hindices : indices.Perm large.toList) (offset : ℤ) (D : ℕ) (a : ι → ℤ) (mag : ι → ℚ)
    (hmag : ∀ i ∈ large, 0 < mag i) :
    ∀ p ∈ proxyPowerOperands indices offset D a mag, p.2 < 0 → p.1 ≠ 0 := by
  intro p hp _
  rcases List.mem_cons.mp hp with rfl | h
  · norm_num
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp h
    exact (hmag i (Finset.mem_toList.mp (hindices.mem_iff.mp hi))).ne'

theorem proxyPowerOperands_budget {ι : Type*} (large : Finset ι) (indices : List ι)
    (hindices : indices.Perm large.toList) (offset : ℤ) (D : ℕ) (a : ι → ℤ) (mag : ι → ℚ)
    {K E B : ℕ} (hk : offset.natAbs ≤ K) (he : ∀ i ∈ large, ((D : ℤ)*a i).natAbs ≤ E)
    (hb : ∀ i ∈ large, ratBits (mag i) ≤ B) :
    3 + ((proxyPowerOperands indices offset D a mag).map powerTermBudget).sum ≤
      10 + 4*K + large.card*(3+(E+1)*B) := by
  let g i := 3 + (((D : ℤ)*a i).natAbs+1)*ratBits (mag i)
  have hmap := (hindices.map g).sum_eq.trans (Finset.sum_map_toList large g)
  have hsum : ∑ i ∈ large, g i ≤ large.card * (3+(E+1)*B) := by
    calc
      _ ≤ ∑ _i ∈ large, (3 + (E+1)*B) := Finset.sum_le_sum
        (fun i hi => Nat.add_le_add_left (Nat.mul_le_mul (Nat.add_le_add_right (he i hi) 1) (hb i hi)) 3)
      _ = _ := by simp
  have h₂ : ratBits (2 : ℚ) = 4 := rfl
  have hre : ((proxyPowerOperands indices offset D a mag).map powerTermBudget).sum =
      3 + (offset.natAbs+1)*ratBits 2 + (indices.map g).sum := by
    simp [proxyPowerOperands,powerTermBudget,List.map_map,Function.comp_def,g]
  calc
    _ = 3 + (3+(offset.natAbs+1)*4+large.sum g) := by rw [hre,h₂,hmap]
    _ ≤ 3 + (3+(K+1)*4+large.card*(3+(E+1)*B)) := Nat.add_le_add_left
      (Nat.add_le_add (Nat.add_le_add_left (Nat.mul_le_mul_right 4 (Nat.add_le_add_right hk 1)) 3) hsum) 3
    _ = _ := by omega

theorem proxyPowerOperands_time {ι : Type*} (large : Finset ι) (indices : List ι)
    (hindices : indices.Perm large.toList) (offset : ℤ) (D : ℕ) (a : ι → ℤ) (mag : ι → ℚ)
    {K E : ℕ} (hk : offset.natAbs.size ≤ K)
    (he : ∀ i ∈ large, ((D : ℤ)*a i).natAbs.size ≤ E) :
    ((proxyPowerOperands indices offset D a mag).map fun p => 2*p.2.natAbs.size+3).sum ≤
      2*K+3+large.card*(2*E+3) := by
  let g i := 2*((D : ℤ)*a i).natAbs.size+3
  have hsum : ∑ i ∈ large, g i ≤ large.card*(2*E+3) := by
    calc
      _ ≤ ∑ _i ∈ large, (2*E+3) := Finset.sum_le_sum
        (fun i hi => Nat.add_le_add_right (Nat.mul_le_mul_left 2 (he i hi)) 3)
      _ = _ := by simp
  have hre : ((proxyPowerOperands indices offset D a mag).map fun p => 2*p.2.natAbs.size+3).sum =
      2*offset.natAbs.size+3+(indices.map g).sum := by
    simp [proxyPowerOperands,List.map_map,Function.comp_def,g]
  have hmap := (hindices.map g).sum_eq.trans (Finset.sum_map_toList large g)
  calc
    _ = 2*offset.natAbs.size+3+large.sum g := by rw [hre,hmap]
    _ ≤ _ := Nat.add_le_add (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hk) 3) hsum

end Compression
end LinearProgramming
end Optimization
end OAI
