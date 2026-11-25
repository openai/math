import OAI.Computability.NearSquareRoot.CRTControlledBudget

/-! # Lifting a packed pass across untouched high fields -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Strip IntegerMultiplication.Code IntegerMultiplication.Loom
open IntegerMultiplication.Adic

/-- The input contains a whole Cartesian array. Carve it into complete rows, park the
shared descriptor with each row, run the same physical command throughout, and flatten
the result. The factor of the inner pass is unchanged by lifting. -/
theorem prefixPass {I : Type} {r : Regime I} {width : I → ℕ} {rate : I → ℝ}
    {A B : I → Type} (s : (i : I) → Series (A i)) (t : (i : I) → Series (B i))
    (hs : Station r s) (ht : Station r t)
    (input output : (i:I) → A i × B i → Tree)
    (live : Alive r (fun i => ((s i).cart (t i)).count) width
      (stackRun (fun i => (s i).cart (t i)) input))
    (step : Breeze (fun z : Sigma A => rate z.1) (r.pull (Sigma.fst : Sigma A → I))
      (fun z => (t z.1).count) (fun z => width z.1)
      (fun z => .fork (r.header z.1) (stripe (t z.1) (fun b => input z.1 (z.2,b))))
      (fun z => stripe (t z.1) (fun b => output z.1 (z.2,b)))) :
    Breeze rate r (fun i => ((s i).cart (t i)).count) width
      (together r.header (stackRun (fun i => (s i).cart (t i)) input))
      (stackRun (fun i => (s i).cart (t i)) output) := by
  let n i := ((s i).cart (t i)).count
  have ns (i : I) : (s i).count ≤ n i := by
    rw [show n i = (s i).count * (t i).count from Series.count_cart ..]; exact Nat.le_mul_of_pos_right _ (ht.1 i)
  have nt (i : I) : (t i).count ≤ n i := by
    rw [show n i = (s i).count * (t i).count from Series.count_cart ..]; exact Nat.le_mul_of_pos_left _ (hs.1 i)
  have pn (i : I) : 1 ≤ n i := (hs.1 i).trans (ns i)
  have data := Drive.self pn live
  have header := Drive.fetch pn live
  have rules := (header.chain (hs.supply ns)).twice (header.chain (ht.supply nt))
  have rows := Rip.carve s t input rules data hs.1 ht.1 (fun i => (Series.count_cart (s i) (t i)).symm.le)
  have pack := Rip.coalesce (fun i _ => r.header i) (fun i a => stripe (t i) (fun b => input i (a,b)))
    (header.chain (clones hs ns r.header Regime.self)) rows
  obtain ⟨hr,d,core⟩ := step
  have hr' (i : I) : 1 ≤ rate i := by
    obtain ⟨a, _⟩ := List.exists_mem_of_ne_nil (l := (s i).explore)
      (fun h => by have := hs.1 i; simp [Series.count,h] at this)
    exact hr ⟨i,a⟩
  have batch := liftoff s (fun i a => .fork (r.header i) (stripe (t i) (fun b => input i (a,b))))
    (fun i a => stripe (t i) (fun b => output i (a,b)))
    (runrate rate r (fun i => (t i).count) width d) core
  have norm (i : I) : (s i).count * runrate rate r (fun i => (t i).count) width d i + 1 ≤
      (2:ℝ) * runrate rate r n width d i := by
    have eq : (s i).count * runrate rate r (fun i => (t i).count) width d i = runrate rate r n width d i := by
      simp only [runrate,mass,n,Series.count_cart,Nat.cast_mul]
      ring
    have one := unit_mass (r := r) (l := width) pn d i
    have h := one_le_mul_of_one_le_of_one_le one (hr' i)
    change 1 ≤ runrate rate r n width d i at h
    rw [eq]; linarith
  have okay (i : I) : 1 ≤ runrate rate r n width d i :=
    one_le_mul_of_one_le_of_one_le (unit_mass pn d i) (hr' i)
  have result := (Breeze.launch pack hr').next (show Breeze rate r n width _ _ from
    ⟨hr',d,batch.times okay 2 norm⟩)
  obtain ⟨_,D,whole⟩ := result
  exact ⟨hr',D,flatten s t output whole⟩

end Controlled

end NearSquareRoot
end Computability
end OAI
