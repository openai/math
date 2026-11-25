import OAI.Hierarchy.FactorOccurrences

namespace OAI
/-! # Computing a factor's tick in a single ordered pass -/

namespace Hierarchy.FactorAllocation

/-- The counter seen by a factor is the number of earlier factors in its class. -/
def prefixCount {N d : ℕ} (w : ℕ) (cost : Fin N → Fin d → ℕ)
    (i : ℕ) (g : Key w d) : ℕ :=
  (group (key w cost) ((List.finRange N).take i) g).length

theorem prefix_zero {N d : ℕ} (w : ℕ) (cost : Fin N → Fin d → ℕ) :
    prefixCount w cost 0 = fun _ => 0 := by funext g; simp [prefixCount,group]

theorem prefix_succ {N d : ℕ} (w : ℕ) (cost : Fin N → Fin d → ℕ) (i : Fin N) :
    prefixCount w cost (i.val+1) =
      Function.update (prefixCount w cost i.val) (key w cost i)
        (prefixCount w cost i.val (key w cost i)+1) := by
  funext g
  have h : i.val < (List.finRange N).length := by simp
  by_cases e : key w cost i = g
  · subst g
    simp [prefixCount,group,List.take_succ_eq_append_getElem h, List.filter_append]
  · simp [prefixCount,group,List.take_succ_eq_append_getElem h, List.filter_append,
      Function.update_of_ne (Ne.symm e),e]

private theorem tick_member {α : Type*} {T : ℕ} (xs : List α) (t : Fin T)
    (i : Fin xs.length) (hit : i.val ≡ t.val [MOD T]) : xs[i] ∈ atTick xs t := by
  apply List.mem_flatten.mpr
  refine ⟨[xs[i]],List.mem_ofFn.mpr ⟨i,?_⟩,by simp⟩
  simp [hit]

/-- Native count modulo the tick period yields the owner used by all
factor-product and resource-bound theorems. -/
theorem owner_eq_prefix {N T d : ℕ} (ht : 0<T) (w : ℕ) (cost : Fin N → Fin d → ℕ)
    (i : Fin N) : (owner ht w cost i).val = prefixCount w cost i.val (key w cost i) % T := by
  let xs := List.finRange N
  let g := key w cost i
  let pre := group (key w cost) (xs.take i.val) g
  let post := group (key w cost) (xs.drop (i.val+1)) g
  let tick : Fin T := ⟨pre.length%T,Nat.mod_lt _ ht⟩
  have bound : i.val<xs.length := by simp [xs]
  have cut : xs.take i.val ++ i::xs.drop (i.val+1) = xs := by
    have get : xs[i.val] = i := by simp [xs]
    have splitRest := List.drop_eq_getElem_cons bound
    rw [get] at splitRest
    rw [←splitRest, List.take_append_drop]
  have split : group (key w cost) xs g = pre ++ i::post := by
    conv_lhs => rw [←cut]
    simp [pre,post,group,List.filter_append,g]
  have inside : i∈atTick (group (key w cost) xs g) tick := by
    rw [split]
    let j : Fin (pre++i::post).length := ⟨pre.length,by simp⟩
    have hit : j.val ≡ tick.val [MOD T] := by simp [j,tick,Nat.ModEq]
    simpa [j] using tick_member (pre++i::post) tick j hit
  have yes : i ∈ factors w cost xs tick := by
    apply List.mem_flatten.mpr
    refine ⟨_, List.mem_ofFn.mpr ⟨finFunctionFinEquiv g,?_⟩,inside⟩
    simp
  have eq := (mem_factors_iff_owner ht w cost i tick).mp yes
  exact congrArg Fin.val eq.symm

end Hierarchy.FactorAllocation

end OAI
