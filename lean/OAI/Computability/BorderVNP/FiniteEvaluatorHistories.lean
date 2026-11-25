import OAI.Computability.BorderVNP.FiniteEvaluatorSequence
import OAI.Computability.BorderVNP.DiagonalNativeCallState

/-! # Native histories after a deterministic field-valued continuation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator

open VPVNP.BurstRAM RoutingISA TeamRAM TeamContraction FieldProcessor
open scoped BigOperators Classical

variable {w m g : ℕ} {Q Γ : Type} {F : Type*} [Field F]
variable (pub : Arg → Word w) (lib : Fin 8 → TeamSite.Macro Q Γ m g) (ret : Returns Q Γ F m 8) (fuel : ℕ)

private theorem within_join {ct cs len clock : ℕ} {es fs : List (TeamRAM.Event w)}
    (left : Within ct len clock es) (right : Within cs len clock fs) : Within (ct+cs) len clock (es++fs) :=
  ⟨(VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add left.cost right.cost),
    fun e he => (List.mem_append.mp he).elim (left.length e) (right.length e),
    fun e he => (List.mem_append.mp he).elim (left.choices e) (right.choices e)⟩

/-- A source-level validator can have many different private paths, including no
successful path at all. Its common real post-state allows one native scalar continuation
for every path. The full charged histories and the entire field-valued sum are preserved. -/
theorem continue_histories (a b : Code) (s : Bank w) (mem : Memory w)
    (old : Finset (List (TeamRAM.Event w))) (ct cs len clock : ℕ) (factor : F)
    (admit : ∀ es, es ∈ old ↔ ∃ t mt, Runs pub (TeamSiteEvents.macros lib fuel) a s mem es t mt)
    (budget : ∀ es ∈ old, Within ct len clock es)
    (same : ∀ {es t mt fs z mz}, Runs pub (TeamSiteEvents.macros lib fuel) a s mem es t mt →
      Runs pub (TeamSiteEvents.macros lib fuel) a s mem fs z mz → t=z ∧ mt=mz)
    (suffix : ∀ {es t mt}, Runs pub (TeamSiteEvents.macros lib fuel) a s mem es t mt →
      ∃ fs z mz, Runs pub (TeamSiteEvents.macros lib fuel) b t mt fs z mz ∧ Within cs len clock fs ∧
        weight pub lib ret fuel b t fs = factor ∧
        ∀ gs v mv, Runs pub (TeamSiteEvents.macros lib fuel) b t mt gs v mv → gs=fs) :
    ∃ paths : Finset (List (TeamRAM.Event w)),
      (∀ es, es ∈ paths ↔ ∃ t mt, Runs pub (TeamSiteEvents.macros lib fuel) (.seq a b) s mem es t mt) ∧
      (∀ es ∈ paths, Within (ct+cs) len clock es) ∧
      (∑ es ∈ paths, weight pub lib ret fuel (.seq a b) s es) = (∑ es ∈ old, weight pub lib ret fuel a s es) * factor := by
  by_cases nonempty : old.Nonempty
  · obtain ⟨es,he⟩ := nonempty
    obtain ⟨t,mt,first⟩ := (admit es).mp he
    obtain ⟨fs,z,mz,last,bound,value,only⟩ := suffix first
    let append : List (TeamRAM.Event w) ↪ List (TeamRAM.Event w) := ⟨(· ++ fs),fun _ _ h => List.append_cancel_right h⟩
    refine ⟨old.map append,?_,?_,?_⟩
    · intro ys
      constructor
      · intro hy
        obtain ⟨xs,hx,rfl⟩ := Finset.mem_map.mp hy
        obtain ⟨u,mu,prior⟩ := (admit xs).mp hx
        obtain ⟨rfl,rfl⟩ := same first prior
        exact ⟨_,_,prior.seq last⟩
      · rintro ⟨v,mv,path⟩
        obtain ⟨u,mu,xs,gs,rfl,prior,tail⟩ := Runs.seq_iff.mp path
        obtain ⟨rfl,rfl⟩ := same first prior
        obtain rfl := only gs v mv tail
        exact Finset.mem_map.mpr ⟨xs,(admit xs).mpr ⟨_,_,prior⟩,rfl⟩
    · intro ys hy
      obtain ⟨xs,hx,rfl⟩ := Finset.mem_map.mp hy
      exact within_join (budget xs hx) bound
    · rw [Finset.sum_map,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro xs hx
      obtain ⟨u,mu,prior⟩ := (admit xs).mp hx
      obtain ⟨rfl,rfl⟩ := same first prior
      exact (weight_seq pub lib ret fuel prior last).trans (congrArg (weight pub lib ret fuel a s xs * ·) value)
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp nonempty
    refine ⟨∅,?_,by simp,by simp⟩
    intro es
    simp only [Finset.notMem_empty, false_iff,not_exists]
    intro t mt run
    obtain ⟨u,mu,xs,_,_,prior,_⟩ := Runs.seq_iff.mp run
    exact Finset.notMem_empty xs ((admit xs).mpr ⟨u,mu,prior⟩)

end FiniteEvaluator

end BorderVNP
end Computability
end OAI
