import OAI.Hierarchy.TaggedSortLiftFour
import OAI.Hierarchy.TaggedSortLiftParallel
import OAI.Hierarchy.DescentSortLiftHeight
import Mathlib.Tactic.Positivity

namespace OAI
/-! # Recursive short sorts with a common clock

Each lift has four passes. A problem already small enough for the preceding
level repeats its preceding schedule four times. Sorted blocks remain sorted,
so the recursion yields the same number of clocks in every branch, including
the half-blocks at the ends of the shifted pass.
-/

namespace Hierarchy.Tagged.SortLift

open scoped Classical
noncomputable section

variable {n : ℕ}

theorem dyadic_four_pass (κ : Type*) [LinearOrder κ] {b e : ℕ} (hb : 4≤b)
    (smaller : b<e) (growth : e≤b+b/4) :
    ∃ ss : List (Stage (2^e)), ss.length=4 ∧
      Widths (fun w => w=2^(b-1) ∨ w=2^b) ss ∧ Sorts ss κ := by
  obtain ⟨k,p,B,hk,pos,large,full,half,small,fit⟩ :=
    DescentSortLiftHeight.oneStepGeometry hb smaller growth
  rw [large,half,← small,← full,half]
  exact four_pass κ k p B hk pos half fit


def whole (n : ℕ) : Stage n :=
  let all : Fin 1 × Fin n ≃ Fin n :=
    ⟨Prod.snd,fun i=>(0,i),fun ⟨b,i⟩=>by simp [Subsingleton.elim b 0], fun _=>rfl⟩
  uniformStage all all

theorem whole_sorts (κ : Type*) [LinearOrder κ] (n : ℕ) : Sorts [whole n] κ := by
  intro x
  funext i
  exact (whole n).eval_output id x (0 : Fin 1) i

theorem sorts_append (κ : Type*) [LinearOrder κ] {ss ts : List (Stage n)}
    (hs : Sorts ss κ) (ht : Sorts ts κ) : Sorts (ss++ts) κ := by
  intro x
  rw [run_append,hs,ht]
  rw [Tuple.sort_eq_refl_iff_monotone.mpr (Tuple.monotone_sort x)]; rfl

private theorem substitute_one (κ : Type*) [LinearOrder κ] (S : Stage n) (D : ℕ) (pos : 0<D)
    (P : ℕ → Prop) (children : ∀ b, ∃ ts : List (Stage (S.length b)),
      ts.length=D ∧ Widths P ts ∧ Sorts ts κ) :
    ∃ ss : List (Stage n), ss.length=D ∧ Widths P ss ∧
      ∀ x : Fin n → κ, run ss id x = S.eval id x := by
  choose ts len width correct using children
  let T (b : Fin S.blocks) (i : Fin D) := (ts b)[i.val]'(by rw [len];exact i.isLt)
  have restore (b : Fin S.blocks) : List.ofFn (T b) = ts b := by
    apply List.ext_getElem
    · simp [len]
    · intro i _ _
      simp [T]
  refine ⟨parallel S D T,parallel_length _ _ _,?_,?_⟩
  · apply parallel_width
    intro b i
    exact width b _ (List.getElem_mem (by rw [len]; exact i.isLt))
  · intro x
    funext row
    obtain ⟨⟨b,i⟩,rfl⟩ := S.output.surjective row
    rw [parallel_eval S D T id x (by omega),restore,correct,S.eval_output]; rfl

theorem substitute_sorts (κ : Type*) [LinearOrder κ] (stages : List (Stage n))
    (D : ℕ) (pos : 0<D) (P : ℕ → Prop)
    (children : ∀ S ∈ stages, ∀ b, ∃ ts : List (Stage (S.length b)),
      ts.length=D ∧ Widths P ts ∧ Sorts ts κ) :
    ∃ ss : List (Stage n), ss.length=stages.length*D ∧ Widths P ss ∧
      ∀ x : Fin n → κ, run ss id x = run stages id x := by
  induction stages with
  | nil => exact ⟨[],by simp,by simp [Widths],fun _=>rfl⟩
  | cons S stages ih =>
    obtain ⟨head,lenH,widthH,exactH⟩ := substitute_one κ S D pos P (children S (by simp))
    obtain ⟨tail,lenT,widthT,exactT⟩ := ih (fun U h => children U (by simp [h]))
    refine ⟨head++tail,?_,?_,?_⟩
    · simp [lenH,lenT,Nat.add_mul,Nat.add_comm]
    · intro U hu
      exact (List.mem_append.mp hu).elim (widthH U) (widthT U)
    · intro x
      rw [run_append, exactH, exactT]; rfl

/-- At recursion level `d`, each one of the `4^d` actual global stages has
block widths between half the bottom size and the full bottom size. -/
theorem recursive_sorts (κ : Type*) [LinearOrder κ] (b : ℕ) (base : 4≤b)
    (d e : ℕ) (lower : b-1 ≤ e) (upper : e≤DescentSortLiftHeight.height b d) :
    ∃ ss : List (Stage (2^e)), ss.length=4^d ∧
      Widths (fun w => 2^(b-1)≤w ∧ w≤2^b) ss ∧ Sorts ss κ := by
  let P : ℕ → Prop := fun w => 2^(b-1)≤w ∧ w≤2^b
  induction d generalizing e with
  | zero =>
    change e≤b at upper
    refine ⟨[whole (2^e)],rfl,?_,whole_sorts κ _⟩
    intro S hS c
    have eqn : S = whole (2^e) := List.mem_singleton.mp hS
    subst S
    change 2^(b-1)≤2^e ∧ 2^e≤2^b
    exact ⟨Nat.pow_le_pow_right (by decide) lower,Nat.pow_le_pow_right (by decide) upper⟩
  | succ d ih =>
    let H := DescentSortLiftHeight.height b d
    have hH : b≤H := DescentSortLiftHeight.base_le _ _
    by_cases small : e≤H
    · obtain ⟨s,hs,ws,correct⟩ := ih e lower small
      refine ⟨(s++s)++(s++s),?_,?_,sorts_append κ (sorts_append κ correct correct)
        (sorts_append κ correct correct)⟩
      · simp only [List.length_append,hs,pow_succ];omega
      · intro U hU
        simp only [List.mem_append,or_self] at hU
        exact ws U hU
    · have grow : e≤H+H/4 := upper
      obtain ⟨stages,len,formats,correct⟩ := dyadic_four_pass κ (base.trans hH)
        (by omega : H<e) grow
      have children (S) (hS : S ∈ stages) (j : Fin S.blocks) :
          ∃ s : List (Stage (S.length j)), s.length=4^d ∧ Widths P s ∧ Sorts s κ := by
        rcases formats S hS j with half | full
        · rw [half]
          exact ih (H-1) (by omega) (by omega)
        · rw [full]
          exact ih H (by omega) le_rfl
      obtain ⟨ss,ls,ws,same⟩ := substitute_sorts κ stages (4^d) (by positivity) P children
      exact ⟨ss,by rw [ls,len,pow_succ,Nat.mul_comm],ws,fun x=>(same x).trans (correct x)⟩

end
end Hierarchy.Tagged.SortLift

end OAI
