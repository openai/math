import OAI.Hierarchy.FormulaPartitionKernel
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma

namespace OAI
/-! # Coefficient transfers along paths with fixed boundary slot sets -/

namespace Hierarchy.FormulaPartition
open scoped BigOperators Classical
noncomputable section

/-- The predicate tests the pair of slot sets at a transition. -/
abbrev GuardedStep (V : Type) (τ : V → Type) (F : Type*) [Field F] [DecidableEq V] :=
  Kernel V τ F × (Finset V → Finset V → Prop)

variable {V : Type} {τ : V → Type} {F : Type*} [Field F] [DecidableEq V] [Fintype V]

def walk : List (GuardedStep V τ F) → (∀ v, τ v) → Finset V → (Finset V → F) → F
  | [], _, S, tip => tip S
  | k :: ks, x, S, tip =>
    ∑ U : Finset V, if k.2 S U then k.1.value x S U * walk ks x U tip else 0

theorem walk_append (first next : List (GuardedStep V τ F)) (x : ∀ v, τ v)
    (S : Finset V) (tip : Finset V → F) :
    walk (first ++ next) x S tip = walk first x S (fun U => walk next x U tip) := by
  induction first generalizing S with
  | nil => rfl
  | cons k ks ih => simp only [List.cons_append,walk,ih]

theorem walk_unmasked (ks : List (Kernel V τ F)) (x : ∀ v,τ v) (S : Finset V) (tip : Leaf V τ F) :
    walk (ks.map (fun k => (k,fun _ _ => True))) x S (tip.value x) = run x tip ks S := by
  induction ks generalizing S with
  | nil => rfl
  | cons k ks ih => simp only [List.map_cons,walk,ite_true,ih,run,Kernel.act]

/-- Transfer from a fixed initial slot set to a fixed terminal slot set. -/
def segmentValue (steps : List (GuardedStep V τ F)) (x : ∀v,τ v) (S T : Finset V) : F :=
  walk steps x S (fun U => if U=T then 1 else 0)

@[simp] theorem segmentValue_nil (x : ∀v,τ v) (S T : Finset V) :
    segmentValue [] x S T = (if S=T then 1 else 0 : F) := rfl

theorem segmentValue_cons (k : GuardedStep V τ F) (ks : List (GuardedStep V τ F))
    (x : ∀v,τ v) (S T : Finset V) :
    segmentValue (k::ks) x S T =
      ∑ U : Finset V, if k.2 S U then k.1.value x S U * segmentValue ks x U T else 0 := rfl

/-- Every nonzero transfer can only discard slots. -/
theorem segmentValue_subset (steps : List (GuardedStep V τ F)) (x : ∀v,τ v) (S T : Finset V)
    (nz : segmentValue steps x S T ≠ 0) : T ⊆ S := by
  induction steps generalizing S with
  | nil =>
    by_contra bad
    have ne : S ≠ T := fun e => bad (by simpa only [e] using Finset.Subset.refl T)
    simp [ne] at nz
  | cons k ks ih =>
    by_contra bad
    apply nz
    rw [segmentValue_cons]
    apply Finset.sum_eq_zero
    intro U _
    by_cases h : k.2 S U
    · rw [ite_eq_left h]
      by_cases sub : U ⊆ S
      · have zero : segmentValue ks x U T = 0 := by
          by_contra hn
          exact bad ((ih U hn).trans sub)
        rw [zero,mul_zero]
      · have zero : k.1.value x S U = 0 := by
          by_contra hn
          exact sub (k.1.subset x S U hn)
        rw [zero,zero_mul]
    · exact ite_eq_right h

/-- Fixing boundary slot sets confines all intermediate factors to their difference. -/
theorem segmentValue_locality (steps : List (GuardedStep V τ F)) (x y : ∀v,τ v) (S T : Finset V)
    (agree : ∀v∈S \ T,x v=y v) : segmentValue steps x S T = segmentValue steps y S T := by
  induction steps generalizing S with
  | nil => rfl
  | cons k ks ih =>
    rw [segmentValue_cons,segmentValue_cons]
    apply Finset.sum_congr rfl
    intro U _
    by_cases hguard : k.2 S U
    · simp only [ite_eq_left hguard]
      by_cases su : U ⊆ S
      · by_cases tu : T ⊆ U
        · have ksame := k.1.locality x y S U (fun v hv => by
            rcases Finset.mem_sdiff.mp hv with ⟨hs,hu⟩
            exact agree v (Finset.mem_sdiff.mpr ⟨hs,fun h => hu (tu h)⟩))
          have rsame := ih U (fun v hv => by
            rcases Finset.mem_sdiff.mp hv with ⟨hu,ht⟩
            exact agree v (Finset.mem_sdiff.mpr ⟨su hu,ht⟩))
          rw [ksame,rsame]
        · have zero (a : ∀v,τ v) : segmentValue ks a U T=0 := by
            by_contra hn
            exact tu (segmentValue_subset ks a U T hn)
          rw [zero x,zero y,mul_zero,mul_zero]
      · have zero (a : ∀v,τ v) : k.1.value a S U=0 := by
          by_contra hn
          exact su (k.1.subset a S U hn)
        rw [zero x,zero y,zero_mul,zero_mul]
    · simp only [ite_eq_right hguard]

/-- Expand the transfer in a basis of fixed end states. -/
theorem walk_eq_sum (steps : List (GuardedStep V τ F)) (x : ∀v,τ v) (S : Finset V)
    (tip : Finset V → F) :
    walk steps x S tip = ∑ T : Finset V, segmentValue steps x S T * tip T := by
  induction steps generalizing S with
  | nil => simp [walk,ite_mul]
  | cons k ks ih =>
    rw [walk]
    simp_rw [segmentValue_cons,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro U _
    by_cases h : k.2 S U <;> simp only [h,ite_true,ite_false,zero_mul,Finset.sum_const_zero,
      ih,Finset.mul_sum,mul_assoc]

/-- Whatever the remaining gates do, a leaf continuation uses only slots
present at the start of that suffix. -/
theorem walk_leaf_locality (steps : List (GuardedStep V τ F)) (tip : Leaf V τ F)
    (x y : ∀v,τ v) (S : Finset V) (agree : ∀v∈S, x v=y v) :
    walk steps x S (tip.value x) = walk steps y S (tip.value y) := by
  rw [walk_eq_sum,walk_eq_sum]
  apply Finset.sum_congr rfl
  intro T _
  by_cases sub : T⊆S
  · rw [segmentValue_locality steps x y S T (fun v hv => agree v (Finset.mem_sdiff.mp hv).1),
        tip.locality x y T (fun v hv => agree v (sub hv))]
  · have zero (a : ∀v,τ v) : segmentValue steps a S T = 0 := by
      by_contra nz
      exact sub (segmentValue_subset steps a S T nz)
    rw [zero x,zero y,zero_mul,zero_mul]

theorem walk_cut (first next : List (GuardedStep V τ F)) (x : ∀v,τ v) (S : Finset V)
    (tip : Finset V → F) :
    walk (first ++ next) x S tip =
      ∑ T : Finset V, segmentValue first x S T * walk next x T tip := by
  rw [walk_append]
  exact walk_eq_sum ..

theorem walk_pin (steps : List (GuardedStep V τ F)) (x : ∀v,τ v) (S T : Finset V)
    (tip : Finset V → F) :
    walk steps x S (fun U => if U=T then tip U else 0) = segmentValue steps x S T * tip T := by
  rw [walk_eq_sum]
  simp only [mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true]

abbrev MarkedSegment (V : Type) (τ : V → Type) (F : Type*) [Field F] [DecidableEq V] :=
  List (GuardedStep V τ F) × Finset V

/-- Composition of the segments with the assigned boundary states imposed at the cuts. -/
def markedWalk : List (MarkedSegment V τ F) → (∀v,τ v) → Finset V → (Finset V → F) → F
  | [], _, S, tip => tip S
  | (ks,T)::rest, x, S, tip =>
    walk ks x S (fun U => if U=T then markedWalk rest x U tip else 0)

def segmentFactors : List (MarkedSegment V τ F) → (∀v,τ v) → Finset V → List F
  | [], _, _ => []
  | (ks,T)::rest, x, S => segmentValue ks x S T :: segmentFactors rest x T

def lastBoundary : List (MarkedSegment V τ F) → Finset V → Finset V
  | [], S => S
  | (_,T)::rest, _ => lastBoundary rest T

/-- After fixing the gates and boundary slot sets, the sum over compatible
internal states is the product of the segment transfers and the terminal value. -/
theorem markedWalk_factor (parts : List (MarkedSegment V τ F)) (x : ∀v,τ v) (S : Finset V)
    (tip : Finset V → F) :
    markedWalk parts x S tip = (segmentFactors parts x S).prod * tip (lastBoundary parts S) := by
  induction parts generalizing S with
  | nil => simp [markedWalk,segmentFactors,lastBoundary]
  | cons part rest ih =>
    obtain ⟨ks,T⟩ := part
    simp only [markedWalk,walk_pin,ih,segmentFactors,lastBoundary,List.prod_cons,mul_assoc]

end
end Hierarchy.FormulaPartition

end OAI
