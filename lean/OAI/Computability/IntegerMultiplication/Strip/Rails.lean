import OAI.Computability.IntegerMultiplication.Strip.Bearing

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
variable {I K : Type} {w : I→ℝ} {input : I→Tree}
theorem fixture (h : Volume w input) (hw : ∀x,1≤w x) (a : Tree) :
    Carries w input (fun _ => a) :=
  Carries.cheap hw h _ (Task.const ..)

-- finite compiled stripe
theorem finite_series (s : Series K) (v : I→K→Tree) (h : Volume w input) (hw : ∀x,1≤w x)
    (g : ∀ k, Carries w input (fun i => v i k)) :
    Carries w input (stackRun (fun _ => s) v) := by
  unfold stackRun
  simp_rw [stripe_simple]
  induction s.explore with
  | nil => exact fixture h hw _
  | cons a l ih => exact (g a).twice ih

theorem finite_cell (s : Series K) (v : I→K→Tree)
    (r : Carries w input (stackRun (fun _ => s) v)) (k : K) :
    Carries w input (fun i => v i k) := by
  apply r.chain
  suffices hh : ∀ l : List K, k∈l → Volume w (fun i => forest (v i) l) →
      Carries w (fun i => forest (v i) l) (fun i => v i k) by
    unfold stackRun
    simpa only [stackRun, stripe_simple] using
      hh s.explore (s.complete k)
        (by
          have ht := r.out
          unfold stackRun at ht
          simpa only [stripe_simple] using ht)
  intro l he h
  induction l with
  | nil => simp at he
  | cons a s ih =>
    simp only [forest_cons] at *
    rcases List.mem_cons.mp he with eq|q
    · subst a
      exact Carries.dropRight r.budget (Volume.left h) (Volume.right h)
    exact (Carries.dropLeft r.budget (Volume.left h) (Volume.right h)).chain (ih q h.right)

theorem unzip_fixed (D : List K) {A : I→Type} (s : (i:I)→Series (A i))
    (v : (i:I)→K→A i→Tree)
    (h : Carries w input (stackRun s (fun i p => forest (fun k => v i k p) D))) :
    Carries w input (fun i => forest (fun k => stripe (s i) (v i k)) D) := by
  have g := h.small; have t := h.budget
  induction D generalizing input with
  | nil => exact fixture g t _
  | cons a D ih =>
    simp only [forest_cons]
    have e := unpair s _ _ h
    have i := e.out
    let tail := Carries.dropLeft t (Volume.left i) (Volume.right i)
    let acc := Carries.dropRight t (Volume.left i) (Volume.right i)
    have he := e.chain acc; have ht := e.chain tail
    exact he.twice (ih ht g)

theorem zip_fixed (D : List K) {A : I→Type} (s : (i:I)→Series (A i))
    (v : (i:I)→K→A i→Tree)
    (h : Carries w input (fun i => forest (fun k => stripe (s i) (v i k)) D))
    -- empty streams on output still cost number records! actual nested nil coming for free?
    -- need count of dynamic s; can construct via tally or assume D nonempty and implement recursive zipping base singleton via map wrapping [].
    (z : Carries w input (stackRun s fun _ _ => (.atom false))) :
    Carries w input (stackRun s (fun i p => forest (fun k => v i k p) D)) := by
  induction D with
  | nil => exact z
  | cons a D ih =>
    have i := h.out
    simp only [forest_cons] at h i ⊢
    have u := h.chain (Carries.dropRight h.budget (Volume.left i) (Volume.right i)); have g := h.chain
      (Carries.dropLeft h.budget (Volume.left i) (Volume.right i))
    exact coalesce s _ _ u (ih g)

/-- narrow transpose in terms of already grouped streams -/
theorem unlay (r : Series K) {A : I→Type} (s : (i:I)→Series (A i)) (v : (i:I)→K→A i→Tree)
    (h : Carries w input (stackRun s fun i p => stripe r (fun k => v i k p))) :
    Carries w input (fun i => stripe r fun k => stripe (s i) (v i k)) := by
  simp_rw [stripe_simple] at h ⊢ -- unfold? nested eta stackRun
  -- slash
  simpa only [stripe_simple] using (unzip_fixed r.explore s v h)
theorem lay (r : Series K) {A : I→Type} (s : (i:I)→Series (A i)) (v : (i:I)→K→A i→Tree)
    (h : Carries w input (fun i => stripe r fun k => stripe (s i) (v i k)))
    (z : Carries w input (stackRun s fun _ _ => (.atom false))) :
    Carries w input (stackRun s fun i p => stripe r (fun k => v i k p)) := by
  simp_rw [stripe_simple]
  apply zip_fixed _ _ _ _ z
  simpa only [stripe_simple] using h
end Strip

end IntegerMultiplication
end Computability
end OAI
