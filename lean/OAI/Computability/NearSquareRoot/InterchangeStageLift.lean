import OAI.Computability.NearSquareRoot.InterchangeSlots

/-!
# Address maps acting on selected physical fields

P192 represents a complete two-wing address by a pair of functions.  An
invertible change on any selected fields extends uniquely to an address
permutation fixing all other fields, including occupied reserve fields.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeStageLift

open IntegerMultiplication.Port NearSquareRoot.InterchangeSlots

variable {I J R : Type}

def view (s : I ↪ Spot J) (x : Duplex J R) : I → R := fun i => hear x (s i)

private def duplexOf (f : Spot J → R) : Duplex J R :=
  (fun j => f (false,j), fun j => f (true,j))

private theorem hear_duplexOf (f : Spot J → R) (u : Spot J) :
    hear (duplexOf f) u = f u := by
  rcases u with ⟨_ | _, j⟩ <;> rfl

/-- Perform a change on the selected fields, keeping the other fields at their
original positions. -/
noncomputable def update (s : I ↪ Spot J) (F : (I → R) → I → R) (x : Duplex J R) :
    Duplex J R := by
  classical
  exact duplexOf fun u => if h : ∃ i, s i = u then F (view s x) h.choose else hear x u

@[simp] theorem update_selected (s : I ↪ Spot J) (F : (I → R) → I → R) (x : Duplex J R) (i : I) :
    hear (update s F x) (s i) = F (view s x) i := by
  classical
  have h : ∃ i', s i' = s i := ⟨i, rfl⟩
  rw [update, hear_duplexOf, dite_eq_left h, s.injective h.choose_spec]

@[simp] theorem view_update (s : I ↪ Spot J) (F : (I → R) → I → R) (x : Duplex J R) :
    view s (update s F x) = F (view s x) := funext (update_selected s F x)

theorem update_outside (s : I ↪ Spot J) (F : (I → R) → I → R) (x : Duplex J R) (u : Spot J)
    (hu : ∀ i, u ≠ s i) : hear (update s F x) u = hear x u := by
  classical
  exact (hear_duplexOf _ _).trans (dite_eq_right (fun ⟨i,hi⟩ => hu i hi.symm))

/-- Uniqueness from the active fields and the spectator fields. -/
theorem eq_update (s : I ↪ Spot J) (F : (I → R) → I → R) {x y : Duplex J R}
    (h : ∀ i, hear y (s i) = F (view s x) i)
    (outside : ∀ u, (∀ i, u ≠ s i) → hear y u = hear x u) : y = update s F x := by
  apply hear_all
  intro u
  by_cases hs : ∃ i, u = s i
  · obtain ⟨i, rfl⟩ := hs
    exact (h i).trans (update_selected s F x i).symm
  · have hu : ∀ i, u ≠ s i := fun i H => hs ⟨i,H⟩
    rw [update_outside _ _ _ _ hu, outside _ hu]

@[simp] theorem update_id (s : I ↪ Spot J) (x : Duplex J R) : update s id x = x :=
  (eq_update s id (fun _ => rfl) (fun _ _ => rfl)).symm

theorem update_comp (s : I ↪ Spot J) (F G : (I → R) → I → R) (x : Duplex J R) :
    update s G (update s F x) = update s (G ∘ F) x := by
  apply eq_update
  · simp
  · intro u hu
    rw [update_outside _ _ _ _ hu, update_outside _ _ _ _ hu]

/-- Extend a permutation of the selected values to a physical address permutation. -/
noncomputable def perm (s : I ↪ Spot J) (F : Equiv.Perm (I → R)) : Equiv.Perm (Duplex J R) where
  toFun := update s F
  invFun := update s F.symm
  left_inv x := by rw [update_comp]; simp
  right_inv x := by rw [update_comp]; simp

@[simp] theorem perm_apply (s : I ↪ Spot J) (F : Equiv.Perm (I → R)) (x : Duplex J R) :
    perm s F x = update s F x := rfl

@[simp] theorem perm_symm (s : I ↪ Spot J) (F : Equiv.Perm (I → R)) :
    (perm s F).symm = perm s F.symm := rfl

@[simp] theorem perm_trans (s : I ↪ Spot J) (F G : Equiv.Perm (I → R)) :
    (perm s F).trans (perm s G) = perm s (F.trans G) := by
  apply Equiv.ext
  exact update_comp s F G

private theorem hear_add [Add R] (x y : Duplex J R) (u : Spot J) :
    hear (x+y) u = hear x u + hear y u := by
  rcases u with ⟨_ | _, j⟩ <;> rfl

private theorem hear_smul {K : Type} [SMul K R] (k : K) (x : Duplex J R) (u : Spot J) :
    hear (k • x) u = k • hear x u := by
  rcases u with ⟨_ | _, j⟩ <;> rfl

variable {K : Type} [Semiring K] [AddCommMonoid R] [Module K R]

/-- Extending selected coordinates preserves linearity over the address ring. -/
noncomputable def linearEquiv (s : I ↪ Spot J) (F : (I → R) ≃ₗ[K] (I → R)) :
    Duplex J R ≃ₗ[K] Duplex J R where
  __ := perm s F.toEquiv
  map_add' x y := by
    apply Eq.symm
    apply eq_update
    · intro i
      have hv : view s (x+y) = view s x + view s y := funext fun k => hear_add x y (s k)
      simp [hear_add, hv]
    · intro u hu
      simp [hear_add, update_outside _ _ _ _ hu]
  map_smul' k x := by
    apply Eq.symm
    apply eq_update
    · intro i
      have hv : view s (k • x) = k • view s x := funext fun l => hear_smul k x (s l)
      simp [hear_smul, hv]
    · intro u hu
      simp [hear_smul, update_outside _ _ _ _ hu]


/-- The original active fields: all early reserve fields followed by the
earlier and later main fields of the selected query. -/
def querySlots (a : ℕ) {m : ℕ} (j : Fin m) : Fin (a+2) ↪ Spot (Fin (a+m+a)) :=
  ⟨active (c:=a) (e:=0) (Nat.add_zero a) j, active_injective _ j⟩

def firstMain (a : ℕ) : Fin (a+2) := ⟨a, by omega⟩

def secondMain (a : ℕ) : Fin (a+2) := ⟨a+1, by omega⟩

@[simp] theorem querySlots_first (a : ℕ) {m : ℕ} (j : Fin m) :
    querySlots a j (firstMain a) = (false, mainRank a j) := active_first _ _

@[simp] theorem querySlots_second (a : ℕ) {m : ℕ} (j : Fin m) :
    querySlots a j (secondMain a) = (true, mainRank a j) := active_second _ _

/-- Swap the two main values and keep the whole early reserve. -/
def querySwap (a : ℕ) (A : Type) : Equiv.Perm (Fin (a+2) → A) :=
  (Equiv.swap (firstMain a) (secondMain a)).arrowCongr (Equiv.refl A)

@[simp] theorem querySwap_apply {A : Type} (a : ℕ) (x : Fin (a+2) → A) (i : Fin (a+2)) :
    querySwap a A x i = x (Equiv.swap (firstMain a) (secondMain a) i) := rfl

/-- A transposition among selected fields acts as the same transposition on
complete physical addresses. -/
theorem hear_update_swap {A : Type} [DecidableEq I] [DecidableEq J] (s : I ↪ Spot J) (i j : I)
    (x : Duplex J A) (u : Spot J) :
    hear (update s (fun v => v ∘ Equiv.swap i j) x) u =
      hear x (Equiv.swap (s i) (s j) u) := by
  by_cases hu : ∃ k, u = s k
  · obtain ⟨k,rfl⟩ := hu
    rw [update_selected]
    change hear x (s (Equiv.swap i j k)) = hear x (Equiv.swap (s i) (s j) (s k))
    by_cases hi : k = i
    · subst k
      simp
    by_cases hj : k = j
    · subst k
      simp
    rw [Equiv.swap_apply_of_ne_of_ne hi hj,
      Equiv.swap_apply_of_ne_of_ne (s.injective.ne hi) (s.injective.ne hj)]
  · have h : ∀ k, u ≠ s k := fun k h => hu ⟨k,h⟩
    rw [update_outside _ _ _ _ h,Equiv.swap_apply_of_ne_of_ne (h i) (h j)]

theorem physical_main_swap {A : Type} {m : ℕ} (a : ℕ) (j : Fin m)
    (x : Duplex (Fin (a+m+a)) A) (u : Spot (Fin (a+m+a))) :
    hear (update (querySlots a j) (querySwap a A) x) u =
      hear x ((Equiv.swap (false,mainRank a j) (true,mainRank a j)) u) := by
  have heq : (querySwap a A : (Fin (a+2) → A) → _) =
      (fun v => v ∘ Equiv.swap (firstMain a) (secondMain a)) := by funext v i; rfl
  rw [heq]
  simpa only [querySlots_first,querySlots_second] using
    hear_update_swap (querySlots a j) (firstMain a) (secondMain a) x u

/-- The lifted diagonal label transfer is exactly the P192 physical pivot,
including all values in the other reserve and main fields. -/
theorem update_querySwap {p m : ℕ} (f a : ℕ) (j : Fin m)
    (x : Duplex (Fin (a+m+a)) (Tower p f)) :
    update (querySlots a j) (querySwap a (Tower p f)) x =
      Lag.fire f x (.pivot (mainRank a j) (mainRank a j)) := by
  symm
  apply eq_update
  · intro i
    by_cases h₁ : i = firstMain a
    · subst i
      simp [Lag.fire,view]
    by_cases h₂ : i = secondMain a
    · subst i
      simp [Lag.fire,view]
    have h₁' : querySlots a j i ≠ (false, mainRank a j) := (querySlots_first a j) ▸ (querySlots a j).injective.ne h₁
    have h₂' : querySlots a j i ≠ (true, mainRank a j) := (querySlots_second a j) ▸ (querySlots a j).injective.ne h₂
    simp [Lag.fire,view,h₁',h₂',Equiv.swap_apply_of_ne_of_ne h₁ h₂]
  · intro u hu
    have h₁ : u ≠ (false, mainRank a j) := (querySlots_first a j) ▸ hu _
    have h₂ : u ≠ (true, mainRank a j) := (querySlots_second a j) ▸ hu _
    simp [Lag.fire,h₁,h₂]

end InterchangeStageLift

end NearSquareRoot
end Computability
end OAI
