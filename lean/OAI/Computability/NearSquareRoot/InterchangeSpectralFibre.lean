import OAI.Computability.NearSquareRoot.InterchangeSpectralRequest
import OAI.Computability.NearSquareRoot.KernelSwapRepair
import OAI.Computability.NearSquareRoot.InterchangeStageRoute

/-!
# Restricting physical spectral sweeps to the main fields

The selected main pairs are embedded in the complete P192 address, with the
reserve pairs and outer tape positions fixed. A forward sweep, or a reversed
inverse sweep, agrees on each such fibre with the spectral map of the main cube.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeSpectralFibre

open IntegerMultiplication IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims
  IntegerMultiplication.Adic IntegerMultiplication.Loom InterchangeAddress SwapSpectrum

section Payload

open Interchange StageRoute

variable {X A D L Q U H : Type} {r : U → Rectangle L} {I J : H → L}

/-- Every label and rectangle layout permutes entire physical records. Their
contiguous payload coordinates retain their order. -/
def withPayload (D : Type) (g : Layout r Q X) : Layout r Q (X × D) where
  S j v := (g.S j v).prodCongr (Equiv.refl D)
  T j v := (g.T j v).prodCongr (Equiv.refl D)
  C j b := (g.C j b).prodCongr (Equiv.refl D)
  prepareSrc u := (g.prepareSrc u).prodCongr (Equiv.refl D)
  prepareDst u := (g.prepareDst u).prodCongr (Equiv.refl D)
  localSrc j u := (g.localSrc j u).prodCongr (Equiv.refl D)
  localDst j u := (g.localDst j u).prodCongr (Equiv.refl D)
  source_triangle j u := congrArg (fun e : X ≃ X => e.prodCongr (Equiv.refl D)) (g.source_triangle j u)
  target_triangle j u := congrArg (fun e : X ≃ X => e.prodCongr (Equiv.refl D)) (g.target_triangle j u)

theorem withPayload_perm (D : Type) (g : Layout r Q X) (op : Move r Q I J) :
    (withPayload D g).perm op = (g.perm op).prodCongr (Equiv.refl D) := by
  cases op with
  | gather j t => rcases t with ⟨_, _ | _⟩ <;> rfl
  | distribute j t => rcases t with ⟨_, _ | _⟩ <;> rfl
  | _ => rfl

/-- A fibre over one physical record address map and one fixed payload position. -/
def withPayloadKey (k : A → X) (d : D) (a : A) : X × D := (k a,d)

theorem withPayload_pull (g : Layout r Q X) (k : A → X) (d : D) (sw : Q → A → A)
    (h : ∀ j v a, (g.S j v).symm (g.T j v (k a)) = k (sw j a))
    (j : Q) (v : L) (a : A) :
    ((withPayload D g).S j v).symm ((withPayload D g).T j v (withPayloadKey k d a)) =
      withPayloadKey k d (sw j a) :=
  Prod.ext (h j v a) rfl

/-- An entire payload moves per conversion, and the arithmetic uses the
symbol at the same payload position in the two records. -/
def lift {R : Type} (F : (X → R) → X → R) (x : X × D → R) (z : X × D) : R :=
  F (fun y => x (y,z.2)) z.1

theorem lift_key {R : Type} (F : (X → R) → X → R) (T : (A → R) → A → R) (k : A → X)
    (h : ∀ x, F x ∘ k = T (x ∘ k)) (d : D) (x : X × D → R) :
    lift F x ∘ withPayloadKey k d = T (x ∘ withPayloadKey k d) :=
  h (fun y => x (y,d))

end Payload

variable {J C R : Type} {m : ℕ} (slot : Fin m ↪ J)

/-- Fill the main fields with the supplied address and keep the other pairs at
their original values. -/
def fill (outside : Address J C) (a : Address (Fin m) C) : Address J C :=
  Function.extend slot a outside

@[simp] theorem fill_slot (outside : Address J C) (a : Address (Fin m) C) (j : Fin m) :
    fill slot outside a (slot j) = a j :=
  slot.injective.extend_apply a outside j

@[simp] theorem fill_outside (outside : Address J C) (a : Address (Fin m) C)
    {k : J} (hk : k ∉ Set.range slot) : fill slot outside a k = outside k :=
  Function.extend_apply' a outside k hk

variable [DecidableEq J]

theorem fill_swap (outside : Address J C) (a : Address (Fin m) C) (j : Fin m) :
    fill slot outside (swap j a) = swap (slot j) (fill slot outside a) := by
  funext k
  by_cases hk : k ∈ Set.range slot
  · obtain ⟨q,rfl⟩ := hk
    by_cases h : q = j
    · subst q; simp
    · simp [swap_other h, swap_other (fun he => h (slot.injective he))]
  · have h : k ≠ slot j := fun he => hk ⟨j,he.symm⟩
    simp [fill_outside slot outside _ hk, swap_other h]

variable [CommRing R]

private theorem passes_fill [LinearOrder C] (outside : Address J C)
    (inverse : Bool) (half : R) (fields : List (Fin m)) (x : Row J C R) :
    InterchangeSpectralStep.passes inverse half (fields.map slot) x ∘ fill slot outside =
      InterchangeSpectralStep.passes inverse half fields (x ∘ fill slot outside) := by
  induction fields generalizing x with
  | nil => rfl
  | cons j js ih =>
    simp only [List.map_cons, InterchangeSpectralStep.passes, List.foldl_cons] at ih ⊢
    rw [ih]
    congr 1
    funext a
    simp only [Function.comp_apply, fill_slot, fill_swap]

variable {b f : ℕ} [NeZero b] {P G B : Dims.Tape}
    (outside : Address J (Fin (b^f))) (p : Pin P) (g : Pin G) (s : Pin B)

/-- The physical key of a main-field address at fixed spectator values. -/
def key : Address (Fin m) (Fin (b^f)) → Keys P G B J (Block b f) :=
  InterchangeSpectralRequest.key p g s ∘ fill slot outside

theorem key_swap (a : Address (Fin m) (Fin (b^f))) (j : Fin m) :
    key slot outside p g s (swap j a) =
      InterchangeSpectralRequest.swapAt (slot j) (key slot outside p g s a) := by
  simp only [key, Function.comp_apply, fill_swap, InterchangeSpectralRequest.key,
    InterchangeSpectralRequest.swapAt, Prod.mk.injEq, true_and, and_true]
  constructor <;> funext k <;> by_cases h : k = slot j
  all_goals first | subst k; simp | simp [swap_other h, Function.update_of_ne h]

/-- Compare the two occupied physical blocks for every selected field. -/
def tag (k : Keys P G B J (Block b f)) : SwapRepair.Pattern m := fun j =>
  if number (k.2.2.2.1 (slot j)) < number (k.2.1 (slot j)) then 1 else 0

omit [DecidableEq J] in
theorem tag_key (a : Address (Fin m) (Fin (b^f))) :
    tag slot (key slot outside p g s a) = SwapRepair.pattern a := by
  funext j
  simp only [tag, key, Function.comp_apply, InterchangeSpectralRequest.key,
    InterchangeSpectralRequest.number_rank_symm, fill_slot, SwapRepair.pattern]
  rfl

/-- The numerical values of both occupied fields at each physical slot. -/
def numerical (k : Keys P G B J (Block b f)) : Address J (Fin (b^f)) := fun j =>
  (InterchangeSpectralRequest.fieldRank b f (k.2.1 j),
   InterchangeSpectralRequest.fieldRank b f (k.2.2.2.1 j))

omit [DecidableEq J] in
theorem key_self (k : Keys P G B J (Block b f)) :
    key slot (numerical k) k.1 k.2.2.1 k.2.2.2.2 (numerical k ∘ slot) = k := by
  have h : fill slot (numerical k) (numerical k ∘ slot) = numerical k := by
    funext j
    by_cases hj : j ∈ Set.range slot
    · obtain ⟨t,rfl⟩ := hj
      simp
    · exact fill_outside slot _ _ hj
  rcases k with ⟨p,u,g,v,s⟩
  simp only [key, Function.comp_apply, h, InterchangeSpectralRequest.key, numerical,
    Equiv.symm_apply_apply]

/-- Simultaneously exchange the two occupied fields at precisely the selected slots. -/
def swapMain (k : Keys P G B J (Block b f)) : Keys P G B J (Block b f) := by
  classical
  exact (k.1, fun j => if j ∈ Set.range slot then k.2.2.2.1 j else k.2.1 j, k.2.2.1,
    fun j => if j ∈ Set.range slot then k.2.1 j else k.2.2.2.1 j, k.2.2.2.2)

theorem key_swapAll (a : Address (Fin m) (Fin (b^f))) :
    key slot outside p g s (SwapRepair.swapAll a) = swapMain slot (key slot outside p g s a) := by
  classical
  simp only [swapMain, key, Function.comp_apply, InterchangeSpectralRequest.key,
    Prod.mk.injEq, true_and, and_true]
  constructor <;> funext j <;> by_cases hj : j ∈ Set.range slot
  all_goals first
    | obtain ⟨i,rfl⟩ := hj; simp [SwapRepair.swapAll]
    | simp [hj]

theorem forward_key (half : R) (hh : 2 * half = 1) (fields : List (Fin m))
    (x : Keys P G B J (Block b f) → R) :
    ((fields.map slot).foldl (fun v j => InterchangeSpectralRequest.advance false half j v) x) ∘
        key slot outside p g s =
      spectrum fields half hh (x ∘ key slot outside p g s) := by
  unfold key
  rw [← Function.comp_assoc, InterchangeSpectralRequest.passes_key, passes_fill,
    InterchangeSpectralStep.forward_passes half hh]
  rfl

theorem inverse_key (half : R) (hh : 2 * half = 1) (fields : List (Fin m))
    (x : Keys P G B J (Block b f) → R) :
    ((fields.map slot).reverse.foldl (fun v j => InterchangeSpectralRequest.advance true half j v) x) ∘
        key slot outside p g s =
      (spectrum fields half hh).symm (x ∘ key slot outside p g s) := by
  unfold key
  rw [← Function.comp_assoc, InterchangeSpectralRequest.passes_key, ← List.map_reverse, passes_fill,
    InterchangeSpectralStep.inverse_passes half hh]
  rfl

end InterchangeSpectralFibre

end

end NearSquareRoot
end Computability
end OAI
