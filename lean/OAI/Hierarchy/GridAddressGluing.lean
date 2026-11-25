import OAI.LinearAlgebra.SpectralBooks.SpectralPlacementPrices.ShortenPrice

namespace OAI
/-! # Contraction of shared hidden, external and literal bit addresses -/

namespace Hierarchy.GridAddress

open LinearAlgebra.SpectralBooks LinearAlgebra.SpectralBooks.SiteTensor
open scoped BigOperators Classical
noncomputable section

variable {I H O : Type} {F : Type*}

abbrev Address (H O : Type) := H ⊕ (O ⊕ Bool)
abbrev Site (H O I : Type) := H ⊕ (O ⊕ I)

def read (x : O → Bool) (h : H → Bool) : Address H O → Bool :=
  Sum.elim h (Sum.elim x id)

def outputSite (o : O) : Site H O I := .inr (.inl o)

private def addressSite (i : I) (a : Address H O) : Site H O I :=
  a.elim Sum.inl (Sum.elim outputSite (fun _ => .inr (.inr i)))

/-- Each literal occurrence gets its own site and thus can be placed freely. -/
def site (addr : I → Address H O) (i : I) : Site H O I := addressSite i (addr i)

def raw (c : (I → Bool) → F) : Raw.{0} I F where
  Leg _ := Bool
  finiteLeg _ := inferInstance
  coeff := c

/-- Sharing is enforced before the factors are multiplied. An unused hidden
address still counts both settings, as in the controller's ordinary sum. -/
def evaluate [Fintype H] [CommSemiring F] (T : (I → Bool) → F) (addr : I → Address H O)
    (x : O → Bool) : F := ∑ h : H → Bool, T (fun i => read x h (addr i))

private theorem localSum_restricts {J : Type} [Fintype J] [CommSemiring F]
    (S T : Raw.{0} J F) (U : J → Type) [∀ j, Fintype (U j)]
    (select : ∀ j, S.Leg j → U j → T.Leg j)
    (coeff : ∀ x, S.coeff x = ∑ u : (∀ j, U j), T.coeff (fun j => select j (x j) (u j))) :
    S.Restricts T := by
  classical
  refine ⟨fun j x a => ∑ b : U j, if a = select j x b then 1 else 0, fun x => ?_⟩
  rw [coeff]
  simp_rw [Fintype.prod_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  have heq (a : ∀ j, T.Leg j) : (∀ j, a j = select j (x j) (u j)) ↔
      a = (fun j => select j (x j) (u j)) := funext_iff.symm
  simp [Fintype.prod_boole, heq, mul_ite]

private def Local (j : Site H O I) : Type :=
  j.elim (fun _ => Bool) (fun _ => Unit)

private instance (j : Site H O I) : Fintype (Local j) := by
  cases j with
  | inl h => exact inferInstanceAs (Fintype Bool)
  | inr t => exact inferInstanceAs (Fintype Unit)

private def settings : (H → Bool) ≃ ((j : Site H O I) → Local j) where
  toFun h j := match j with
    | .inl z => h z
    | .inr _ => ()
  invFun u h := u (.inl h)
  left_inv _ := rfl
  right_inv u := by
    funext j
    cases j with
    | inl h => rfl
    | inr t => exact Subsingleton.elim (α := Unit) _ _

private def sample :
    (j : Site H O I) → ({o : O // outputSite o = j} → Bool) →
      Local j → Address H O → Bool
  | .inl _, _, u, _ => u
  | .inr (.inl o), x, _, _ => x ⟨o, rfl⟩
  | .inr (.inr _), _, _, a => a.elim (fun _ => false) (Sum.elim (fun _ => false) id)

private def assign (addr : I → Address H O) (j : Site H O I)
    (x : {o : O // outputSite o = j} → Bool) (u : Local j) (p : {i : I // site addr i = j}) :
    Bool := sample j x u (addr p.1)

private theorem read_sample
    (x : ∀ j : Site H O I, {o : O // outputSite o = j} → Bool) (h : H → Bool) (i : I)
    (a : Address H O) :
    read (fun o => x (outputSite o) ⟨o,rfl⟩) h a =
      sample (addressSite i a) (x _) ((settings h) _) a := by
  rcases a with z | o | b <;> rfl

/-- The shared-address contraction is a restriction of the independent
factor ports grouped at their physical addresses. -/
theorem restricts [Fintype I] [Fintype H] [Fintype O] [CommSemiring F]
    (T : (I → Bool) → F) (addr : I → Address H O) :
    ((raw (evaluate T addr)).group (outputSite (H:=H) (I:=I))).Restricts
      ((raw T).group (site addr)) := by
  let : DecidableEq (Site H O I) := fun _ _ => Classical.propDecidable _
  apply localSum_restricts _ _ Local (assign addr)
  intro x
  exact Fintype.sum_equiv settings _ _ (fun h => congrArg T (funext fun i => read_sample x h i (addr i)))

/-- Each shared address can be placed independently. Two sites may have equal
physical positions, including distinct literal occurrences. -/
theorem price_le {X : Type*} [MetricSpace X] [Fintype I] [Fintype H] [Fintype O]
    [Nonempty (Site H O I)] [Field F]
    (P : SpectralPlacementPrices F X) (T : (I → Bool) → F) (addr : I → Address H O)
    (x : Site H O I → X) :
    P.price (raw (evaluate T addr)) (x ∘ outputSite) ≤ P.price (raw T) (x ∘ site addr) := by
  rw [P.group (raw (evaluate T addr)) outputSite x, P.group (raw T) (site addr) x]
  exact P.placed_mono x (restricts T addr)

end
end Hierarchy.GridAddress

end OAI
