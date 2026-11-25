import OAI.Computability.BorderVNP.ShortenNetworkSew
import OAI.Computability.BorderVNP.PackedGridLanes

/-! # Sewing two trivalent one-bit networks at their matching ports -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FinitePrewire

open Crossing
open scoped BigOperators Classical

variable {D : ℕ} {X Y : Type} [Fintype X] [Fintype Y]
    (O : Network D (Y ⊕ X) (fun _ => 1)) (N : Network D X (fun _ => 1))

/-- The free and the glued terminals are both single-bit ports. -/
private abbrev joinBits : Y ⊕ X → ℕ := Sum.elim (fun _ => 1) (fun _ => 1)

/-- Identical sites, edges, widths and attachments, with the port family
expressed in the two cases consumed by the sewing constructor. -/
abbrev splitOuter : Network D (Y ⊕ X) (joinBits (X := X) (Y := Y)) where
  Site := O.Site
  Edge := O.Edge
  finiteSite := O.finiteSite
  finiteEdge := O.finiteEdge
  src := O.src
  dst := O.dst
  width := O.width
  attach := O.attach
  position := O.position
  in_ball := O.in_ball

omit [Fintype X] [Fintype Y] in
private theorem joinWidth (p : Y ⊕ X) : joinBits p = 1 := by cases p <;> rfl

/-- The outer factors consume the same bit at each public and joining terminal. -/
def splitTables {A : Type*} (table : O.Tables A) : (splitOuter O).Tables A :=
  fun v a y => table v a (fun p i => y p (i.cast (joinWidth p.val).symm))

/-- The network on the remaining free field slots. Each joining cable
replaces one port on either side. -/
abbrev sewn := (splitOuter O).sew N

/-- The actual local factor attached to each old site after sewing. -/
def sewnTables {A : Type*} (ot : O.Tables A) (nt : N.Tables A) : (sewn O N).Tables A :=
  (splitOuter O).sewTables N (splitTables O ot) nt

omit [Fintype Y] in
/-- Matching old and new ports gives the exact pointwise tensor contraction
over one shared choice of each join bit. -/
theorem value_sewn {A : Type*} [CommSemiring A] (ot : O.Tables A) (nt : N.Tables A)
    (y : Y → Bool) :
    (sewn O N).value (sewnTables O N ot nt) (fun p _ => y p) =
    ∑ x : X → Bool, O.value ot (fun p _ => p.elim y x) * N.value nt (fun p _ => x p) := by
  rw [sewnTables, Network.value_sew]
  let eqv : Ports (fun _ : X => 1) ≃ (X → Bool) :=
    Equiv.piCongrRight fun _ => Equiv.funUnique (Fin 1) Bool
  apply Finset.sum_equiv eqv (fun _ => by simp)
  intro z _
  have hz (i : X) (j : Fin 1) : z i j = eqv z i := congrArg (z i) (Subsingleton.elim _ _)
  apply congrArg₂ (· * ·)
  · unfold Network.value
    apply Finset.sum_congr (Finset.ext fun _ => by simp)
    intro a _
    apply Finset.prod_congr (Finset.ext fun _ => by simp)
    intro v _
    apply congrArg (ot v (fun e => a e.val))
    funext p j
    rcases p with ⟨q | i,hp⟩
    · rfl
    · exact hz i _
  · apply congrArg (N.value nt)
    funext i j
    exact hz i j

open private degree_eq from OAI.Computability.BorderVNP.PackedGridLanes

omit [Fintype Y] in
private theorem sewn_edges_sum (f : (sewn O N).Edge → ℕ) :
    (∑ e, f e) = (∑ i : X, f (.inl i)) + (∑ o : O.Edge, f (.inr (.inl o))) +
      (∑ n : N.Edge, f (.inr (.inr n))) := by
  rw [Nat.add_assoc]
  exact (Fintype.sum_sum_type f).trans (congrArg _ (Fintype.sum_sum_type (fun e => f (.inr e))))

private theorem sewn_degree (v : (sewn O N).Site) :
    (sewn O N).bitDegree v = v.elim O.bitDegree N.bitDegree := by
  rcases v with o | n
  · change (sewn O N).bitDegree (.inl o) = O.bitDegree o
    rw [degree_eq (sewn O N) (.inl o), degree_eq O o]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [sewn_edges_sum O N, sewn_edges_sum O N]
    dsimp only [sewn, Network.sew, splitOuter]
    simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Sum.inl.injEq,
      Sum.inr_ne_inl, ite_false, Finset.sum_const_zero, Nat.zero_add, Nat.add_zero]
    omega
  · change (sewn O N).bitDegree (.inr n) = N.bitDegree n
    rw [degree_eq (sewn O N) (.inr n), degree_eq N n]
    simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    rw [sewn_edges_sum O N, sewn_edges_sum O N]
    dsimp only [sewn, Network.sew, splitOuter]
    simp only [Sum.elim_inl, Sum.elim_inr, Sum.inr.injEq, Sum.inl_ne_inr,
      ite_false, Finset.sum_const_zero, Nat.zero_add, Nat.add_zero]
    omega

/-- Trivalence is preserved at every site, including sites with several joining ports. -/
theorem trivalent_sewn (ho : O.Trivalent) (hn : N.Trivalent) : (sewn O N).Trivalent := by
  refine ⟨?_,?_⟩
  · rintro (i | e | e)
    · rfl
    · exact ho.1 e
    · exact hn.1 e
  · intro v
    rw [sewn_degree]
    cases v with
    | inl o => exact ho.2 o
    | inr n => exact hn.2 n

omit [Fintype Y] in
/-- Joining preserves distinct free input leaves when the outer leaves are distinct. -/
theorem sewn_attach_injective (h : Function.Injective O.attach) : Function.Injective (sewn O N).attach :=
  fun _ _ he => Sum.inl.inj (h (Sum.inl.inj he))

/-- Each join becomes one cable and the two consumed ports disappear from the count. -/
theorem sewn_volume : (sewn O N).bitVolume + Fintype.card X = O.bitVolume + N.bitVolume := by
  change Fintype.card (O.Site ⊕ N.Site) + Fintype.card (X ⊕ O.Edge ⊕ N.Edge) +
    Fintype.card Y + Fintype.card X = (Fintype.card O.Site + Fintype.card O.Edge +
    Fintype.card (Y ⊕ X)) + (Fintype.card N.Site + Fintype.card N.Edge + Fintype.card X)
  simp only [Fintype.card_sum]
  omega

end FinitePrewire

end BorderVNP
end Computability
end OAI
