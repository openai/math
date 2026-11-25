import OAI.Computability.NearSquareRoot.SynchronizedRoutedWalsh
import OAI.Computability.NearSquareRoot.SynchronizedRoutingEmbedding
import OAI.Computability.NearSquareRoot.SynchronizedPlacedMatching

/-! # Eight-slot lowering of a placed batch butterfly

The routing table begins with the two endpoints of every placed pair, in the
given enumeration. Its suffix pairs up all remaining cells in physical order.
The corresponding eight-slot word acts by all the placed butterflies at once.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier.RoutedWalsh

variable {X J C A : Type} {m n : ℕ}
  (f : X ≃ Fin 2 × C) (e : X × J ↪ A) (rank : A ≃ Fin n) (labels : C × J ≃ Fin m)

/-- Physical endpoint at a given bit and active-pair number. -/
def endpoints : Fin 2 × Fin m ↪ Fin n where
  toFun p := rank (e (f.symm (p.1, (labels.symm p.2).1), (labels.symm p.2).2))
  inj' := by
    rintro ⟨b,q⟩ ⟨b',q'⟩ h
    have hp := e.injective (rank.injective h)
    have hb := f.symm.injective (congrArg Prod.fst hp)
    have hbit : b = b' := congrArg (fun x : Fin 2 × C => x.1) hb
    have hc : (labels.symm q).1 = (labels.symm q').1 := congrArg (fun x : Fin 2 × C => x.2) hb
    have hj : (labels.symm q).2 = (labels.symm q').2 := congrArg (fun x : X × J => x.2) hp
    exact Prod.ext hbit (labels.symm.injective (Prod.ext hc hj))

include f e rank labels in
private theorem enough_pairs : m ≤ n / 2 := by
  have hc := Fintype.card_le_of_embedding (endpoints f e rank labels)
  simp only [Fintype.card_prod, Fintype.card_fin] at hc
  omega

/-- The label of an active pair in the completed table of all physical pairs. -/
def pairNumber (q : C × J) : Fin (n / 2) :=
  Fin.castLE (enough_pairs f e rank labels) (labels q)

/-- The complete matching used by the endpoint-list routing program. -/
def routeMatching (he : Even n) : Fin 2 × Fin (n / 2) ≃ A :=
  let E := endpoints f e rank labels
  (RoutingTable.matching he (RoutingTable.activePairs E) (RoutingTable.activePairs_nodup E)).trans rank.symm

theorem routeMatching_active (he : Even n) (bit : Fin 2) (c : C) (j : J) :
    routeMatching f e rank labels he (bit, pairNumber f e rank labels (c,j)) =
      e (f.symm (bit,c),j) := by
  let E := endpoints f e rank labels
  obtain ⟨hi,h⟩ := RoutingTable.pairAt E he bit (labels (c,j))
  change rank.symm (RoutingTable.matching he (RoutingTable.activePairs E) (RoutingTable.activePairs_nodup E)
    (bit, ⟨(labels (c,j)).val,hi⟩)) = _
  rw [h]
  change rank.symm (rank (e (f.symm (bit,(labels.symm (labels (c,j))).1),
    (labels.symm (labels (c,j))).2))) = _
  simp

/-- The active part of the completed matching occupies precisely its numeric prefix. -/
theorem active_iff_range (s : Fin (n / 2)) :
    decide (s.val < m) = true ↔ s ∈ Set.range (pairNumber f e rank labels) := by
  rw [decide_eq_true_eq]
  constructor
  · intro hs
    exact ⟨labels.symm ⟨s.val, hs⟩, Fin.ext (by simp [pairNumber])⟩
  · rintro ⟨q,rfl⟩
    exact (labels q).isLt

/-- The route, three fixed-bit Walsh/phase rounds, and return route. -/
noncomputable def routingCode (bits : A ≃ Fin 2 × Fin (n / 2))
    (f : X ≃ Fin 2 × C) (e : X × J ↪ A) (rank : A ≃ Fin n) (labels : C × J ≃ Fin m)
    (he : Even n) : List (Slot A) :=
  code bits (routeMatching f e rank labels he) (fun s => decide (s.val < m))

@[simp] theorem routingCode_length (bits : A ≃ Fin 2 × Fin (n / 2)) (he : Even n) :
    (routingCode bits f e rank labels he).length = 8 := rfl

/-- The actual placement matrix, with the identity on every unused cell, is the
product of the explicit eight slots computed from its endpoint table. -/
theorem routingCode_prod [Fintype X] [DecidableEq X] [Fintype C] [DecidableEq C]
    [Fintype J] [DecidableEq J] [Fintype A] [DecidableEq A]
    (bits : A ≃ Fin 2 × Fin (n / 2))
    (f : X ≃ Fin 2 × C) (e : X × J ↪ A) (rank : A ≃ Fin n) (labels : C × J ≃ Fin m)
    (he : Even n) :
    ((routingCode bits f e rank labels he).map (Slot.matrix bits)).prod =
      placeHom e (Slot.matrix f .walsh) := by
  rw [routingCode, code_prod]
  exact (placeWalsh_matching f e (routeMatching f e rank labels he) (pairNumber f e rank labels)
    (fun s => decide (s.val < m)) (active_iff_range f e rank labels)
    (routeMatching_active f e rank labels he)).symm

end ShortFourier.RoutedWalsh

end NearSquareRoot
end Computability
end OAI
