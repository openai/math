import OAI.LinearAlgebra.SpectralBooks.SiteTensor.Ops

/-! # Extending a tensor by one-dimensional slots -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

open scoped BigOperators Classical
universe v u w z

noncomputable section

variable {S : Type u} (O : Type z) {K : Type w}

/-- Adjoin one scalar leg at every site outside the occupied set. -/
def withTrivial (X : Raw.{v} S K) : Raw.{v} (S ⊕ O) K where
  Leg := Sum.elim X.Leg (fun _ => PUnit)
  finiteLeg := Sum.rec (fun s => X.finiteLeg s) (fun _ => inferInstanceAs (Fintype PUnit))
  coeff x := X.coeff (fun s => x (.inl s))

/-- Reading the occupied coordinates is a bijection on basis positions. -/
def withTrivialIndex (X : Raw.{v} S K) :
    (∀ i, (withTrivial O X).Leg i) ≃ (∀ s, X.Leg s) where
  toFun x s := x (.inl s)
  invFun x := Sum.rec x fun _ => PUnit.unit
  left_inv x := by funext i; cases i <;> rfl
  right_inv _ := rfl

variable [Fintype S] [Fintype O] [CommSemiring K]

/-- A restriction on the occupied sites acts as identity on the scalar slots. -/
theorem withTrivial_restricts {X Y : Raw.{v} S K} (h : X.Restricts Y) :
    (withTrivial O X).Restricts (withTrivial O Y) := by
  classical
  let : DecidableEq (S ⊕ O) := Classical.decEq _
  obtain ⟨M, hM⟩ := h
  let N (i : S ⊕ O) : (withTrivial O X).Leg i → (withTrivial O Y).Leg i → K :=
    match i with
    | .inl s => M s
    | .inr _ => fun _ _ => 1
  refine ⟨N, fun x => ?_⟩
  rw [show (withTrivial O X).coeff x = _ from hM (fun s => x (.inl s))]
  exact Fintype.sum_equiv (withTrivialIndex O Y).symm _ _ (fun a => by
    simp [withTrivialIndex, withTrivial, Fintype.prod_sum_type, N]
    rfl)

/-- Extension preserves grouped tensor products up to local reindexing. -/
theorem withTrivial_mul_equivalent (X Y : Raw.{v} S K) :
    (withTrivial O (mul X Y)).Equivalent (mul (withTrivial O X) (withTrivial O Y)) := by
  let e (i : S ⊕ O) : (withTrivial O (mul X Y)).Leg i ≃
      (mul (withTrivial O X) (withTrivial O Y)).Leg i := match i with
    | .inl _ => Equiv.refl _
    | .inr _ => ⟨fun _ => (PUnit.unit, PUnit.unit), fun _ => PUnit.unit, fun _ => rfl, fun _ => rfl⟩
  exact reindex_equivalent e (fun _ => rfl)

theorem withTrivial_one_equivalent :
    (withTrivial O (one S K : Raw.{v} S K)).Equivalent (one (S ⊕ O) K) := by
  apply reindex_equivalent (fun i => ?_)
  · intro x; rfl
  · cases i <;> exact Equiv.refl _

end
end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
