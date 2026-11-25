import OAI.LinearAlgebra.SpectralBooks.TensorGroupRaw

/-! # Identity and composition of tensor groupings -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SiteTensor.Raw

universe u v
variable {I J : Type u} {D K : Type*} [Fintype I] [Fintype J] [Fintype D] [CommSemiring K]

/-- Grouping first over the fibers of `p` and then of `q` reindexes the local
basis of the tensor grouped directly along their composite. -/
theorem group_group_equivalent (T : Raw.{max u v} I K) (p : I → J) (q : J → D) :
    ((T.group p).group q).Equivalent (T.group (q ∘ p)) := by
  apply reindex_equivalent (X := (T.group p).group q) (Y := T.group (q ∘ p)) (fun d => {
    toFun := fun f t => f ⟨p t.1, t.2⟩ ⟨t.1, rfl⟩
    invFun := fun f j i => f ⟨i.1, (congrArg q i.2).trans j.2⟩
    left_inv := by
      intro f
      funext ⟨j, hj⟩ ⟨i, hi⟩
      change p i = j at hi
      subst j
      rfl
    right_inv := fun _ => rfl })
  intro x
  rfl

/-- Each fiber of the identity has a canonical coordinate, so grouping along
the identity preserves the tensor up to mutual restriction. -/
theorem group_id_equivalent (T : Raw.{max u v} I K) : (T.group id).Equivalent T := by
  apply reindex_equivalent (X := T.group id) (Y := T) (fun i => {
    toFun := fun f => f ⟨i, rfl⟩
    invFun := fun x j => cast (congrArg T.Leg (show i = j.1 from j.2.symm)) x
    left_inv := by
      intro f
      funext ⟨j, hj⟩
      change j = i at hj
      subst j
      rfl
    right_inv := fun _ => rfl })
  intro x
  rfl

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
