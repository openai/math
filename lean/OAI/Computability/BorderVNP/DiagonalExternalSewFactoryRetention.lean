import OAI.Computability.BorderVNP.DiagonalExternalSewAncestry
import OAI.Computability.BorderVNP.PackedSiteEpochs

/-! # Iterating the site map of an actual packing factory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing Shortening Adaptive Packing Packing.PhysicalEpochs

variable {D : ℕ} {P K : Type} [Fintype P] [Field K] {bits : P → ℕ}
    (F : Factory D K) {start T : ℕ} (deep : F.floor+1+F.drop*T ≤ start)

/-- Each actual local epoch retains the child boxes at the vertices of its
own chosen profile. Both a direct and an input-sorted crossing can supply
this address map. -/
abbrev FactoryStepHosts := ∀ (n : ℕ) (_ : n < T) (c : Fin F.fan → F.State bits start n)
    (q : (F.epoch deep n c).Index), Retains (parallelPacks fun i => (c i).pack).layout
      ((F.epoch deep n c).term q).pack.layout

variable (step : FactoryStepHosts (bits := bits) F deep) (bottom : F.State bits start 0)

/-- Compose the true per-epoch site maps on the nested history, prefixing
each branch by its own child number. -/
noncomputable def factoryNestedHosts :
    (n : ℕ) → (hn : n ≤ T) → (q : (F.histories deep bottom n).Index) →
    Retains (parallelLeaves (fun _ : Unit => bottom.pack) n (leavesEquiv F.fan Unit n fun _ => ())).layout
      ((F.histories deep bottom n).term q).pack.layout
  | 0, _, _ => Retains.id _
  | n+1, hn, q => by
    let H := F.histories deep bottom n
    let c := fun i : Fin F.fan => H.term (q.1 i)
    exact (Retains.parallel fun i => factoryNestedHosts n (Nat.le_of_succ_le hn) (q.1 i)).trans
      (step n (Nat.lt_of_succ_le hn) c q.2)

/-- Original vertex addresses for the true flattened outputs of the whole
factory, with the leaf number in the outer row-major order. -/
noncomputable def factoryOuterHosts (q : (F.histories deep bottom T).Index) :
    Retains (parallelPacks (fun _ : Fin (F.fan^T) => bottom.pack)).layout
      (flattenPack T ((F.histories deep bottom T).term q).pack).layout :=
  (flatOriginal (fun _ : Unit => bottom.pack) T (fun _ => ())).trans
    (factoryNestedHosts F deep step bottom T le_rfl q).flat

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
