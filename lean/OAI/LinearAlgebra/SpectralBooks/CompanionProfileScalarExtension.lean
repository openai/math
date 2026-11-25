import OAI.LinearAlgebra.SpectralBooks.CompanionPaidFromProfile

/-! Transport the certified one-copy decomposition to the field where the companion
measures its image closure. Every table entry is mapped by the supplied ring homomorphism. -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace CompanionBridge

open scoped BigOperators Classical
open OAI.Computability.BorderVNP.Crossing
noncomputable section
variable {K L : Type*} [Field K] [Field L] {D m : ℕ}

def mapPaid (φ : K →+* L) (e : PaidIdentity K D m) : PaidIdentity L D m where
  count := e.count
  net := e.net
  table := fun a v s x => φ (e.table a v s x)
  placed := e.placed
  identity x := by
    calc
      antipodalTensor L D m x = φ (antipodalTensor K D m x) := by simp [antipodalTensor, apply_ite]
      _ = φ (∑ a, (e.net a).value (e.table a) x) := congrArg φ (e.identity x)
      _ = ∑ a, (e.net a).value (fun v s u => φ (e.table a v s u)) x := by
        simp [Network.value, Network.read, map_sum, map_prod]
  cap := e.cap
  cost_le := e.cost_le
  strict := e.strict

theorem companionProfile_map (φ : K →+* L) (hD : 2 ≤ D) (h : Crossing.HasProfileShortening K D) :
    OAI.Computability.BorderVNP.Crossing.HasProfileShortening L := by
  obtain ⟨m,hm,⟨e⟩⟩ := paidIdentity_of_profile hD h
  exact ⟨D,hD,m,hm,(mapPaid φ e).profileShortening (by omega) hm⟩

theorem companionProfile_algebraicClosure (hD : 2 ≤ D) (h : Crossing.HasProfileShortening K D) :
    OAI.Computability.BorderVNP.Crossing.HasProfileShortening (AlgebraicClosure K) :=
  companionProfile_map (algebraMap K (AlgebraicClosure K)) hD h

end
end CompanionBridge

end SpectralBooks
end LinearAlgebra
end OAI
