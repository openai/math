import OAI.Hierarchy.ProtocolRAMStoredPurchaseCount
import OAI.Hierarchy.ProbePositiveSampler
import OAI.Hierarchy.ProtocolRAMPurchaseMarketResult
import OAI.Hierarchy.ProtocolRAMPurchaseDensity

namespace OAI
/-! # Purchase density in the single contiguous output of a frozen-market run -/

namespace Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe Filter
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing BigOperators Classical

noncomputable section
variable {z d k : ℕ}

/-- One degree-bounded sampler works for every sufficiently large height, every
permutation, and every prepared frozen stock. Its actual native run places a
linear number of purchase flags in a single contiguous output bank. -/
theorem acquire_of_advised (d k depth : ℕ) (hd : 1≤ d) (hk : 0< k) (T : ℝ) (positive : 0< T)
    (S : PurchaseSampler) (enough : AdvisedCoverage S d k depth T) :
    ∀ᶠ z : ℕ in atTop, ∀ (π : Equiv.Perm (Fin (2^z))) (sh : Shelf)
      (phase : PhasePrice) (kind : ℕ) (frozen fixture : Mem z d),
      sh.Incoming (k:=k) S π depth phase T kind frozen →
      (∀ i : Key z d k, sh.Prepared S depth fixture i frozen) →
      sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies →
      0≤ phase.time → phase.time≤1 →
      (∀ v a,PurchaseCT.stockBits sh.stockBase k frozen v a < sh.table.size) →
      (∀ v a,rise phase.M (phase.quote kind (PurchaseCT.stockBits sh.stockBase k frozen v a))≤1) →
      ((Fintype.card (PurchaseCT.Tile z d):ℝ) ≤ ∑ v, ∑ a, phase.time*
        (rise phase.M (phase.quote kind (PurchaseCT.stockBits sh.stockBase k frozen v a))/T)^2) →
      let out := sh.result S k depth frozen
      (sh.program S z d k depth).Exec frozen out (sh.clock S z d k depth) ∧
        sh.Untouched (k:=k) S depth frozen out ∧
        T^2/(4*k)*((permutationFabric z d).shapes.length*(2:ℝ)^z)/(2*(depth+1:ℕ)) ≤
          (sh.packedCount S k depth out : ℝ) := by
  filter_upwards [enough] with z density
  intro π sh phase kind frozen fixture input prepared room time early small cap energy
  let sets := fun t j => sh.marked phase T kind frozen (key (z:=z) (d:=d) (k:=k) t j)
  have coverage := PurchaseCT.measured_coverage_at sh.stockBase sh.table k hk phase T kind frozen
    positive time early small cap energy
  have sets_eq : sets = PurchaseCT.strataAt sh.stockBase sh.table k phase T kind frozen := by
    funext t j
    dsimp only [sets, marked]
    rw [stage_key, axis_key]
    rfl
  have many := density π sets (by rw [sets_eq]; exact coverage)
  obtain ⟨ran,frame,_,bits⟩ := sh.run S π depth hd phase T kind frozen fixture input prepared room
  refine ⟨ran,frame,?_⟩
  calc
    _ ≤ ∑ t, ∑ j, ((advisedPurchases S π t depth (sets t j)).1.length : ℝ) := many
    _ = _ := by exact_mod_cast (sh.packedCount_eq S π depth phase T kind frozen _ bits).symm

theorem acquire_positive (d k depth : ℕ) (hd : 1≤ d) (hk : 0< k) (T : ℝ) (positive : 0< T) :
    ∃ S : PurchaseSampler, 0<S.degree ∧ ∀ᶠ z : ℕ in atTop, ∀ (π : Equiv.Perm (Fin (2^z))) (sh : Shelf)
      (phase : PhasePrice) (kind : ℕ) (frozen fixture : Mem z d),
      sh.Incoming (k:=k) S π depth phase T kind frozen →
      (∀ i : Key z d k, sh.Prepared S depth fixture i frozen) →
      sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies →
      0≤ phase.time → phase.time≤1 →
      (∀ v a,PurchaseCT.stockBits sh.stockBase k frozen v a < sh.table.size) →
      (∀ v a,rise phase.M (phase.quote kind (PurchaseCT.stockBits sh.stockBase k frozen v a))≤1) →
      ((Fintype.card (PurchaseCT.Tile z d):ℝ) ≤ ∑ v, ∑ a, phase.time*
        (rise phase.M (phase.quote kind (PurchaseCT.stockBits sh.stockBase k frozen v a))/T)^2) →
      let out := sh.result S k depth frozen
      (sh.program S z d k depth).Exec frozen out (sh.clock S z d k depth) ∧
        sh.Untouched (k:=k) S depth frozen out ∧
        T^2/(4*k)*((permutationFabric z d).shapes.length*(2:ℝ)^z)/(2*(depth+1:ℕ)) ≤
          (sh.packedCount S k depth out : ℝ) := by
  let : Nonempty (Fin (2*k)) := ⟨⟨0,by omega⟩⟩
  have kp : (0:ℝ) < k := by exact_mod_cast hk
  obtain ⟨S,degree,enough⟩ := advised_purchases_linear_positive (C:=Fin (2*k)) hd depth (β:=T^2/(4*k)) (by positivity)
  exact ⟨S,degree,acquire_of_advised d k depth hd hk T positive S enough⟩

theorem acquire (d k depth : ℕ) (hd : 1≤ d) (hk : 0< k) (T : ℝ) (positive : 0< T) :
    ∃ S : PurchaseSampler, ∀ᶠ z : ℕ in atTop, ∀ (π : Equiv.Perm (Fin (2^z))) (sh : Shelf)
      (phase : PhasePrice) (kind : ℕ) (frozen fixture : Mem z d),
      sh.Incoming (k:=k) S π depth phase T kind frozen →
      (∀ i : Key z d k, sh.Prepared S depth fixture i frozen) →
      sh.flagsBase S z d k depth+count z d k*paths z S.degree depth<2^wordBits z d copies →
      0≤ phase.time → phase.time≤1 →
      (∀ v a,PurchaseCT.stockBits sh.stockBase k frozen v a < sh.table.size) →
      (∀ v a,rise phase.M (phase.quote kind (PurchaseCT.stockBits sh.stockBase k frozen v a))≤1) →
      ((Fintype.card (PurchaseCT.Tile z d):ℝ) ≤ ∑ v, ∑ a, phase.time*
        (rise phase.M (phase.quote kind (PurchaseCT.stockBits sh.stockBase k frozen v a))/T)^2) →
      let out := sh.result S k depth frozen
      (sh.program S z d k depth).Exec frozen out (sh.clock S z d k depth) ∧
        sh.Untouched (k:=k) S depth frozen out ∧
        T^2/(4*k)*((permutationFabric z d).shapes.length*(2:ℝ)^z)/(2*(depth+1:ℕ)) ≤
          (sh.packedCount S k depth out : ℝ) := by
  obtain ⟨S,_,run⟩:=acquire_positive d k depth hd hk T positive
  exact ⟨S,run⟩

end
end Hierarchy.ProtocolRAM.PurchaseFrozen.Shelf

end OAI
