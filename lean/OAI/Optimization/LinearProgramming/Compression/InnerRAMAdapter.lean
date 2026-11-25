import OAI.Optimization.LinearProgramming.Compression.InnerNative
import OAI.Optimization.LinearProgramming.Compression.SignWireProtocol
import OAI.Optimization.LinearProgramming.Compression.ProxyHomogeneousFuel

/-! Specialize the finite bit service to the real physical sign comparator and its
fixed-size exponent arena. Every reachable ask obeys the checked callback contract. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec _root_.OAI.Optimization.LinearProgramming.Lattice
open scoped BigOperators

noncomputable def coefficientCap (N : ℕ) : ℤ := (2:ℤ)^(manuscriptProxyFuel N-(paperRadius N+7))

theorem coefficientCap_scaled (N : ℕ) : (2:ℤ)^(paperRadius N+7)*coefficientCap N = (2:ℤ)^manuscriptProxyFuel N := by
  have h := manuscript_homogeneous_grid_fuel N 0 (by omega)
  unfold coefficientCap
  rw [← pow_add]
  congr 1
  omega

theorem permitted_coefficientBudget {p N : ℕ} (a : Fin (p+1) → ℤ) (ha : permitted N a) :
    DyadicRAM.coefficientBudget (coefficientCap N) a := by
  have hs : (2:ℤ)^(paperRadius N+7)*(∑ i,|a i|) ≤ (2:ℤ)^(paperRadius N+7)*coefficientCap N := by
    rw [coefficientCap_scaled]; exact ha
  have h : ∑ i, |a i| ≤ coefficientCap N := by
    by_contra hn
    exact (not_lt_of_ge hs) (mul_lt_mul_of_pos_left (lt_of_not_ge hn) (by positivity))
  simpa only [DyadicRAM.coefficientBudget,Fin.sum_univ_castSucc,add_comm (∑ i : Fin p, |a i.castSucc|) |a (Fin.last p)|] using h

/-- The actual rational cache comparator agrees on the native signed row word. -/
theorem cached_matches (N g : ℕ) (mag : ℕ → ℚ) (hm : ∀ i : Fin (g+1), 0 < mag i) :
    «matches» N (fun i : Fin (g+1) => mag i)
      (SignWire.cachedWordOracle (g+1) (manuscriptProxyFuel N) (paperRadius N+7) mag) := by
  intro h a _
  rw [SignWire.cachedWordOracle,wordSignOracle_query,logProxySign_correct _ _ _ _ _ hm]
  rfl

/-- The service's machine witness is directly usable by the registered host callback. -/
theorem machine_for_allowed_clock (N g : ℕ) (hg : g≤paperWidth N) (mem : Bool) (r : ℕ) (hr : r≤g)
    (hv : mem=true → r<g) (v : Fin (g+1) → ℝ) (neg : (Fin (g+1) → ℤ) → ℤ → Bool)
    (hn : ∀ a c, neg a c=true ↔ requestForm v a+c<0) (o : WordOracle) (ho : matchesCoordinates N v o) :
    let arg := inputWord N g mem r
    let out := outputWord (sharedMinorStep N g (position g mem r) neg)
    machine.ComputesWithin o arg (clock.eval N) (fun hist w => w=out ∧ goodHistory N (g+2) hist) ∧
      BitRAM.Dispatch.PermittedAsksFrom machine o (SignWire.AllowedSignPacket (g+1) (clock.eval N) (coefficientCap N) machine)
        (machine.initial arg) ∧ out.length≤clock.eval N := by
  obtain ⟨run,perm,sz⟩ := machine_computes_for_clock N g hg mem r hr hv v neg hn o ho
  refine ⟨run,?_,sz⟩
  intro st j q next before pc ask
  obtain ⟨count,row,wire,hbound⟩ := perm st j q next before pc ask
  exact ⟨count,row,wire,permitted_coefficientBudget row hbound⟩

theorem machine_cached_clock (N g : ℕ) (hg : g≤paperWidth N) (mem : Bool) (r : ℕ) (hr : r≤g)
    (hv : mem=true → r<g) (mag : ℕ → ℚ) (hm : ∀ i : Fin (g+1),0 < mag i) :
    let o := SignWire.cachedWordOracle (g+1) (manuscriptProxyFuel N) (paperRadius N+7) mag
    let arg := inputWord N g mem r
    let out := outputWord (numericalValue N (position g mem r) (fun i : Fin (g+1) => mag i))
    machine.ComputesWithin o arg (clock.eval N) (fun hist w => w=out ∧ goodHistory N (g+2) hist) ∧
      BitRAM.Dispatch.PermittedAsksFrom machine o (SignWire.AllowedSignPacket (g+1) (clock.eval N) (coefficientCap N) machine)
        (machine.initial arg) ∧ out.length≤clock.eval N := by
  let fuel := manuscriptProxyFuel N
  let p := paperRadius N+7
  let data := fun i : Fin (g+1) => mag i
  exact machine_for_allowed_clock N g hg mem r hr hv (generatorProxy fuel p data)
    (requestMagnitudeNegative fuel p data) (requestMagnitudeNegative_correct fuel p data hm) _
    (matches_coordinates_of_magnitudes data hm _ (cached_matches N g mag hm))

theorem machine_cached : ∃ P : Polynomial ℕ, ∀ (N g : ℕ), g≤paperWidth N →
    ∀ (member : Bool) (rank : ℕ), rank≤g → (member=true → rank<g) →
    ∀ (mag : ℕ → ℚ), (∀ i : Fin (g+1), 0 < mag i) →
    let o := SignWire.cachedWordOracle (g+1) (manuscriptProxyFuel N) (paperRadius N+7) mag
    let arg := inputWord N g member rank
    let out := outputWord (numericalValue N (position g member rank) (fun i : Fin (g+1) => mag i))
    machine.ComputesWithin o arg (P.eval N) (fun hist w => w=out ∧ goodHistory N (g+2) hist) ∧
      BitRAM.Dispatch.PermittedAsksFrom machine o (SignWire.AllowedSignPacket (g+1) (P.eval N) (coefficientCap N) machine)
        (machine.initial arg) ∧ out.length≤P.eval N :=
  ⟨clock,machine_cached_clock⟩

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
