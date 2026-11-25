import OAI.Hierarchy.ProbePayloadStrip
import OAI.Hierarchy.ProbeSiteOrder

namespace OAI
/-! # The payload estimate is uniform in the physical order of every strip -/

namespace Hierarchy.AdaptiveProbe.PayloadStrip
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped BigOperators Classical
noncomputable section
universe v

abbrev Site (N k : ℕ) := ColumnSite (Columns N) k
abbrev Naming (N k : ℕ) := Site N k ≃ Fin (Fintype.card (Site N k))

def namedError (F : Type*) [Field F] (N k : ℕ) (name : Naming N k) (M : ℝ)
    (y : Quotes N k → ℝ) : ℝ :=
  letI : SiteNaming (Site N k) := ⟨name⟩
  Probe.discrepancy F (wires N k) (demands N k) (prices N k M y)

private theorem nonnegativeError (F : Type*) [Field F] (N k : ℕ) (name : Naming N k) (M : ℝ)
    (y : Quotes N k → ℝ) : 0≤namedError F N k name M y := by
  let : SiteNaming (Site N k) := ⟨name⟩
  apply Real.sInf_nonneg
  rintro _ ⟨q,rfl⟩
  exact Probe.testError_nonneg _ _ _ _ _ _

/-- Both cutoffs are chosen before the embedding of a particular payload row
in a particular ambient permutation board. -/
theorem sorted_readout {F : Type*} [Field F] (N k : ℕ) (hk : 0<k)
    (no : ¬HasSpectralFlat F (k+1)) {η : ℝ} (tol : 0<η) :
    ∃ K : ℕ, ∀ M ≥ K, ∃ ε : ℝ, 0<ε ∧ ∀ name : Naming N k,
      ∀ y ∈ Set.Icc (0:Quotes N k → ℝ) (ceiling N k M), namedError F N k name M y≤ε →
        y (.inl ())≤η+N*(Real.sqrt (2*k)*η)+∑ t,‖readings N k M y t‖ := by
  let good (e : Naming N k) (M : ℕ) (ε : ℝ) := ∀ y ∈ Set.Icc (0:Quotes N k → ℝ) (ceiling N k M),
    namedError F N k e M y≤ε → y (.inl ())≤η+N*(Real.sqrt (2*k)*η)+∑ t,‖readings N k M y t‖
  apply SiteOrder.common_tolerance good (fun e M _ _ ab h y box pass=>h y box (pass.trans ab))
  intro e
  let : SiteNaming (Site N k) := ⟨e⟩
  obtain ⟨K,each⟩ := readout N k hk no tol
  refine ⟨K+1,?_⟩; intro M large
  exact each M (by exact_mod_cast (show 0<M by omega)) (by exact_mod_cast (show K≤M by omega))

/-- At s=1, low altimeter energy and a sufficiently small sum of real local
discrepancies exclude payload excess. Every payload row may use its own
physical order and the lengths are those of the common layout. -/
theorem payload_mean_le_one {F : Type*} [Field F] (N k : ℕ) (hk : 0<k)
    (no : ¬HasSpectralFlat F (k+1)) {T η : ℝ} (hT : 0≤T) (tol : 0<η)
    (bias : η+N*(Real.sqrt (2*k)*η)+N*T≤1/2) :
    ∃ K : ℕ, ∀ M ≥ K, ∃ ε : ℝ, 0<ε ∧ ∀ (P : Type v) [Fintype P]
      (name : P → Naming N k) (x : Commodity P N k → ℝ),
      (∀ p,rowQuotes x p ∈ Set.Icc (0:Quotes N k → ℝ) (ceiling N k M)) →
      AdaptiveProbe.readings M x ≤ Fintype.card P*(N:ℝ)*T^2 →
      (∑ p,namedError F N k (name p) M (rowQuotes x p))≤Fintype.card P*ε/(2*(N+1)) →
      (∑ p,x (.inl p))≤Fintype.card P := by
  classical
  obtain ⟨K,each⟩ := sorted_readout N k hk no tol
  refine ⟨K,?_⟩; intro M large
  obtain ⟨ε,ep,all⟩ := each M large
  refine ⟨ε,ep,?_⟩; intro P _ name x box energy sums
  let disc (p : P) := namedError F N k (name p) M (rowQuotes x p)
  let bad := Finset.univ.filter (fun p=>ε<disc p)
  have count : (bad.card:ℝ)*ε≤Fintype.card P*ε/(2*(N+1)) :=
    (exceptional_test_mass disc (fun p=>nonnegativeError F N k (name p) M (rowQuotes x p)) ε).trans sums
  have cutoff := (le_div_iff₀ (by positivity : (0:ℝ)<2*(N+1))).mp count
  have ratio : (bad.card:ℝ)*(2*(N+1))≤Fintype.card P := by
    apply (le_of_mul_le_mul_right _ ep)
    linarith [show (bad.card:ℝ)*(2*(N+1))*ε=bad.card*ε*(2*(N+1)) by ring]
  have avg := payload_mass (fun p j=>readings N k M (rowQuotes x p) j) (fun p=>x (.inl p)) bad
    (bias:=η+N*(Real.sqrt (2*k)*η)) (cap:=(N:ℝ)) hT (by positivity) (by positivity)
    (fun p=>(box p).2 (.inl ())) (fun p good=>all (name p) _ (box p)
      (le_of_not_gt (fun h=>good (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))))
    ((row_energy x M).le.trans energy)
  have normalized := mul_le_mul_of_nonneg_left bias (Nat.cast_nonneg (α:=ℝ) (Fintype.card P))
  linarith [Nat.cast_nonneg (α:=ℝ) bad.card]

/-- The public radius and discrepancy threshold can even precede the choice of
the number of tiles, when the advised CT stage count ranges in a fixed interval. -/
theorem all_payload_lengths {F : Type*} [Field F] (L k : ℕ) (hk : 0<k)
    (no : ¬HasSpectralFlat F (k+1)) {T η : ℝ} (hT : 0≤T) (tol : 0<η)
    (bias : ∀ N≤L, η+N*(Real.sqrt (2*k)*η)+N*T≤1/2) :
    ∃ K : ℕ, ∀ M ≥ K, ∃ ε : ℝ, 0<ε ∧ ∀ N≤L, ∀ (P : Type v) [Fintype P]
      (name : P → Naming N k) (x : Commodity P N k → ℝ),
      (∀ p,rowQuotes x p ∈ Set.Icc (0:Quotes N k → ℝ) (ceiling N k M)) →
      AdaptiveProbe.readings M x ≤ Fintype.card P*(N:ℝ)*T^2 →
      (∑ p,namedError F N k (name p) M (rowQuotes x p))≤Fintype.card P*ε/(2*(N+1)) →
      (∑ p,x (.inl p))≤Fintype.card P := by
  let good (j : Fin (L+1)) (M : ℕ) (ε : ℝ) := ∀ (P : Type v) [Fintype P]
    (name : P → Naming j.val k) (x : Commodity P j.val k → ℝ),
    (∀ p,rowQuotes x p ∈ Set.Icc (0:Quotes j.val k → ℝ) (ceiling j.val k M)) →
    AdaptiveProbe.readings M x≤Fintype.card P*(j.val:ℝ)*T^2 →
    (∑ p,namedError F j.val k (name p) M (rowQuotes x p))≤Fintype.card P*ε/(2*(j.val+1)) →
    (∑ p,x (.inl p))≤Fintype.card P
  have mono (j M) {a b : ℝ} (ab : a≤b) (h : good j M b) : good j M a := by
    intro P _ name x box energy lim
    exact h P name x box energy (lim.trans (div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left ab (Nat.cast_nonneg _)) (by positivity)))
  obtain ⟨K,all⟩ := finite_tolerances good mono (fun j=>
    payload_mean_le_one j.val k hk no hT tol (bias j.val (by omega)))
  refine ⟨K,?_⟩; intro M enough
  obtain ⟨ε,ep,use⟩ := all M enough
  exact ⟨ε,ep,fun N bounded=>use ⟨N,by omega⟩⟩

end
end Hierarchy.AdaptiveProbe.PayloadStrip

end OAI
