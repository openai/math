import OAI.Hierarchy.ProbeStrip
import OAI.Hierarchy.ProbePayload
import OAI.Hierarchy.ProbeExcess

namespace OAI
/-! # Recovering a payload price from its own physical strip of signed altimeters -/

namespace Hierarchy.AdaptiveProbe.PayloadStrip
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open scoped Classical BigOperators
noncomputable section

universe v

abbrev edgeCount (N : ℕ) := 2*N+1
abbrev Columns (N : ℕ) := TestColumns (Strip.steps (edgeCount N)) 0 (edgeCount N)
abbrev Quotes (N k : ℕ) := Unit ⊕ (Fin N × (Fin k × Bool))

/-- The site before the j-th free join. At j=N the join goes to the output. -/
def first (N : ℕ) (j : Fin (N+1)) : Columns N := Strip.column _ ⟨2*j.val,by have := j.isLt; dsimp [edgeCount]; omega⟩
def last (N : ℕ) (j : Fin (N+1)) : Columns N := Strip.column _ ⟨2*j.val+1,by have := j.isLt; dsimp [edgeCount]; omega⟩

def length (N : ℕ) (e : Fin (edgeCount N)) : ℝ := if e.val%2=0 then 0 else 1

def external (N : ℕ) : DistinctPair (Columns N) :=
  ⟨first N 0,last N (Fin.last N),fun h=>by
    have t := congrArg (fun c : Columns N=>c.val.val) h
    change 2*0=2*N+1 at t
    omega⟩

def commodity (N k : ℕ) : Quotes N k → LocalCommodity (Columns N) k
  | .inl _ => .payload (external N)
  | .inr (j,u) => .altimeter (last N j.castSucc) (first N j.succ) u.1 u.2

def noProbe (N : ℕ) : Empty → DistinctPair (Columns N) := Empty.elim
def ceiling (N k : ℕ) (M : ℝ) : Quotes N k → ℝ := Sum.elim (fun _=>N) (fun _=>M+1)

abbrev wires (N k : ℕ) [SiteNaming (ColumnSite (Columns N) k)] := ColumnWires.wires (Strip.horizontal (edgeCount N))
  (LocalCommodity.extraEnds (commodity N k) (noProbe N))
abbrev demands (N k : ℕ) := ColumnWires.demand (I:=Columns N) (H:=Fin (edgeCount N)) (k:=k)
  (Sum.inl (α:=Quotes N k) (β:=Empty))
abbrev prices (N k : ℕ) (M : ℝ) (y : Quotes N k → ℝ) := ColumnWires.quote (I:=Columns N) (k:=k)
  M (length N) (LocalCommodity.extraPrice (B:=Empty) y)

instance (N : ℕ) : Nonempty (Columns N) := ⟨first N 0⟩
instance (N k : ℕ) : Nonempty (ColumnWires.Role (Columns N) (Fin (edgeCount N)) (Quotes N k ⊕ Empty) k) :=
  ⟨.extra (.inl (.inl ()))⟩
instance (N k : ℕ) : Nonempty (Fin (Fintype.card (ColumnSite (Columns N) k))) :=
  Fin.pos_iff_nonempty.mp (Fintype.card_pos (α:=ColumnSite (Columns N) k))

def readings (N k : ℕ) (M : ℝ) (y : Quotes N k → ℝ) (j : Fin N) :
    EuclideanSpace ℝ (Fin k × Bool) :=
  WithLp.toLp 2 fun u=>rise M (y (.inr (j,u)))

/-- Restrict the global live quote tape to one physical payload row. -/
def rowQuotes {P : Type*} {N k : ℕ} (x : Commodity P N k → ℝ) (p : P) : Quotes N k → ℝ
  | .inl _ => x (.inl p)
  | .inr (t,j) => x (.inr ((p,t),j))

/-- Every global altimeter occurs on exactly one payload row and tile. -/
theorem row_energy {P : Type*} [Fintype P] {N k : ℕ} (x : Commodity P N k → ℝ) (M : ℝ) :
    (∑ p,∑ j,‖readings N k M (rowQuotes x p) j‖^2)=AdaptiveProbe.readings M x := by
  simp [AdaptiveProbe.readings,Fintype.sum_prod_type,EuclideanSpace.norm_sq_eq,
    readings,rowQuotes,Real.norm_eq_abs,sq_abs]

/-- One and the same set of frame coordinates witnesses both the endpoint
price estimate and every signed tile reading. This includes the two external
zero-cost joins. -/
theorem frames {F : Type*} [Field F] (N k : ℕ) [SiteNaming (ColumnSite (Columns N) k)] (hk : 0<k)
    (no : ¬ HasSpectralFlat F (k+1)) {η : ℝ} (res : 0<η) :
    ∃ M₀ : ℕ, ∀ M : ℝ, 0<M → M₀≤M → ∃ ε : ℝ, 0<ε ∧
    ∀ y ∈ Set.Icc (0:Quotes N k → ℝ) (ceiling N k M),
      Probe.discrepancy F (wires N k) (demands N k) (prices N k M y)≤ε →
      ∃ path : ℕ → Coordinates k,
        y (.inl ())≤η+‖path N-path 0‖ ∧
        ∀ (t : Fin N) j, |signedVector (path (t.val+1)-path t.val) j-readings N k M y t j|≤η := by
  have bound : ∀ e,length N e≤1 := by intro e; unfold length; split <;> norm_num
  obtain ⟨K,work⟩ := Strip.strip_flattening hk no (length N) bound (commodity N k) (noProbe N) res
  refine ⟨K,?_⟩; intro M pm large
  obtain ⟨ε,ep,all⟩ := work M pm large (ceiling N k M)
  refine ⟨ε,ep,?_⟩; intro y within pass
  obtain ⟨z,joined,obs⟩ := all y within pass
  have free (j : Fin (N+1)) : z (first N j)=z (last N j) := by
    let e : Fin (edgeCount N) := ⟨2*j.val,by have := j.isLt; dsimp [edgeCount]; omega⟩
    have zero : length N e=0 := by simp [length,e]
    exact joined e zero
  let path (j : ℕ) := z (first N ⟨min j N,Nat.lt_succ_of_le (min_le_right ..)⟩)
  have atSite (j : Fin (N+1)) : path j.val=z (first N j) := by
    have eq : min j.val N=j.val := min_eq_left (by omega)
    simp [path,eq]
  refine ⟨path,?_,?_⟩
  · have h := obs (.inl (Sum.inl ()))
    change |y (.inl ())-dist (z (first N 0)) (z (last N (Fin.last N)))|<η at h
    have start := atSite (0:Fin (N+1))
    have finish := (atSite (Fin.last N)).trans (free (Fin.last N))
    change path 0=_ at start
    change path N=_ at finish
    rw [←start,←finish,dist_comm,dist_eq_norm] at h
    linarith [(abs_lt.mp h).2]
  · rintro t ⟨j,sign⟩
    have h := obs (.inl (Sum.inr (t,(j,sign))))
    change |rise M (y (.inr (t,(j,sign)))) -
      max (Source.sign sign*(z (first N t.succ) j-z (last N t.castSucc) j)) 0|<η at h
    have before := (atSite t.castSucc).trans (free t.castSucc)
    have after := atSite t.succ
    change path t.val=_ at before
    change path (t.val+1)=_ at after
    rw [←before,←after,abs_sub_comm] at h
    cases sign <;> simpa [signedVector,readings,Source.sign] using h.le

/-- Small discrepancy for the concrete physical quotes bounds the payload
price by the measured readings on the N signed tiles of this route. -/
theorem readout {F : Type*} [Field F] (N k : ℕ) [SiteNaming (ColumnSite (Columns N) k)] (hk : 0<k)
    (no : ¬ HasSpectralFlat F (k+1)) {η : ℝ} (res : 0<η) :
    ∃ M₀ : ℕ, ∀ M : ℝ, 0<M → M₀≤M → ∃ ε : ℝ, 0<ε ∧
    ∀ y ∈ Set.Icc (0:Quotes N k → ℝ) (ceiling N k M),
      Probe.discrepancy F (wires N k) (demands N k) (prices N k M y)≤ε →
      y (.inl ())≤η+N*(Real.sqrt (2*k)*η)+∑ j,‖readings N k M y j‖ := by
  obtain ⟨K,go⟩ := frames N k hk no res
  refine ⟨K,?_⟩; intro M pos large
  obtain ⟨ε,ep,all⟩ := go M pos large
  refine ⟨ε,ep,?_⟩; intro y box pass
  obtain ⟨z,ends,close⟩ := all y box pass
  exact payload_path z (readings N k M y) res.le ends close

/-- The total measured discrepancy pays for all exceptional payloads. The
threshold is fixed before the number of routed payloads or their prices. -/
theorem total_readout {F : Type*} [Field F] (N k : ℕ) [SiteNaming (ColumnSite (Columns N) k)] (hk : 0<k)
    (no : ¬ HasSpectralFlat F (k+1)) {η : ℝ} (res : 0<η) :
    ∃ M₀ : ℕ, ∀ M : ℝ, 0<M → M₀≤M → ∃ ε : ℝ, 0<ε ∧
    ∀ (P : Type v) [Fintype P] (y : P → Quotes N k → ℝ) (T : ℝ), 0≤T →
      (∀ p,y p ∈ Set.Icc (0:Quotes N k → ℝ) (ceiling N k M)) →
      (∑ p,∑ j,‖readings N k M (y p) j‖^2)≤Fintype.card P*(N:ℝ)*T^2 →
      (∑ p,y p (.inl ()))≤Fintype.card P*(η+N*(Real.sqrt (2*k)*η))+
        Fintype.card P*(N:ℝ)*T+
        ((∑ p, Probe.discrepancy F (wires N k) (demands N k) (prices N k M (y p)))/ε)*N := by
  classical
  obtain ⟨K,go⟩ := readout N k hk no res
  refine ⟨K,?_⟩; intro M pos large
  obtain ⟨ε,ep,all⟩ := go M pos large
  refine ⟨ε,ep,?_⟩; intro P _ y T ht box energy
  let disc (p : P) := Probe.discrepancy F (wires N k) (demands N k) (prices N k M (y p))
  let bad := Finset.univ.filter (fun p=>ε<disc p)
  have nn (p : P) : 0≤disc p := by
    apply Real.sInf_nonneg
    rintro _ ⟨t,rfl⟩
    exact Probe.testError_nonneg _ _ _ _ _ _
  have few : (bad.card:ℝ)≤(∑ p,disc p)/ε :=
    (le_div_iff₀ ep).2 (exceptional_test_mass disc nn ε)
  have avg := payload_mass (fun p j=>readings N k M (y p) j) (fun p=>y p (.inl ())) bad
    (bias:=η+N*(Real.sqrt (2*k)*η)) (cap:=(N:ℝ)) ht (by positivity) (by positivity)
    (fun p=>(box p).2 (.inl ())) (fun p good=>all (y p) (box p)
      (le_of_not_gt (fun h=>good (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩)))) energy
  apply avg.trans
  exact add_le_add_right (mul_le_mul_of_nonneg_right few (Nat.cast_nonneg (α:=ℝ) N)) _

end
end Hierarchy.AdaptiveProbe.PayloadStrip

end OAI
