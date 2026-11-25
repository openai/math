import OAI.Computability.BorderVNP.PackedHistoryRealizedSchedule

/-! # Geometric cost receipts on the actual selected processor rectangles -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule

open Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Cover Shortening Adaptive Packing PublicCapacity
open Diagonal TeamScales Filter EnrichedOuter VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
variable {P : Type} [Fintype P] {bits : P → ℕ} {r n start T : ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}
variable (R : Compiled bits deep budget cap (60*logWidth r n))

/-- The actual geometric gate lists, child guards and count pins of one chosen processor
obey a single uniform bound per reserved site, cable and tile. -/
structure Compiled.GeometryRows (A p : ℕ) : Prop where
  pre : ∀ t ht, (R.atLevel t ht).pre.size ≤ rowWork A (CoverScale.sites (Cube D) start)
    (logWidth r n) p (boundaryShape S start t)
  post : ∀ t ht, (R.atLevel t ht).post.size ≤ rowWork A (CoverScale.sites (Cube D) start)
    (logWidth r n) p (boundaryShape S start (t+1))
  nodes : ∀ t ht (i : Fin S.rounds),
    (R.nodes t ht i).size+(2*S.fanIn+4)+Fintype.card (Count S start t (fun _ => 60*logWidth r n) i.val) ≤
      rowWork A (CoverScale.sites (Cube D) start) (logWidth r n) p ((before S start t i).parallel S.fanIn)

/-- Increase the common cost coefficient or degree, preserving a per-row upper bound. -/
theorem rowWork_mono {A B p q V L : ℕ} (s : Shape) (hl : 1 ≤ L) (coef : A ≤ B) (exp : p ≤ q) :
    rowWork A V L p s ≤ rowWork B V L q s :=
  Nat.mul_le_mul (Nat.mul_le_mul_right _ coef) (Nat.pow_le_pow_right hl exp)

/-- The processor word range absorbs both geometric boundary polynomials. The
same constants apply to every previously selected compilation with these local receipts. -/
theorem eventually_geometryRows_of_localSizes (S : SiteSchedule e) {a x : ℕ} (scales : EpochScales S a x)
    (A a₀ B b J j : ℕ) :
    ∃ F u : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      let T := epochs scales.τ n
      let start := CoverScale.initialDepth (Cube D) r n
      ∀ (deep : S.floor+1+S.drop*T ≤ start) {P : Type} [Fintype P] {bits : P → ℕ}
        {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ} (R : Compiled bits deep budget cap (60*logWidth r n)),
        Machine.LocalSizes (r:=r) (n:=n) A a₀ B b J j R.machine → R.GeometryRows (r:=r) (n:=n) F u := by
  obtain ⟨H,h,bound⟩ := boundary_costs (Cube D) 60 (Fintype.card (Cube D)) (interiors S) A a₀ B b (fan S)
  refine ⟨H+2*J,max h j,?_⟩
  filter_upwards [eventually_boundaries S scales,eventually_ge_atTop 1] with n rows hn
  intro r hr T start deep P _ bits budget cap R raw
  have hL : 1 ≤ logWidth r n := by
    rw [public_logWidth]
    exact (Nat.clog_mono_right 2 (by nlinarith [Nat.mul_le_mul hn hr] : 2≤2*n*r)).trans' (by decide)
  constructor
  · intro t ht
    have hd : S.high (offset S start t) ≤ start+1 := by
      rw [(levels S deep ht).2.2]
      dsimp [EnrichedOuter.depth]
      omega
    have geom := (bound (z:=start+1) (boundaryShape S start t) hr hn ((rows r hr).1 t ht.le) hd le_rfl).1
    exact (raw.subdivision t ht).trans (geom.trans (rowWork_mono _ hL (by omega) (le_max_left ..)))
  · intro t ht
    have hd : offset S start t ≤ start+1 := by dsimp [offset,EnrichedOuter.depth]; omega
    have geom := (bound (z:=start+1) (boundaryShape S start (t+1)) hr hn ((rows r hr).1 (t+1) ht) hd le_rfl).2
    exact (raw.terminal t ht).trans (geom.trans (rowWork_mono _ hL (by omega) (le_max_left ..)))
  · intro t ht i
    have gates := raw.round t ht i.val i.isLt
    rw [R.node_size t ht i] at gates
    let sub := (before S start t i).parallel S.fanIn
    let W := rowWork J (CoverScale.sites (Cube D) start) (logWidth r n) j sub
    have add := Nat.add_le_add gates (raw.counts t ht i.val i.isLt)
    have twice : W+W = rowWork (2*J) (CoverScale.sites (Cube D) start) (logWidth r n) j sub := by
      unfold W rowWork; ring
    exact add.trans (twice.le.trans (rowWork_mono sub hL (by omega) (le_max_right ..)))

/-- All calibrated processors have a single selected compilation realizing the geometric
semantics and uniform rectangular costs. Its gate bounds can be reused when emitting
additional width columns from these same named nodes. -/
theorem eventually_compiled_geometryRows (S : SiteSchedule e) (hm : 0 < m) {a x : ℕ} (scales : EpochScales S a x)
    (physical : ∀ d ≥ S.floor, S.FitsLevels d ∧ S.HasLeaves d ∧ S.RunsEnriched.{1,0} d) :
    ∃ A p : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1 ≤ r →
      ∀ base : ℕ, 1+base ≤ TeamScales.width n (1/2:ℝ) →
      ∀ (P : Type) [Fintype P] (bits : P → ℕ),
        let T := epochs scales.τ n
        let start := CoverScale.initialDepth (Cube D) r n
        ∃ deep : S.floor+1+S.drop*T ≤ start,
        ∃ R : Compiled bits deep (boundaryBudget S base) (innerCap S base) (60*logWidth r n),
          R.GeometryRows (n:=n) (r:=r) A p := by
  obtain ⟨A,a₀,B,b,J,j,make⟩ := eventually_compiled S hm scales physical
  obtain ⟨F,u,measure⟩ := eventually_geometryRows_of_localSizes S scales A a₀ B b J j
  refine ⟨F,u,?_⟩
  filter_upwards [make,measure] with n comp cost
  intro r hr base hbase P _ bits T start
  obtain ⟨deep,R,raw⟩ := comp r hr base hbase P bits
  refine ⟨deep,R,cost r hr deep R ?_⟩
  refine ⟨fun t ht => (raw t ht).1,fun t ht => (raw t ht).2.1,?_,?_⟩
  · intro t ht i hi
    exact (Nat.le_add_right _ _).trans ((raw t ht).2.2 ⟨i,hi⟩)
  · intro t ht i hi
    have pins := (Fintype.card_congr (Physical.pinEquiv (I := Cube D) (e := e)
      (B := fun i => (S.source.pattern i).bins.Bin) (depth := S.level (offset S start t))
      (fun _ => 60*logWidth r n) ⟨i,hi⟩)).symm
    exact pins.le.trans ((Nat.le_add_left _ _).trans ((raw t ht).2.2 ⟨i,hi⟩))

end PackedHistoryCircuit.Normalized.SelectedSchedule

end BorderVNP
end Computability
end OAI
