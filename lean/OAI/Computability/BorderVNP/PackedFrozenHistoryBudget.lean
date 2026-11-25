import OAI.Computability.BorderVNP.PackedFrozenSelectedReturn
import OAI.Computability.BorderVNP.PackedHistoryRealizedSchedule

/-! # The complete public tree including frozen records, widths and histogram words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

open Crossing Cover BorderVNP.Epoch Packing Shortening PublicCapacity Diagonal TeamScales Filter
open Inherited FrozenTape ProgramSchemas EnrichedOuter VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} {S : SiteSchedule e}
    {n r start T : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {deep : S.floor+1+S.drop*T ≤ start}
    {budget : ℕ → ℕ} {cap : ℕ → ℕ → ℕ}

local notation3 "word" => 60*logWidth r n
local notation3 "tiles" => CoverScale.sites (Cube D) start

/-- Per-rectangle charges of the actual additional frozen-tape and work/extent
gates. The fixed multiple of the original selected pass allows reading its
old-only population table, routing and saved geometry on this same node. -/
structure TapeCosts {σ : Type} [Fintype σ] (multiplier C exponent : ℕ)
    (R : Compiled bits deep budget cap word) (base : Format)
    (f : Frame σ (outerPins S start word base 0))
    (pre : ∀ t, t<T → Frame (Fin (fan S) × outerPins S start word base t)
      (Fin (fan S) × stagePins S start word base t 0))
    (nodes : ∀ t, t<T → Steps S.fanIn S.rounds (stagePins S start word base t) (Count S start t (fun _ => word))) : Prop where
  /-- The original grouped grid, its two width fields and its immutable birth records. -/
  leaf : f.size+1 ≤ rowWork C tiles (logWidth r n) exponent (bottom (D:=D) start)
  /-- Full batched subdivisions, owner translations and added relay rows. -/
  subdivision : ∀ t ht, (pre t ht).size ≤ multiplier*(R.machine t ht).pre.size+
    rowWork C tiles (logWidth r n) exponent (boundaryShape S start t)
  /-- Actual selected branch on the same pins, including all chronology, delivery and width updates. -/
  round : ∀ t ht i (hi : i<S.rounds), (nodes t ht i hi).size+(2*S.fanIn+4) ≤
    multiplier*((R.machine t ht).step i hi).size+
      rowWork C tiles (logWidth r n) exponent ((before S start t i).parallel S.fanIn)

private theorem work_mono {c c' u u' V L : ℕ} (shape : Shape)
    (hc : c≤c') (hu : u≤u') (hL : 1≤L) : rowWork c V L u shape ≤ rowWork c' V L u' shape :=
  Nat.mul_le_mul (Nat.mul_le_mul_right _ hc) (Nat.pow_le_pow_right hL hu)

private theorem add_work {k c f u v U V L : ℕ} (shape : Shape) (hu : u≤U) (hv : v≤U) (hL : 1≤L) :
    k*rowWork c V L u shape+rowWork f V L v shape ≤ rowWork (k*c+f) V L U shape := by
  have a := work_mono (V:=V) (L:=L) shape (le_refl c) hu hL
  have b := work_mono (V:=V) (L:=L) shape (le_refl f) hv hL
  exact (Nat.add_le_add (Nat.mul_le_mul_left k a) b).trans_eq (by unfold rowWork; ring)

variable (S) (A a B b J j multiplier fresh extra Q : ℕ)

set_option maxHeartbeats 1500000 in
/-- The complete augmented computation has the same guessed count pins as the
physical source. Each stage reads the public frozen chronology from its actual
predecessors. The seam forwards the root tape without another computation. -/
theorem eventually_tape_budget {p x : ℕ} (scales : EpochScales S p x) :
    ∃ ω : ℝ, 0<ω ∧ ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r → (r:ℝ)≤2^((n:ℝ)^ω) →
      let T := epochs scales.τ n
      let start := CoverScale.initialDepth (Cube D) r n
      let w := 60*logWidth r n
      ∀ (P : Type) [Fintype P] (bits : P → ℕ) (deep : S.floor+1+S.drop*T ≤ start)
        (budget : ℕ → ℕ) (cap : ℕ → ℕ → ℕ) (R : Compiled bits deep budget cap w),
        Machine.LocalSizes (r:=r) (n:=n) A a B b J j R.machine → ∀ (base : Format) {σ : Type} [Fintype σ]
        (f : Frame σ (outerPins S start w base 0))
        (pre : ∀ t, t<T → Frame (Fin (fan S) × outerPins S start w base t) (Fin (fan S) × stagePins S start w base t 0))
        (nodes : ∀ t, t<T → Steps S.fanIn S.rounds (stagePins S start w base t) (Count S start t (fun _ => w))),
        TapeCosts (r:=r) (n:=n) multiplier fresh extra R base f pre nodes →
        ((Q*(compile (fun t ht => R.tapeStep base t ht (pre t ht) (nodes t ht)) T le_rfl (repeatLeaf (fan S) f T)).size+
          Fintype.card (Slot (fan S) (Machine.Guess S start (fun _ _ => w)) T) : ℕ) : ℝ) < r*(n:ℝ)^(92/100:ℝ) := by
  obtain ⟨H,h,bounds⟩ := boundary_costs (Cube D) 60 (Fintype.card (Cube D)) (interiors S) A a B b (fan S)
  let c := H+J+(multiplier*H+fresh)+(multiplier*J+fresh)
  let exp := max extra (max h j)
  obtain ⟨ω,hω,fold⟩ := eventually_schedule_history S scales c exp Q
  refine ⟨ω,hω,?_⟩
  filter_upwards [fold,eventually_boundaries S scales,eventually_ge_atTop 1] with n sum available hn
  intro r hr room T start w P fp bits deep budget cap R original base σ _ f pre nodes measured
  let L := logWidth r n
  let V := CoverScale.sites (Cube D) start
  have hL : 1≤L := by
    change 1≤logWidth r n
    rw [public_logWidth]
    exact (Nat.clog_mono_right 2 (by nlinarith only [Nat.mul_le_mul hn hr] : 2≤2*n*r)).trans' (by decide)
  have hx : extra≤exp := le_max_left ..
  have hh : h≤exp := (le_max_left h j).trans (le_max_right ..)
  have hj : j≤exp := (le_max_right h j).trans (le_max_right ..)
  apply sum r hr room σ (outerPins S start w base) (stagePins S start w base) (fun t => Count S start t (fun _ => w))
    f nodes pre (fun t ht => R.tapePost base t ht)
  constructor
  · exact measured.leaf.trans (work_mono _ (by dsimp [c]; omega) hx hL)
  · intro t ht
    let shape := boundaryShape S start t
    have high : S.high (offset S start t) ≤ start+1 := by rw [(levels S deep ht).2.2]; dsimp [EnrichedOuter.depth]; omega
    have preRaw := (bounds (r:=r) (n:=n) (z:=start+1) shape hr hn ((available r hr).1 t ht.le) high le_rfl).1
    have preSize := (original.subdivision t ht).trans preRaw
    have total := (measured.subdivision t ht).trans (Nat.add_le_add_right (Nat.mul_le_mul_left multiplier preSize) _)
    exact total.trans ((add_work shape hh hx hL).trans (work_mono shape (by dsimp [c]; omega) le_rfl hL))
  · intro t ht
    let shape := boundaryShape S start (t+1)
    have low : offset S start t ≤ start+1 := by dsimp [offset,EnrichedOuter.depth]; omega
    have postRaw := (bounds (r:=r) (n:=n) (z:=start+1) shape hr hn ((available r hr).1 (t+1) ht) low le_rfl).2
    rw [R.tapePost_size]
    exact (original.terminal t ht).trans (postRaw.trans (work_mono shape (by dsimp [c]; omega) hh hL))
  · intro t ht i hi
    let shape := (before S start t i).parallel S.fanIn
    have old : ((R.machine t ht).step i hi).size ≤ rowWork J V L j shape :=
      (Nat.le_add_right _ _).trans (original.round t ht i hi)
    have sum' := (measured.round t ht i hi).trans (Nat.add_le_add_right (Nat.mul_le_mul_left multiplier old) _)
    exact ⟨sum'.trans ((add_work shape hj hx hL).trans (work_mono shape (by dsimp [c]; omega) le_rfl hL)),
      (original.counts t ht i hi).trans (work_mono shape (by dsimp [c]; omega) hj hL)⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.Compiled

end BorderVNP
end Computability
end OAI
