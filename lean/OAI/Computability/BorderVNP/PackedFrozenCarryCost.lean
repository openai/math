import OAI.Computability.BorderVNP.PackedFrozenHistoryCapacity
import OAI.Computability.BorderVNP.CellPacketGeometryRate
import OAI.Computability.BorderVNP.PackedSelectedTreeWork

/-! # Cost of moving complete immutable tapes through the true history

The batched translation looks up one public owner per reserved prior row.
The slots include every old endpoint, subdivision relay, seed program and
terminal hook in the copy tree. Source widths and payload values never affect
the number of owner translations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape

open Crossing Cover Epoch Shortening Shortening.PublicCapacity Diagonal Filter TeamScales
open PackedHistoryCircuit PackedHistoryCircuit.Normalized.SelectedSchedule VPVNP.VerifierNetwork
open CellPacketGeometry.LiveWords
open private epoch_le_logWidth from OAI.Computability.BorderVNP.PackedResources
open scoped Classical BorderVNP.Epoch.Cube

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] {e : PaidIdentity K D m} (S : Normalized.SiteSchedule e)

/-- Fresh frozen endpoint/relay rows allocated at an epoch's input. -/
noncomputable def subdividedSlots (start t : ℕ) :=
  let s := epochRows e S.fanIn S.rounds (interiors S) (seedCount S start) (bottom (D := D) start) t
  Fintype.card (Subdivision.Gates.Row s.edges (portSlots S start t 0) (interiors S))

/-- The fixed combining block includes all retained interval candidates,
paid seed templates and terminal hooks before the geometry guard is applied. -/
noncomputable def freshSlots (start t j : ℕ) :=
  let old := (before S start t j).parallel S.fanIn
  Fintype.card (RoundRows e (0,false) (Fin (seedCount S start t j)) old.edges (portSlots S start t (j+1)))

/-- Actual number of reserved earlier record rows in one child of a public combining node. -/
noncomputable def priorSlots (start base t j : ℕ) :=
  let subdiv := subdividedSlots S start
  let fresh := freshSlots S start
  let outer := epochSlots S.fanIn S.rounds subdiv fresh base t
  combineSlots S.fanIn (fresh t) (outer+subdiv t) j

/-- The real cumulative public slots, including all padded candidates, occupy
at most a linear number of physical rows per preceding stage. -/
theorem priorSlots_le (start base C : ℕ) (hb : base ≤ C*physicalRows (bottom (D := D) start))
    (hsub : 2≤C) (hf : roundSlots e (0,false) ≤ C) (t j : ℕ) :
    priorSlots S start base t j ≤ ((t*(S.rounds+1)+j+2)*C)*physicalRows (before S start t j) := by
  have sub (t : ℕ) := (actual_subdivisionSlots S start t).trans (Nat.mul_le_mul_right _ hsub)
  have fresh (t j : ℕ) :=
    ((actual_roundSlots S start t j 0 (Fin (seedCount S start t j)) (Fintype.card_fin _)).1).trans
      (Nat.mul_le_mul_right _ hf)
  exact (historySlots_le S start base C (subdividedSlots S start) (freshSlots S start) hb sub fresh).2 t j

/-- The Batcher owner-key pass costs a cubic logarithmic factor per physical
input or lookup request, for arbitrary payload bits kept in the same frame. -/
theorem lookupCost_cubic (slots queries d d' W : ℕ) (hb : Nat.clog 2 (slots+queries) ≤ W)
    (hd : d ≤ W) (hd' : d' ≤ W) :
    lookupCost slots queries d d' ≤ 1000*(slots+queries+1)*(W+1)^3 := by
  change histogramBudget slots queries d d' ≤ _
  apply (histogram_cubic hb hd hd').trans
  exact (Nat.mul_le_mul_right _ (pow_clog_le (slots+queries))).trans_eq (by ring)

private theorem logRows (slots L C : ℕ) (hL : 1≤L) (fit : slots ≤ C*L*2^(60*L)) :
    Nat.clog 2 slots ≤ (Nat.clog 2 C+61)*L := by
  apply Nat.clog_le_of_le_pow
  have hC : C ≤ 2^(Nat.clog 2 C*L) := (Nat.le_pow_clog (by decide) C).trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ hL))
  have hL' : L ≤ 2^L := (Nat.lt_two_pow_self (n := L)).le
  exact fit.trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul hC hL')).trans_eq (by
    rw [←pow_add,←pow_add]; congr 1; ring))

/-- The public numerical lookup cost at every attained height, including all prior row slots. -/
theorem eventually_carry_cost {a x : ℕ} (s : EpochScales S a x) (C₀ : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let V := CoverScale.sites (Cube D) start
      let w := 60*logWidth r n
      ∀ base : ℕ, base ≤ C₀*physicalRows (bottom (D := D) start) →
      ∀ t < epochs s.τ n, ∀ j : Fin S.rounds,
        let shape := before S start t j
        ∀ requests ≤ priorSlots S start base t j,
          1+S.fanIn*lookupCost shape.sites requests w w ≤ rowWork C V (logWidth r n) 4 (shape.parallel S.fanIn) := by
  let C := max C₀ (max 2 (roundSlots e (0,false)))
  let Z := (2*S.rounds+3)*C
  let F := 2*(Z+1)
  let Y := Nat.clog 2 F+62
  let A := 1+1000*(Z+2)*(Y+1)^3*S.fanIn
  refine ⟨A,?_⟩
  have τ : 0 ≤ (s.τ:ℝ) := by exact_mod_cast s.tau_pos.le
  have τ1 : (s.τ:ℝ) ≤ 1 := by linarith [s.tau_small,s.alpha_small]
  filter_upwards [eventually_ranges S s (fun _ => 0) (fun _ => 0),eventually_ge_atTop 1] with n rang hn
  intro r hr start V w base hb t ht j shape requestCount count
  let L := logWidth r n
  let N := physicalRows shape
  let joined := shape.parallel S.fanIn
  have hL : 1 ≤ L := by
    rw [show L=Nat.clog 2 (2*n*r) from public_logWidth n r]
    exact (by decide : 1 ≤ Nat.clog 2 2).trans (Nat.clog_mono_right 2 (by nlinarith [Nat.mul_le_mul hn hr]))
  have et : epochs s.τ n ≤ L := by exact_mod_cast epoch_le_logWidth τ τ1 hn hr
  have stage : t*(S.rounds+1)+j.val+2 ≤ (2*S.rounds+3)*L := by
    have hi := Nat.mul_le_mul_right (S.rounds+1) (ht.le.trans et)
    have hj := j.isLt.le.trans (Nat.le_mul_of_pos_right S.rounds hL)
    nlinarith only [hi,hj,hL]
  have hc := priorSlots_le S start base C (hb.trans (Nat.mul_le_mul_right _ (le_max_left ..)))
    ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..)) t j
  have query : requestCount ≤ Z*L*N := count.trans (hc.trans (by
    exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ stage)).trans_eq (by dsimp only [Z]; ring)))
  have small : shape.sites ≤ N := Nat.le_add_right _ _
  have small' : N ≤ 2*2^(60*L) := by
    have q := (rang r hr).2 t ht j
    have hs := (Nat.le_mul_of_pos_left shape.sites S.positiveFanIn).trans q.words.2.2.2.1
    have he := (Nat.le_mul_of_pos_left shape.edges S.positiveFanIn).trans q.words.2.2.2.2.1
    change shape.sites ≤ 2^(60*L) at hs
    change shape.edges ≤ 2^(60*L) at he
    change shape.sites+shape.edges ≤ _
    omega
  have requests : shape.sites+requestCount ≤ (Z+1)*L*N := by
    have nL := Nat.le_mul_of_pos_left N hL
    nlinarith only [small,query,nL]
  have index : Nat.clog 2 (shape.sites+requestCount) ≤ Y*L := by
    apply (logRows _ L F hL (requests.trans ((Nat.mul_le_mul_left _ small').trans_eq (by dsimp only [F]; ring)))).trans
    exact Nat.mul_le_mul_right L (by dsimp only [Y]; omega)
  have code : w ≤ Y*L := by
    change 60*L ≤ _
    exact Nat.mul_le_mul_right L (by dsimp only [Y]; omega)
  have lookup := lookupCost_cubic shape.sites (requestCount) w w (Y*L) index code code
  have joint : N ≤ joined.volume V := by
    have hr : N ≤ physicalRows joined := (Nat.le_mul_of_pos_left N S.positiveFanIn).trans_eq (parallel_physicalRows shape S.fanIn).symm
    exact hr.trans (by unfold physicalRows Shape.volume; omega)
  have one : 1 ≤ joined.volume V := by unfold Shape.volume; omega
  have req : shape.sites+requestCount+1 ≤ (Z+2)*L*joined.volume V := by
    have r₁ := requests.trans (Nat.mul_le_mul_left _ joint)
    have c := Nat.mul_pos hL one
    nlinarith only [r₁,c]
  have cap : Y*L+1 ≤ (Y+1)*L := by nlinarith only [hL]
  have unit : 1 ≤ joined.volume V*L^4 := Nat.mul_pos one (Nat.one_le_pow _ _ hL)
  apply (Nat.add_le_add_left (Nat.mul_le_mul_left S.fanIn lookup) 1).trans
  change _ ≤ A*joined.volume V*L^4
  calc
    _ ≤ joined.volume V*L^4 + S.fanIn*(1000*((Z+2)*L*joined.volume V)*((Y+1)*L)^3) :=
      Nat.add_le_add unit (Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ req) (Nat.pow_le_pow_left cap _)))
    _ = _ := by dsimp only [A]; ring

/-- An actual owner-translation circuit for the complete prior tape. -/
theorem eventually_carry_work {a x : ℕ} (s : EpochScales S a x) (C₀ : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ r : ℕ, 1≤r →
      let start := CoverScale.initialDepth (Cube D) r n
      let V := CoverScale.sites (Cube D) start
      let w := 60*logWidth r n
      ∀ base : ℕ, base ≤ C₀*physicalRows (bottom (D := D) start) →
      ∀ t < epochs s.τ n, ∀ j : Fin S.rounds,
        let shape := before S start t j
        ∀ (R B : Type*) [Fintype R] [Fintype B],
          Fintype.card R ≤ priorSlots S start base t j →
          ∀ (old : Fin shape.sites ↪ Fin (2^w)) (next : Fin (S.fanIn*shape.sites) ↪ Fin (2^w)),
            ∃ f : Frame (Fin S.fanIn × Pins R B w) (Fin S.fanIn × Pins R B w),
              Carries old next f ∧ f.size ≤ rowWork C V (logWidth r n) 4 (shape.parallel S.fanIn) := by
  obtain ⟨C,cost⟩ := eventually_carry_cost S s C₀
  refine ⟨C,?_⟩
  filter_upwards [cost] with n hcost
  intro r hr start V w base hb t ht j shape R B instR instB count old next
  obtain ⟨f,hf,correct⟩ := exists_carry (Row := R) (Payload := B) old next
  exact ⟨f,correct,hf.trans (hcost r hr base hb t ht j (Fintype.card R) count)⟩

end Packing.Inherited.FrozenTape

end BorderVNP
end Computability
end OAI
