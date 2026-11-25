import OAI.Computability.NearSquareRoot.PhysicalBoxPhase
import OAI.Computability.NearSquareRoot.PrecisionWalshTicketAdapter
import OAI.Computability.NearSquareRoot.PrecisionActualWalshRow
import OAI.Computability.NearSquareRoot.PrecisionWalshMaskBudget
import OAI.Computability.NearSquareRoot.PhysicalWalshSelectedPass
import OAI.Computability.NearSquareRoot.SynchronizedSelectedMask

/-! # The synchronized Walsh branch with its real ticket and operand frame

The ordinal of the directed row determines the mask read by the stable-gather
program. Both permutations, the grouped Walsh recursion and the terminal
normalized butterfly contribute to the raw pass's time and visited tape bound.
The chronological interpreter receives a new record stream with its original
operand length, measured against the exact matrix on the Fourier axes.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 2400000
noncomputable section
namespace FixedLayer
open IntegerMultiplication Code Space Strip FixedPoint FixedCandidate DigitPacking
open ShortFourier.BatchWord SynchronizedLayers.ScheduleProgram SynchronizedPadding Matrix
open PhysicalWalsh PhysicalWalsh.GatherProgram KernelPass PhysicalWalshNode Filter

def walshBits {k : ℕ} (h : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k))
    (dir : Bool) (j : ℕ) (inside : j < (directedPlan (dir,tally k)).length) : Finset (Fin k) :=
  (rowActive (k:=k) (directedPlan (dir,tally k))[j]).image (BoxFin.selectedPosition h)

private theorem ticketMask {I : Type} (k j : I → ℕ) (dir : I → Bool)
    (inside : ∀ i, j i < (directedPlan (dir i,tally (k i))).length)
    (h : ∀ i, BoxShape.Valid (k i) (BoxScale.width (k i)) (CoprimeBox.box (k i))) :
    (phaseTicketRegime k j dir inside).Has (fun i => flags (walshBits (h i) (dir i) (j i) (inside i))) := by
  let s := phaseTicketRegime k j dir inside
  have head : s.Has (fun i => phaseStageTicket (k i) (dir i) (j i) (inside i)) := Regime.self
  have r := head.ez Easy.snd
  have K : s.Has (fun i => tally (k i)) := r.ez Easy.fst
  have D : s.Has dir := (r.ez Easy.snd).ez Easy.fst
  have J : s.Has (fun i => tally (j i)) := (r.ez Easy.snd).ez Easy.snd
  have H := ((D.pair K).pair J).thenDo emittedMask_poly
  have eq i := emittedMask_eq (h i) (dir i) ⟨j i,inside i⟩
  exact (show _ = (fun i => flags (walshBits (h i) (dir i) (j i) (inside i))) from funext eq) ▸ H

/-- Output function of a Walsh ticket at a valid directory. -/
def walshRowOutput {a W n : ℕ} (hw : 0<W) (p : Plan (a+1) W W) (h : Directory n)
    (dir : Bool) (j : ℕ) (ok : j < (directedPlan (dir,tally (addressBits n))).length) (x : FixedCandidate.Array n) :=
  selectedResult hw p (walshBits h dir j ok) x

/-- Promote a selected-array execution to one chronological ticket step. Both
the header and the stored Fourier-axis matrix are the ones emitted by this
row's index, even in the adjoint direction. -/
theorem walshRowBranch_of_mask {I : Type} {ρ : ℝ} (hr : 0 ≤ ρ)
    (n stage : I → ℕ) (dir : I → Bool) (hn : ∀ i, 2 ≤ n i)
    (hk : ∀ i, 1 ≤ addressBits (n i)) (hb : ∀ i, Directory (n i)) (hd : ∀ i, 4 ≤ (box (n i)).length)
    (inside : ∀ i, stage i < (directedPlan (dir i,tally (addressBits (n i)))).length)
    (tag : ∀ i, ((directedPlan (dir i,tally (addressBits (n i))))[stage i]'(inside i)).2.1 = kindCode .walsh)
    (x out : (i : I) → FixedCandidate.Array (n i))
    (pass : BoundedTask (fun i => Pieces.sparseTime ρ (addressBits (n i))) (fun i => Pieces.sparseSpace (addressBits (n i)))
      (fun i => send (flags (walshBits (hb i) (dir i) (stage i) (inside i)),Odd.words (x i)))
      (fun i => send (Odd.words (out i))))
    (acc : ∀ i, ‖recordArray (ι:=Fin (2^addressBits (n i))) (out i) - WithLp.toLp 2
      (BoxFin.flatWalsh (walshBits (hb i) (dir i) (stage i) (inside i)) *ᵥ (fun j => FixedPoint.value _ (x i j)))‖ ≤
        1/(2:ℝ)^(50*addressBits (n i))) :
    BoundedTask (fun i => Pieces.sparseTime ρ (addressBits (n i))) n
        (fun i => .fork (send (phaseStageTicket (addressBits (n i)) (dir i) (stage i) (inside i))) (framed (x i)))
        (fun i => framed (out i)) ∧
      ∀ i, let _ := BoxFin.modulus_neZero (hb i)
        let M := boxRow (physicalLayout (hb i)) (hd i) ((directedPlan (dir i,tally (addressBits (n i))))[stage i]'(inside i))
        ‖recordArray (out i ∘ index (hb i)) -
          WithLp.toLp 2 (M *ᵥ (fun z => recordArray (x i ∘ index (hb i)) z))‖ ≤ 1/(2:ℝ)^(50*addressBits (n i)) := by
  let k i := addressBits (n i)
  let s := phaseTicketRegime k stage dir inside
  let head i := send (phaseStageTicket (k i) (dir i) (stage i) (inside i))
  obtain ⟨setup,d,run⟩ := walshPassPrepared (s:=s) hr (ticketMask k stage dir inside hb) x out pass
  have vol i : 2^k i ≤ Pieces.sparseSpace (k i) := Nat.le_mul_of_pos_right _ (hk i)
  have bounded := absorbArraySetup (k:=k) d (fun i => (vol i).trans (Pieces.space_le_clock hr _)) vol run
  constructor
  · have lin i : n i ≤ Pieces.sparseTime ρ (k i) := (packed_volume (hn i)).1.trans (Pieces.space_le_clock hr _)
    have hh i : (head i).count ≤ 1920000000000*(n i+1) := by
      have low : k i+1 ≤ 192*n i := (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _)).trans (array_volume (hn i))
      have ht := phaseStageTicket_size (k i) (dir i) (stage i) (inside i)
      change size (phaseStageTicket (k i) (dir i) (stage i) (inside i)) ≤ _
      omega
    apply framedStage n _ hn lin head 1920000000000 hh x out
    apply bounded.bound 1 49
    · intro i; simp
    · intro i
      have h := (packed_volume (hn i)).2
      change 2^k i*k i+1 ≤ 49*(n i+1)
      change 2^k i*k i ≤ 48*n i at h
      omega
  · intro i
    let _ := BoxFin.modulus_neZero (hb i)
    apply transferRow (index (hb i)) _ (x i) (out i) _ _ (acc i)
    exact congrArg (fun M => M *ᵥ (fun j => recordArray (x i) j))
      (flat_walshRow (hb i) (hd i) ⟨stage i,inside i⟩ (tag i))

/-- Use a physical recursion and a position-table router at their supplied
rate. Its threshold and its tape program are uniform over operand lengths,
row ordinals, directions, masks and admissible input records. -/
theorem walshRowBranch_of_release {a W K₀ : ℕ} (hw : 0 < W) (p : Plan (a+1) W W) (ha : 1 < a+1)
    (correct : Correct p) {ρ c H Q : ℝ} {q : ℕ} {L P : ℕ → ℝ} (hr : 0 < ρ) (hc : 0 ≤ c) (hP : ∀ w,0 ≤ P w)
    (release : PieceRelease hw p ρ c L P) (route : PositionRuns ρ K₀) (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (overhead : ∀ᶠ k : ℕ in atTop,
      (0 ≤ L (componentBits k) ∧ L (componentBits k) ≤ H*(1+Real.log (2+k))) ∧
        P (componentBits k) ≤ Q*(k+1:ℝ)^q) :
    ∃ K : ℕ, ∀ {I : Type} (n stage : I → ℕ) (dir : I → Bool) (_hn : ∀ i,2 ≤ n i)
      (_large : ∀ i,K ≤ addressBits (n i)) (hb : ∀ i, Directory (n i)) (hd : ∀ i,4 ≤ (box (n i)).length)
      (inside : ∀ i,stage i < (directedPlan (dir i,tally (addressBits (n i)))).length)
      (_tag : ∀ i, ((directedPlan (dir i,tally (addressBits (n i))))[stage i]'(inside i)).2.1 = kindCode .walsh)
      (x : (i : I) → FixedCandidate.Array (n i)),
      (∀ i, let _ := BoxFin.modulus_neZero (hb i)
        ‖recordArray (x i ∘ index (hb i))‖ ≤ (2:ℝ)^(13*addressBits (n i))) →
      let out i := walshRowOutput hw p (hb i) (dir i) (stage i) (inside i) (x i)
      BoundedTask (fun i => Pieces.sparseTime ρ (addressBits (n i))) n
        (fun i => .fork (send (phaseStageTicket (addressBits (n i)) (dir i) (stage i) (inside i))) (framed (x i)))
        (fun i => framed (out i)) ∧
      ∀ i, let _ := BoxFin.modulus_neZero (hb i)
        let M := boxRow (physicalLayout (hb i)) (hd i) ((directedPlan (dir i,tally (addressBits (n i))))[stage i]'(inside i))
        ‖recordArray (out i ∘ index (hb i)) -
          WithLp.toLp 2 (M *ᵥ (fun z => recordArray (x i ∘ index (hb i)) z))‖ ≤ 1/(2:ℝ)^(50*addressBits (n i)) := by
  obtain ⟨R,raw⟩ := selectedPass hw p ha correct hr hc hP release route (g:=1) (q:=q) (by norm_num) hH hQ
  obtain ⟨D,ok⟩ := eventually_atTop.mp overhead
  refine ⟨max (max 2 D) R,?_⟩
  intro I n stage dir hn large hb hd inside tag x hx out
  let k i := addressBits (n i)
  let b i := walshBits (hb i) (dir i) (stage i) (inside i)
  have hge i : 2 ≤ k i := by have := large i; dsimp [k]; omega
  have hx' i : ‖recordArray (x i)‖ ≤ (2:ℝ)^(13*k i) := by
    let _ := BoxFin.modulus_neZero (hb i)
    exact ((ProductRecovery.pull (index (hb i))).norm_map (recordArray (x i))).symm.le.trans (hx i)
  have sep i := ok (k i) (show D ≤ k i by have := large i; dsimp [k]; omega)
  obtain ⟨pass,_,acc⟩ := raw k b (fun i => flags (b i)) x (fun i => by have := large i; dsimp [k]; omega)
    (fun _ => rfl) (fun i => BoxFin.selected_sparse (hb i) (hge i) _) hx' (fun i => (sep i).1) (fun i => (sep i).2)
  exact walshRowBranch_of_mask hr.le n stage dir hn (fun i => (hge i).trans' (by decide))
    hb hd inside tag x out pass acc

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
