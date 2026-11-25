import OAI.Computability.NearSquareRoot.PrecisionPhaseTicket
import OAI.Computability.NearSquareRoot.SynchronizedBoxPhaseRow
import OAI.Computability.NearSquareRoot.FixedLayerFrame
import OAI.Computability.NearSquareRoot.FixedCandidateArrays
import OAI.Computability.NearSquareRoot.ProductReindex

/-! # A diagonal branch of the chronological Fourier-word interpreter

The physical command reads the emitted row ticket and preserves the operand
length while operating on the packed data. Its error is measured on the
padded Fourier axes against the exact matrix specified by the same ticket.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 1400000
noncomputable section
namespace FixedLayer

open IntegerMultiplication Code Space FixedPoint FixedCandidate DigitPacking
open ShortFourier.BatchWord SynchronizedLayers.ScheduleProgram SynchronizedPadding Matrix

/-- Reindex a numerical error bound onto the coordinates of the actual matrix row. -/
theorem transferRow {α β : Type} [Fintype α] [Fintype β] {k : ℕ}
    (e : α ≃ β) (M : Matrix α α ℂ) (x y : β → Record k) (v : EuclideanSpace ℂ β)
    (matchRow : M.submatrix e.symm e.symm *ᵥ (fun j => recordArray x j) = (fun j => v j))
    {δ : ℝ} (err : ‖recordArray y - v‖ ≤ δ) :
    ‖recordArray (y ∘ e) - WithLp.toLp 2 (M *ᵥ (fun z => recordArray (x ∘ e) z))‖ ≤ δ := by
  have eq : ProductRecovery.pull e v = WithLp.toLp 2 (M *ᵥ (fun z => recordArray (x ∘ e) z)) := by
    rw [submatrix_mulVec_equiv] at matchRow
    ext a
    simpa only [ProductRecovery.pull_apply,recordArray,WithLp.ofLp_toLp,Function.comp_apply,Function.comp_def,
      Equiv.symm_apply_apply,Equiv.symm_symm] using (congrFun matchRow (e a)).symm
  rw [← eq,← ProductRecovery.pull_recordArray,← map_sub,LinearIsometryEquiv.norm_map]
  exact err

/-- The width-cost factor in one array multiplier sweep. -/
def phaseClock (n : ℕ) := n * (Nat.clog 2 (addressBits n+1)+1)

/-- The finite row index and direction select the precise matrix of this
branch, including padded local lanes whose optional descriptor is absent. -/
theorem phaseRowBranch {I : Type} (n stage : I → ℕ) (dir : I → Bool)
    (hn : ∀ i, 2 ≤ n i) (hb : ∀ i, Directory (n i))
    (hd : ∀ i, 4 ≤ (box (n i)).length)
    (inside : ∀ i, stage i < (directedPlan (dir i,tally (addressBits (n i)))).length)
    (tag : ∀ i, ((directedPlan (dir i,tally (addressBits (n i))))[stage i]'(inside i)).2.1 = kindCode .diagonal)
    (x : (i : I) → FixedCandidate.Array (n i))
    (hx : ∀ i, let _ := BoxFin.modulus_neZero (hb i)
      ‖recordArray (x i ∘ index (hb i))‖ ≤ (2:ℝ)^(13*addressBits (n i))) :
    ∃ out : (i : I) → FixedCandidate.Array (n i),
      BoundedTask (fun i => phaseClock (n i)) n
        (fun i => .fork (send (phaseStageTicket (addressBits (n i)) (dir i) (stage i) (inside i))) (framed (x i)))
        (fun i => framed (out i)) ∧
      ∀ i, let _ := BoxFin.modulus_neZero (hb i)
        let M := boxRow (physicalLayout (hb i)) (hd i)
          ((directedPlan (dir i,tally (addressBits (n i))))[stage i]'(inside i))
        ‖recordArray (out i ∘ index (hb i)) -
          WithLp.toLp 2 (M *ᵥ (fun z => recordArray (x i ∘ index (hb i)) z))‖ ≤ 1/(2:ℝ)^(50*addressBits (n i)) := by
  let k := fun i => addressBits (n i)
  have hk i : 1 ≤ k i := by
    have h := width_le_twice_addressBits (hn i)
    have p := width_pos (hn i)
    dsimp [k]
    omega
  have hx' i : ‖recordArray (x i)‖ ≤ (2:ℝ)^(13*k i) := by
    let _ := BoxFin.modulus_neZero (hb i)
    exact ((ProductRecovery.pull (index (hb i))).norm_map (recordArray (x i))).symm.le.trans (hx i)
  obtain ⟨out,hu,run,num⟩ := phaseTicketPass k stage dir inside hb hd x hk hx'
  refine ⟨out,?_,?_⟩
  · let header i := send (phaseStageTicket (k i) (dir i) (stage i) (inside i))
    have lin i : n i ≤ phaseClock (n i) := Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ _)
    have hh i : (header i).count ≤ 1920000000000*(n i+1) := by
      have hk' : k i+1 ≤ 192*n i :=
        (Nat.le_mul_of_pos_left _ (Nat.zero_lt_succ _)).trans (array_volume (hn i))
      have ht := phaseStageTicket_size (k i) (dir i) (stage i) (inside i)
      change size (phaseStageTicket (k i) (dir i) (stage i) (inside i)) ≤ _
      omega
    apply framedStage n _ hn lin header 1920000000000 hh x out
    apply run.bound 193 193
    · intro i
      have cap := Nat.mul_le_mul_right (Nat.clog 2 (k i+1)+1) (array_volume (hn i))
      change (2^k i+1)*((k i+1)*(Nat.clog 2 (k i+1)+1))+1 ≤ 193*(phaseClock (n i)+1)
      change (2^k i+1)*(k i+1)*(Nat.clog 2 (k i+1)+1) ≤ 192*n i*(Nat.clog 2 (k i+1)+1) at cap
      rw [Nat.mul_assoc] at cap
      change _ ≤ 193*(n i*(Nat.clog 2 (k i+1)+1)+1)
      rw [Nat.mul_assoc 192] at cap
      omega
    · intro i
      have cap := array_volume (hn i)
      change (2^k i+1)*(k i+1)+1 ≤ 193*(n i+1)
      change (2^k i+1)*(k i+1) ≤ 192*n i at cap
      omega
  · intro i
    let _ := BoxFin.modulus_neZero (hb i)
    apply transferRow (index (hb i)) _ (x i) (out i) _ _ (num i)
    exact flat_phaseRow_apply (hb i) (hd i) ⟨stage i,inside i⟩ (tag i) (hu i) (recordArray (x i))

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
