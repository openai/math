import OAI.Computability.NearSquareRoot.FixedLayerWalshTemplateAt
import OAI.Computability.NearSquareRoot.PhysicalWalshPlanTotal

/-! # Input envelopes and sharp traces for actual Walsh tickets -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 1800000
noncomputable section
namespace FixedLayer

open IntegerMultiplication Code Space FixedPoint FixedCandidate DigitPacking
open FixedLayerTickets ShortFourier.BatchWord
open PhysicalWalsh PhysicalWalsh.GatherProgram PhysicalWalshNode
open KernelPass KernelPass.ComputableSyntax PhysicalWalshCompile.Dispatch
open EffectiveBoundedTask CommonRegisters GeneratorSyntax

variable {P : Type} {I : P → Type}
  (r : P → Raw) {num den : P → ℕ} (sel : ∀ j, Selected (num j) (den j) (r j))
  (router piece : P → Cmd) (n : ∀ j,I j → ℕ) (hv : ∀ j i,Directory (n j i))
  (dir : ∀ j,I j → Bool)

private theorem rawWordsSize {n : ℕ} (hn : 2 ≤ n) (x : FixedCandidate.Array n) :
    size (Odd.words x) ≤ 75000*(n+1) := by
  have h := framed_size hn x
  change size (tally n, FixedCandidate.records x) ≤ _ at h
  simp only [size_prod] at h
  have eq : Odd.words x = FixedCandidate.records x := List.map_ofFn (f:=x) (g:=Dusk.mark)
  rw [eq]
  omega

theorem walshRawArgument_size (j : P) (e : WalshRowInput n hv dir j)
    (hn : 2 ≤ n j e.val.instanceIndex) :
    (walshRawArgument n hv dir j e).count ≤ 75000*(n j e.val.instanceIndex+1)+2*addressBits (n j e.val.instanceIndex)+2 := by
  let bits := walshBits (hv j e.val.instanceIndex) (dir j e.val.instanceIndex) e.val.position.val e.val.position.isLt
  change size (flags bits, Odd.words e.val.payload) ≤ _
  rw [size_prod, Bits.size_word, flags_length]
  dsimp only [Prod.snd]
  have h := rawWordsSize hn e.val.payload
  omega

theorem walshRawReply_size (j : P) (e : WalshRowInput n hv dir j)
    (hn : 2 ≤ n j e.val.instanceIndex) :
    (walshRawReply r sel n hv dir j e).count ≤ 75000*(n j e.val.instanceIndex+1) :=
  rawWordsSize hn _

theorem walshInput_norm (j : P) (e : WalshRowInput n hv dir j) :
    ‖recordArray e.val.payload‖ ≤ (2:ℝ)^(13*addressBits (n j e.val.instanceIndex)) := by
  let _ := BoxFin.modulus_neZero (hv j e.val.instanceIndex)
  exact ((ProductRecovery.pull (index (hv j e.val.instanceIndex))).norm_map
    (recordArray e.val.payload)).symm.le.trans e.val.inRange

theorem two_of_walshCut {K k : ℕ} {r : Raw} (h : walshTemplateCut K r ≤ k) : 2 ≤ k := by
  have precision : precisionCutoff (rawFactor r) ≤ k :=
    (le_max_right ..).trans ((le_max_right ..).trans h)
  apply le_trans _ precision
  change 2^1 ≤ 2^(4*(rawFactor r+1))
  exact Nat.pow_le_pow_right (by decide) (by omega)

/-- A restriction of the actual ticket domain can use the sharp estimate
without changing any opcode of the selected program. -/
theorem walshSource_sparse {J : Type} (j : P) (row : J → WalshRowInput n hv dir j)
    {ρ B c H Q : ℝ} {L S : ℕ → ℝ} {q K : ℕ}
    (hr : 0 < ρ) (hB : 0 ≤ B) (hc : 0 ≤ c) (hS : ∀ w,0 ≤ S w)
    (hH : 0 ≤ H) (hQ : 0 ≤ Q)
    (raw : let a := (dimensions (r j)).1
      let hw : 0 < (dimensions (r j)).2 := (sel j).wide.trans' (by decide)
      Runs (piece j)
        (fun v : PhysicalWalshNode.Admitted hw (sel j).plan => pieceTimeBound (a+1) (sel j).plan.calls ρ B L S v.val.shape)
        (fun v => pieceSpaceBound (a+1) c S v.val.shape)
        (rawInput hw (sel j).plan) (rawOutput hw (sel j).plan))
    (route : PositionRunsAt (router j) ρ K)
    (large : ∀ i,walshTemplateCut K (r j) ≤ addressBits (n j (row i).val.instanceIndex))
    (overhead : ∀ i,let k := addressBits (n j (row i).val.instanceIndex)
      0 ≤ L (componentBits k) ∧ L (componentBits k) ≤ H*(1+Real.log (2+k)))
    (setup : ∀ i,let k := addressBits (n j (row i).val.instanceIndex)
      S (componentBits k) ≤ Q*(k+1:ℝ)^q) :
    Runs (walshSource r router piece j)
      (fun i => Pieces.sparseTime ρ (addressBits (n j (row i).val.instanceIndex)))
      (fun i => Pieces.sparseSpace (addressBits (n j (row i).val.instanceIndex)))
      (fun i => walshRawArgument n hv dir j (row i)) (fun i => walshRawReply r sel n hv dir j (row i)) := by
  let k i := addressBits (n j (row i).val.instanceIndex)
  let bits i := walshBits (hv j (row i).val.instanceIndex) (dir j (row i).val.instanceIndex)
    (row i).val.position.val (row i).val.position.isLt
  have hw := (show 0 < 2 by decide).trans_le (sel j).wide
  have ha := (show 1 < 5 by decide).trans_le (sel j).large
  exact (planPassAt hw (sel j).plan ha (router j) (piece j) (sel j).correct (selectedFactor (sel j))
    hr hB hc hS raw route (g:=1) (G:=0) (q:=q) (by norm_num) (by norm_num) hH hQ k bits
    (fun i => flags (bits i)) (fun i => (row i).val.payload) large (fun _ => rfl)
    (fun i => BoxFin.selected_sparse (hv j (row i).val.instanceIndex) (two_of_walshCut (large i)) _)
    (fun i => walshInput_norm n hv dir j (row i)) overhead setup).1

/-- At the common numerical cutoff, arbitrary finite subroutine costs
suffice for a finite correct run of the literal selected pass. -/
theorem walshSource_total (j : P) {K : ℕ}
    (raw : let hw : 0 < (dimensions (r j)).2 := (show 0 < 2 by decide).trans_le (sel j).wide
      ∃ t s, Runs (piece j) t s (rawInput hw (sel j).plan) (rawOutput hw (sel j).plan))
    (route : PositionTotalAt (router j) K)
    (large : ∀ i,walshTemplateCut K (r j) ≤ addressBits (n j i)) :
    ∃ t s, Runs (walshSource r router piece j) t s (walshRawArgument n hv dir j)
      (walshRawReply r sel n hv dir j) := by
  let k (e : WalshRowInput n hv dir j) := addressBits (n j e.val.instanceIndex)
  let bits (e : WalshRowInput n hv dir j) := walshBits (hv j e.val.instanceIndex)
    (dir j e.val.instanceIndex) e.val.position.val e.val.position.isLt
  have hw := (show 0 < 2 by decide).trans_le (sel j).wide
  have ha := (show 1 < 5 by decide).trans_le (sel j).large
  exact (planPassTotal hw (sel j).plan ha (router j) (piece j) (sel j).correct (selectedFactor (sel j))
    raw route (g:=1) (G:=0) (by norm_num) (by norm_num) k bits (fun e => flags (bits e))
    (fun e => e.val.payload) (fun e => large e.val.instanceIndex) (fun _ => rfl)
    (fun e => BoxFin.selected_sparse (hv j e.val.instanceIndex) (two_of_walshCut (large e.val.instanceIndex)) _)
    (walshInput_norm n hv dir j)).1

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
