import OAI.Computability.NearSquareRoot.FixedLayerEffectiveWalsh
import OAI.Computability.NearSquareRoot.PhysicalWalshPlanCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSelected

/-! # Lowering a compiled selected template to the effective Walsh branch

The selector supplies one literal plan for each outer index. Its two parsed
dimensions drive the grouped controller, its raw word gives a computable
precision cutoff, and its proved matrix specifies the output of the same
emitted recursive command. Both source subroutines have a common register
bound, independent of the outer index.
-/

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

/-- Width threshold tested by a searched kernel with its associated physical
bit router. The mask sparsity constant for real scheduled rows is one. -/
def walshTemplateCut (router : ℕ) (r : Raw) :=
  selectedCutoff router 0 (dimensions r).2 (rawFactor r)

theorem walshTemplateCut_computable {P : Type} [Primcodable P] {r : P → Raw} {t : P → ℕ}
    (hs : Computable r) (ht : Computable t) : Computable (fun p => walshTemplateCut (t p) (r p)) :=
  selectedCutoff_computable ht (Computable.const 0)
    ((Primrec.snd.comp primrec_dimensions).to_comp.comp hs) (rawFactor_primrec.to_comp.comp hs)

/-- Turn the two elementary physical command families into the complete
Walsh branch of the emitted Fourier schedule. The outer index controls the
compiler only through the very syntax decoded by `sel`. -/
theorem effectiveWalsh_from_compiled {P : Type} [Primcodable P] {I : P → Type}
    (r : P → Raw) (hs : Computable r) {num den : P → ℕ}
    (sel : ∀ j, Selected (num j) (den j) (r j))
    {ρ : P → ℝ} (hr : ∀ j,0 < ρ j) (router piece : P → Cmd)
    (er : Effective ltr router) (ep : Effective ltr piece) (R : ℕ)
    (wr : ∀ j, Within R (router j)) (wp : ∀ j, Within R (piece j))
    (K : P → ℕ) (route : ∀ j, PositionRunsAt (router j) (ρ j) (K j))
    {B c H Q : P → ℝ} {L S : P → ℕ → ℝ} {q : P → ℕ}
    (hB : ∀ j,0 ≤ B j) (hc : ∀ j,0 ≤ c j) (hS : ∀ j w,0 ≤ S j w)
    (hH : ∀ j,0 ≤ H j) (hQ : ∀ j,0 ≤ Q j)
    (pieceExec : ∀ j,
      let a := (dimensions (r j)).1
      let hw : 0 < (dimensions (r j)).2 := (sel j).wide.trans' (by decide)
      EffectiveBoundedTask.Runs (piece j)
        (fun v : PhysicalWalshNode.Admitted hw (sel j).plan => pieceTimeBound (a+1) (sel j).plan.calls (ρ j) (B j) (L j) (S j) v.val.shape)
        (fun v => pieceSpaceBound (a+1) (c j) (S j) v.val.shape)
        (rawInput hw (sel j).plan) (rawOutput hw (sel j).plan))
    (n : ∀ j, I j → ℕ) (hv : ∀ j i, Directory (n j i)) (dir : ∀ j, I j → Bool)
    (hd : ∀ j i,4 ≤ (box (n j i)).length) (hn : ∀ j i,2 ≤ n j i)
    (clock : P → ℕ → ℕ) (linear : ∀ j i,n j i ≤ clock j (n j i))
    (room : ∀ j i,Pieces.sparseTime (ρ j) (addressBits (n j i)) ≤ clock j (n j i))
    (large : ∀ j i,walshTemplateCut (K j) (r j) ≤ addressBits (n j i))
    (overhead : ∀ j i, let k := addressBits (n j i)
      0 ≤ L j (componentBits k) ∧ L j (componentBits k) ≤ H j*(1+Real.log (2+k)))
    (setup : ∀ j i, let k := addressBits (n j i)
      S j (componentBits k) ≤ Q j*(k+1:ℝ)^(q j)) :
    EffectiveImplements n hv dir hd clock .walsh := by
  let a j := (dimensions (r j)).1
  let W j := (dimensions (r j)).2
  have ha j : 1 < a j+1 := (show 1 < 5 by decide).trans_le (sel j).large
  have hw j : 0 < W j := (show 0 < 2 by decide).trans_le (sel j).wide
  have factor j : recursionFactor (sel j).plan ≤ rawFactor (r j) := by
    have f := recursionFactor_le_rawFactor (r j).2 (sel j).plan (sel j).decode
    simpa only [rawFactor] using f
  have kcut j i : precisionCutoff (rawFactor (r j)) ≤ addressBits (n j i) :=
    (le_max_right ..).trans ((le_max_right ..).trans (large j i))
  apply effectiveWalsh_of_selectedFamily n hv dir hd hn clock linear ρ room hw
    (fun j => (sel j).plan) ha (fun j => (sel j).correct) factor kcut
  let bits j (e : WalshRowInput n hv dir j) := walshBits (hv j e.val.instanceIndex)
    (dir j e.val.instanceIndex) e.val.position.val e.val.position.isLt
  let k j (e : WalshRowInput n hv dir j) := addressBits (n j e.val.instanceIndex)
  apply planCmd_family (A:=fun j => a j+1) (W:=W)
    (Primrec.nat_add.to_comp.comp ((Primrec.fst.comp primrec_dimensions).to_comp.comp hs) (Computable.const 1))
    ((Primrec.snd.comp primrec_dimensions).to_comp.comp hs) er ep R wr wp
  intro j
  have hx (e : WalshRowInput n hv dir j) : ‖recordArray e.val.payload‖ ≤ (2:ℝ)^(13*k j e) := by
    let _ := BoxFin.modulus_neZero (hv j e.val.instanceIndex)
    exact ((ProductRecovery.pull (index (hv j e.val.instanceIndex))).norm_map (recordArray e.val.payload)).symm.le.trans e.val.inRange
  have two (e : WalshRowInput n hv dir j) : 2 ≤ k j e := by
    have p := kcut j e.val.instanceIndex
    have lo : 2 ≤ precisionCutoff (rawFactor (r j)) := by
      change 2^1 ≤ 2^(4*(rawFactor (r j)+1))
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact lo.trans p
  exact (planPassAt (hw j) (sel j).plan (ha j) (router j) (piece j) (sel j).correct (factor j)
    (hr j) (hB j) (hc j) (hS j) (pieceExec j) (route j) (g:=1) (G:=0) (q:=q j)
    (by norm_num) (by norm_num) (hH j) (hQ j) (k j) (bits j) (fun e => flags (bits j e))
    (fun e => e.val.payload) (fun e => large j e.val.instanceIndex) (fun _ => rfl)
    (fun e => BoxFin.selected_sparse (hv j e.val.instanceIndex) (two e) _) hx
    (fun e => overhead j e.val.instanceIndex) (fun e => setup j e.val.instanceIndex)).1

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
