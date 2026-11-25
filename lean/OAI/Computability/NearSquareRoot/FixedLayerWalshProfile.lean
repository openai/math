import OAI.Computability.NearSquareRoot.FixedLayerWalshSource
import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudgetTotal
import OAI.Computability.NearSquareRoot.BoundedProgramForget

/-! # Walsh row execution under a guessed machine cost

Each guess uses its compiled recursive piece and position router. Their
termination ensures finite physical costs on every operand. The fast bounds
for a correct guess recover the sparse clock and an operand-linear arena for
the very same program.
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

private theorem fits_of_named_run {I : Type} {c : Cmd} {t s : I → ℕ} {u v : I → Tree}
    (h : Runs c t s u v) (i : I) : ∃ T, ∀ env r, Fits env c (pile 0 (u i) r) (pile 0 (v i) r) T := by
  have H : ∃ C : ℕ, ∀ i env, Fits.value env c 0 (u i) (v i) (C*(t i+1)) :=
    command_contract c from h.task.forget
  obtain ⟨C,H⟩ := H
  exact ⟨_,H i⟩

/-- The two physical subroutine estimates used to measure a successful guess.
The cutoff counts operand bits, while the position router counts address bits. -/
structure WalshSharpRelease {num den : ℕ} {r : Raw} (sel : Selected num den r)
    (router piece : Cmd) (ρ : ℝ) (cut : ℕ) where
  B : ℝ
  c : ℝ
  H : ℝ
  Q : ℝ
  L : ℕ → ℝ
  S : ℕ → ℝ
  q : ℕ
  K : ℕ
  positive : 0 < ρ
  cost : 0 ≤ B
  cells : 0 ≤ c
  logFactor : 0 ≤ H
  setupFactor : 0 ≤ Q
  setupNonneg : ∀ w,0 ≤ S w
  route : PositionRunsAt router ρ K
  raw : let hw : 0 < (dimensions r).2 := (show 0 < 2 by decide).trans_le sel.wide
    Runs piece (fun v : PhysicalWalshNode.Admitted hw sel.plan =>
      pieceTimeBound ((dimensions r).1+1) sel.plan.calls ρ B L S v.val.shape)
      (fun v => pieceSpaceBound ((dimensions r).1+1) c S v.val.shape)
      (rawInput hw sel.plan) (rawOutput hw sel.plan)
  large : ∀ w ≥ cut, walshTemplateCut K r ≤ addressBits w
  overhead : ∀ w ≥ cut,let k := addressBits w
    0 ≤ L (componentBits k) ∧ L (componentBits k) ≤ H*(1+Real.log (2+k))
  setup : ∀ w ≥ cut,let k := addressBits w
    S (componentBits k) ≤ Q*(k+1:ℝ)^q

theorem effectiveWalshProfile {P : Type} [Primcodable P] {I : P → Type}
    (r : P → Raw) (hs : Computable r) {num den : P → ℕ} (sel : ∀ j,Selected (num j) (den j) (r j))
    (router piece : P → Cmd) (er : Effective ltr router) (ep : Effective ltr piece)
    (R : ℕ) (wr : ∀ j,Within R (router j)) (wp : ∀ j,Within R (piece j))
    (n : ∀ j,I j → ℕ) (hv : ∀ j i,Directory (n j i)) (dir : ∀ j,I j → Bool)
    (hd : ∀ j i,4 ≤ (box (n j i)).length) (hn : ∀ j i,2 ≤ n j i)
    (K : P → ℕ) (large : ∀ j i,walshTemplateCut (K j) (r j) ≤ addressBits (n j i))
    (route : ∀ j,PositionTotalAt (router j) (K j))
    (raw : ∀ j,let hw : 0 < (dimensions (r j)).2 := (show 0 < 2 by decide).trans_le (sel j).wide
      ∃ t s, Runs (piece j) t s (rawInput hw (sel j).plan) (rawOutput hw (sel j).plan))
    (good : P → Prop) (cut : P → ℕ) (ρ : P → ℝ)
    (fast : ∀ j,good j → Nonempty (WalshSharpRelease (sel j) (router j) (piece j) (ρ j) (cut j))) :
    ∃ arena clock : P → ℕ → ℕ,
      EffectiveImplementsAt n hv dir hd arena clock .walsh ∧
      (∀ j w,w ≤ arena j w ∧ arena j w ≤ clock j w) ∧
      ∀ j,good j → ∀ w ≥ cut j, arena j w = w ∧
        clock j w = max w (Pieces.sparseTime (ρ j) (addressBits w)) := by
  let width j (e : WalshRowInput n hv dir j) := n j e.val.instanceIndex
  have hA : Computable (fun j => (dimensions (r j)).1+1) :=
    Primrec.nat_add.to_comp.comp ((Primrec.fst.comp primrec_dimensions).to_comp.comp hs) (Computable.const 1)
  have hW := (Primrec.snd.comp primrec_dimensions).to_comp.comp hs
  have gen : Effective ltr (walshSource r router piece) := planCmd_effective hA hW er ep
  obtain ⟨R',pos,register⟩ := planCmd_within R
  have within j : Within R' (walshSource r router piece j) := register _ _ _ _ (wr j) (wp j)
  have total j (e : WalshRowInput n hv dir j) :
      ∃ t, ∀ env reg, Fits env (walshSource r router piece j) (pile 0 (walshRawArgument n hv dir j e) reg)
        (pile 0 (walshRawReply r sel n hv dir j e) reg) t := by
    obtain ⟨t,s,h⟩ := walshSource_total r sel router piece n hv dir j (raw j) (route j) (large j)
    exact fits_of_named_run h e
  have sharp j (ok : good j) := (fast j ok).some
  obtain ⟨arena,clock,family,bounds,rate⟩ := total_width_budgets good cut width
    (walshRawArgument n hv dir) (walshRawReply r sel n hv dir)
    (fun _ w => 75000*(w+1)+2*addressBits w+2) (fun _ w => 75000*(w+1))
    (fun j w => Pieces.sparseTime (ρ j) (addressBits w))
    (fun j e => walshRawArgument_size n hv dir j e (hn j e.val.instanceIndex))
    (fun j e => walshRawReply_size r sel n hv dir j e (hn j e.val.instanceIndex))
    (walshSource r router piece) R' gen pos within total (by
      intro j ok
      let rel := sharp j ok
      let row := fun v : {e : WalshRowInput n hv dir j // cut j ≤ width j e} => v.val
      have F := walshSource_sparse r sel router piece n hv dir j row rel.positive rel.cost rel.cells
        rel.setupNonneg rel.logFactor rel.setupFactor rel.raw rel.route
        (fun v => rel.large _ v.property) (fun v => rel.overhead _ v.property) (fun v => rel.setup _ v.property)
      apply F.bound 1 49 (fun _ => by simp [row,width]) (fun v => ?_)
      have h := (packed_volume (hn j v.val.val.instanceIndex)).2
      change capacity (n j v.val.val.instanceIndex)*addressBits (n j v.val.val.instanceIndex)+1 ≤ 49*(n j v.val.val.instanceIndex+1)
      omega)
  refine ⟨arena,clock,?_,bounds,rate⟩
  let hw j := (show 0<2 by decide).trans_le (sel j).wide
  apply effectiveWalsh_of_selectedFamilyAt n hv dir hd hn arena clock (fun j i => (bounds j _).1)
    (fun j i => (bounds j _).2) hw (fun j => (sel j).plan)
    (fun j => (show 1<5 by decide).trans_le (sel j).large) (fun j => (sel j).correct)
    (fun j => selectedFactor (sel j)) (fun j i => (le_max_right ..).trans ((le_max_right ..).trans (large j i))) family

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
