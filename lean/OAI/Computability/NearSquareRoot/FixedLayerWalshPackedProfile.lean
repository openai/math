import OAI.Computability.NearSquareRoot.FixedLayerWalshSharp

/-! # The effective Walsh row profile from named packed programs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace FixedLayer

open IntegerMultiplication Code FixedCandidate FixedPoint DigitPacking Filter
open PhysicalWalsh PhysicalWalsh.GatherProgram PhysicalWalshNode KernelPass
  KernelPass.ComputableSyntax PhysicalWalshCompile.Dispatch EffectiveBoundedTask
  CommonRegisters GeneratorSyntax

/-- A good tuple supplies a packed time and space estimate for its own
recursive piece command, with constants allowed to depend on the tuple. -/
def PackedPieceRate {num den : ℕ} {r : Raw} (sel : Selected num den r) (piece : Cmd) (ρ : ℝ) : Prop :=
  let hw : 0 < (dimensions r).2 := (show 0 < 2 by decide).trans_le sel.wide
  ∃ (B c : ℝ) (K d : ℕ), 0 ≤ B ∧ 0 ≤ c ∧
    Runs piece (fun v : PhysicalWalshNode.Admitted hw sel.plan =>
      pieceTimeBound ((dimensions r).1+1) sel.plan.calls ρ B RouterClock.logWidth
        (envelopeSetup K d (fun _ => 0)) v.val.shape)
      (fun v => pieceSpaceBound ((dimensions r).1+1) c (envelopeSetup K d (fun _ => 0)) v.val.shape)
      (rawInput hw sel.plan) (rawOutput hw sel.plan)

/-- The row dispatcher has a total effective Walsh implementation for all
tuples. For every good tuple its named router and recursive piece yield the
fixed-exponent row clock and eventually an operand-linear arena. -/
theorem effectiveWalshPackedProfile {P : Type} [Primcodable P] {I : P → Type}
    (r : P → Raw) (hs : Computable r) {num den : P → ℕ} (sel : ∀ j,Selected (num j) (den j) (r j))
    (router piece : P → Cmd) (er : Effective ltr router) (ep : Effective ltr piece)
    (R : ℕ) (wr : ∀ j,Within R (router j)) (wp : ∀ j,Within R (piece j))
    (n : ∀ j,I j → ℕ) (hv : ∀ j i,Directory (n j i)) (dir : ∀ j,I j → Bool)
    (hd : ∀ j i,4 ≤ (box (n j i)).length) (hn : ∀ j i,2 ≤ n j i)
    (K : P → ℕ) (large : ∀ j i,walshTemplateCut (K j) (r j) ≤ addressBits (n j i))
    (route : ∀ j,PositionTotalAt (router j) (K j))
    (raw : ∀ j,let hw : 0 < (dimensions (r j)).2 := (show 0 < 2 by decide).trans_le (sel j).wide
      ∃ t s, Runs (piece j) t s (rawInput hw (sel j).plan) (rawOutput hw (sel j).plan))
    (good : P → Prop) (ρ : P → ℝ) (positive : ∀ j,good j → 0 < ρ j)
    (routeRate : ∀ j,good j → ∃ k, PositionRunsAt (router j) (ρ j) k)
    (pieceRate : ∀ j,good j → PackedPieceRate (sel j) (piece j) (ρ j)) :
    ∃ arena clock : P → ℕ → ℕ,
      EffectiveImplementsAt n hv dir hd arena clock .walsh ∧
      (∀ j w,w ≤ arena j w ∧ arena j w ≤ clock j w) ∧
      ∀ j,good j → (∀ᶠ w in atTop,arena j w = w) ∧ RowClock (ρ j) (clock j) := by
  classical
  have release j (h : good j) : ∃ cut, Nonempty (WalshSharpRelease (sel j) (router j) (piece j) (ρ j) cut) := by
    obtain ⟨k,rcost⟩ := routeRate j h
    obtain ⟨B,c,D,d,hB,hc,pcost⟩ := pieceRate j h
    exact WalshSharpRelease.of_packed (sel j) (positive j h) hB hc rcost pcost
  let cut j := if h : good j then (release j h).choose else 0
  have sharp j (h : good j) : Nonempty (WalshSharpRelease (sel j) (router j) (piece j) (ρ j) (cut j)) := by
    simpa only [cut,dite_eq_left h] using (release j h).choose_spec
  obtain ⟨arena,clock,branch,bounds,profile⟩ := effectiveWalshProfile r hs sel router piece er ep R wr wp
    n hv dir hd hn K large route raw good cut ρ sharp
  exact ⟨arena,clock,branch,bounds,fun j h =>
    walshProfile_rowClock arena clock cut (positive j h).le (profile j h)⟩

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
