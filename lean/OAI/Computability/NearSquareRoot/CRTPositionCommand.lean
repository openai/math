import OAI.Computability.NearSquareRoot.CRTPositionFourCommandLarge
import OAI.Computability.NearSquareRoot.CRTPositionFourCommandCutoff
import OAI.Computability.NearSquareRoot.CRTPositionSmallCommand

/-! # One position command for every address width

The command compares the length of the supplied permutation table with a
literal cutoff. Its small-width branch runs the elementary swaps. Its
large-width branch computes both reserve widths and runs the four-stage route.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd

open IntegerMultiplication IntegerMultiplication.Adic IntegerMultiplication.Code
open IntegerMultiplication.Strip IntegerMultiplication.Loom PositionProgram PositionRows
open CommonRegisters EffectiveBoundedTask GeneratorSyntax Filter

noncomputable section

def positionCmd (K a b : ℕ) (core : Cmd) : Cmd :=
  cutoffCmd K ((widthCmd a b).join (reserveCmd core)) smallCmd

theorem position_effective {P : Type} [Primcodable P] {K a b : P → ℕ} {core : P → Cmd}
    (hK : Computable K) (ha : Computable a) (hb : Computable b) (hc : Effective ltr core) :
    Effective ltr (fun j => positionCmd (K j) (a j) (b j) (core j)) :=
  cutoff_effective hK ((width_effective_on ha hb).join (reserve_effective hc)) small_effective_const

theorem position_within (R : ℕ) :
    ∃ S : ℕ, 0 < S ∧ ∀ K a b c, Within R c → Within S (positionCmd K a b c) := by
  obtain ⟨B,hB,res⟩ := reserve_within R
  obtain ⟨S,hs,hcut,hw,hsmall⟩ := ((eventually_ge_atTop B).and
    (cutoff_within.and (width_within_eventually.and small_within))).exists
  exact ⟨S,by omega,fun K a b c hc => hcut _ _ _ ⟨hw _ _,RegisterSelect.within_mono hs _ (res c hc)⟩ hsmall⟩

/-- The natural clock and the literal input and output trees of a position command. -/
def PositionRuns (c : Cmd) (ρ : ℝ) {I : Type} (k : I → ℕ) {U : I → Type}
    (u : (i : I) → Series (U i)) (p : (i : I) → Equiv.Perm (Fin (k i)))
    (f : (i : I) → Block 2 (k i) → U i → Bead) : Prop :=
  let V i := 2^(k i)*(u i).count
  Runs c (fun i => V i*(positionFactor ρ (k i)+1)) V
    (fun i => .fork (send (Reflections.table (p i))) (cloth (fun i => line 2 (k i)) u f i))
    (cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z)))

private theorem withSmall {ρ : ℝ} (K : ℕ) (big : Cmd) {I : Type} (k : I → ℕ)
    {U : I → Type} (u : (i : I) → Series (U i)) (pos : ∀ i, 0 < (u i).count)
    (p : (i : I) → Equiv.Perm (Fin (k i))) (f : (i : I) → Block 2 (k i) → U i → Bead)
    (large : PositionRuns big ρ (fun i : {i // K < k i} => k i.val)
      (fun i => u i.val) (fun i => p i.val) (fun i => f i.val)) :
    PositionRuns (cutoffCmd K big smallCmd) ρ k u p f := by
  let V i := 2^(k i)*(u i).count
  let T i := V i*(positionFactor ρ (k i)+1)
  let data := cloth (fun i => line 2 (k i)) u f
  let output := cloth (fun i => line 2 (k i)) u (fun i z => f i (flatBitPullback (p i) z))
  have room i : V i ≤ T i := Nat.le_mul_of_pos_right _ (by omega)
  have area i : 2^(k i) ≤ V i := Nat.le_mul_of_pos_right _ (pos i)
  have size i : (data i).count ≤ 5*(V i+1) := (ReserveSmall.beadClothCap k _ u f pos
    (fun _ => le_rfl) i).trans (Nat.mul_le_mul_left _ (Nat.le_succ _))
  apply cutoff_runs K k T V p data output room area 5 size
  · exact large
  · have small := small_cloth_runs (I := {i // k i ≤ K}) K (fun i => k i.val)
      (fun i => (u i.val).count) (fun i => u i.val) (fun i => p i.val) (fun i => f i.val)
      (fun i => i.property) (fun i => pos i.val) (fun _ => le_rfl)
    exact small.mono (fun i => room i.val) (fun _ => le_rfl)

/-- Explicit reserve and cutoff candidates produce an all-width command whenever
the two reserves fit beyond that cutoff. -/
theorem position_runs_from_cutoff {ρ : ℝ} (positive : 0 ≤ ρ) (core : Cmd)
    (hc : RowCommand.GroupedRuns core ρ) :
    ∃ D : ℕ, ∀ a b K : ℕ, D ≤ a → D ≤ b → ⌈ρ⌉₊+2 ≤ b →
      (∀ k : ℕ, K < k → payloadBits a k + payloadBits b k ≤ k/2-2) →
      ∀ {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i))
        (_pos : ∀ i, 0 < (u i).count) (p : (i : I) → Equiv.Perm (Fin (k i)))
        (f : (i : I) → Block 2 (k i) → U i → Bead), PositionRuns (positionCmd K a b core) ρ k u p f := by
  obtain ⟨D,run⟩ := runs_from_fits positive core hc
  refine ⟨D,?_⟩
  intro a b K ha hb hρ fit I k U u pos p f
  apply withSmall K _ k u pos p f
  exact run a b ha hb hρ (I := {i // K < k i}) (fun i => k i.val) (fun i => u i.val) (fun i => pos i.val)
    (fun i => p i.val) (fun i => f i.val) (fun i => Nat.zero_lt_of_lt i.property)
    (fun i => fit _ i.property)

/-- One set of literal command parameters works for every permutation table
and every positive-width record file, including an empty address field. -/
theorem position_runs {ρ : ℝ} (positive : 0 ≤ ρ) (core : Cmd) (hc : RowCommand.GroupedRuns core ρ) :
    ∃ a b K : ℕ, ∀ {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i))
      (_pos : ∀ i, 0 < (u i).count) (p : (i : I) → Equiv.Perm (Fin (k i)))
      (f : (i : I) → Block 2 (k i) → U i → Bead), PositionRuns (positionCmd K a b core) ρ k u p f := by
  obtain ⟨a,b,K,large⟩ := large_named_runs positive core hc
  refine ⟨a,b,K,?_⟩
  intro I k U u pos p f
  apply withSmall K _ k u pos p f
  exact large (I := {i // K < k i}) (fun i => k i.val) (fun i => u i.val) (fun i => pos i.val) (fun i => p i.val)
    (fun i => f i.val) (fun i => i.property)

end
end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
