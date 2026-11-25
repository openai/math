import OAI.Computability.NearSquareRoot.FixedCandidateJointParameters
import OAI.Computability.NearSquareRoot.CRTPositionRouterTotal
import OAI.Computability.NearSquareRoot.InterchangeROMBinarySelected

/-! # The midpoint rectangle and address-router files on the common arithmetic tuples -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CandidateParameters

open IntegerMultiplication Code Adic Strip Loom GeneratorSyntax CommonRegisters Controlled
open PositionProgram Filter

/-- The degree of the charged rectangle packet and the register file are common
to all exponents. The rectangle command takes only the exponent index. -/
structure NativeFiles where
  degree : ℕ
  registers : ℕ
  rectangle : ℕ → Cmd
  effective : GeneratorSyntax.Effective ltr rectangle
  within : ∀ j, Within registers (rectangle j)
  physical : ∀ j, InterchangeROMBinary.RectPhysical (rectangle j) (Generator.midExponent j) degree

/-- Apply the physical binary conversion to the actual native compiler, with
selector index `2*j+2` to share the signed kernel's midpoint exponent. -/
noncomputable def selectedFiles (F : InterchangeROMFamily.NativeFamily) : NativeFiles := Classical.choice <| by
  obtain ⟨D,R,c,eff,run⟩ := InterchangeROMBinary.Selected.ofNative F
  let ix (j : ℕ) := 2*j+2
  have hix : Primrec ix := Primrec.nat_add.comp (Primrec.nat_mul.comp (.const 2) .id) (.const 2)
  refine ⟨⟨D,R,fun j => c (ix j),eff.comp hix.to_comp,fun j => (run (ix j)).1,?_⟩⟩
  intro j
  exact (native_exponent (j,0,0,0)) ▸ (run (ix j)).2

namespace NativeFiles

abbrev rectangleFile (r : NativeFiles) (p : Guess) := r.rectangle (exponent p)

theorem rectangleFile_effective (r : NativeFiles) : GeneratorSyntax.Effective ltr r.rectangleFile :=
  r.effective.comp exponent_pr.to_comp

theorem contract (r : NativeFiles) (j : ℕ) : Controlled.Effective.rectContract (r.rectangle j) (Generator.midExponent j) :=
  ⟨r.degree,r.physical j⟩

/-- This position source is shared by all array inputs and independent of the
extra exterior degree used by sparse mask passes. -/
noncomputable def positionFile (r : NativeFiles) (p : Guess) :=
  routeCmd (positionLow p) (positionHigh p) (r.rectangleFile p)

theorem positionFile_effective (r : NativeFiles) : GeneratorSyntax.Effective ltr r.positionFile :=
  routeCmd_effective positionLow_pr.to_comp positionHigh_pr.to_comp r.rectangleFile_effective

theorem positionFile_within (r : NativeFiles) : ∃ R, 0 < R ∧ ∀ p, Within R (r.positionFile p) := by
  obtain ⟨R,pos,w⟩ := routeCmd_within r.registers
  exact ⟨R,pos,fun p => w _ _ _ (r.within (exponent p))⟩

private theorem rate_pos (j : ℕ) : 0 ≤ Generator.midExponent j := by unfold Generator.midExponent; positivity

theorem positionFile_total (r : NativeFiles) (p : Guess) {I : Type} (k : I → ℕ)
    {U : I → Type} (u : (i : I) → Series (U i)) (hu : ∀ i, 0 < (u i).count)
    (per : (i : I) → Equiv.Perm (Fin (k i))) (f : (i : I) → Block 2 (k i) → U i → Bead) :
    ∃ t, EffectiveTask.Runs (r.positionFile p) t
      (together (fun i => send (Reflections.table (per i))) (cloth (fun i => line 2 (k i)) u f))
      (cloth (fun i => line 2 (k i)) u (fun i x => f i (flatBitPullback (per i) x))) :=
  routeCmd_total (rate_pos _) (r.contract _) _ _ k u hu per f

/-- A proof-side reserve threshold for the fixed file at index `j`. -/
noncomputable def positionDegree (r : NativeFiles) (j : ℕ) :=
  (routeCmd_runs (rate_pos j) (r.contract j)).choose

def PositionGood (r : NativeFiles) (p : Guess) : Prop :=
  r.positionDegree (exponent p) ≤ positionLow p ∧ r.positionDegree (exponent p) ≤ positionHigh p ∧
  ⌈Generator.midExponent (exponent p)⌉₊ + 2 ≤ positionHigh p

theorem positionFile_runs (r : NativeFiles) (p : Guess) (h : r.PositionGood p)
    {I : Type} (k : I → ℕ) {U : I → Type} (u : (i : I) → Series (U i)) (hu : ∀ i, 0 < (u i).count)
    (per : (i : I) → Equiv.Perm (Fin (k i))) (f : (i : I) → Block 2 (k i) → U i → Bead) :
    PositionCmd.PositionRuns (r.positionFile p) (Generator.midExponent (exponent p)) k u per f :=
  (routeCmd_runs (rate_pos _) (r.contract _)).choose_spec _ _ h.1 h.2.1 h.2.2 k u hu per f

theorem eventually_positionGood (r : NativeFiles) (j : ℕ) :
    ∀ᶠ a : ℕ in atTop, ∀ᶠ b : ℕ in atTop, ∀ D : ℕ, r.PositionGood (j,a,b,D) := by
  filter_upwards [eventually_ge_atTop (r.positionDegree j)] with a ha
  filter_upwards [eventually_ge_atTop (r.positionDegree j),eventually_ge_atTop (⌈Generator.midExponent j⌉₊+2)]
    with b hb hb'
  exact fun _ => ⟨ha,hb,hb'⟩

end NativeFiles
end FixedCandidate.CandidateParameters

end NearSquareRoot
end Computability
end OAI
