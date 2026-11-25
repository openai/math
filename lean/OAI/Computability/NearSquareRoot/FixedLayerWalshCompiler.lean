import OAI.Computability.NearSquareRoot.FixedLayerWalshPackedProfile
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileNodeRoutedTotal
import OAI.Computability.NearSquareRoot.SelectedPhysicalKernel

/-! # From the physical XOR opcodes to both costs of the same compiled piece -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 1500000
noncomputable section
namespace FixedLayer

open IntegerMultiplication Code Space FixedPoint KernelPass KernelPass.ComputableSyntax
open PhysicalWalsh PhysicalWalshNode PhysicalWalshCompile PhysicalWalshCompile.Dispatch
open CommonRegisters GeneratorSyntax EffectiveBoundedTask

/-- A closed physical estimate for the controlled routing opcodes in one
selected file. The local estimates may use any sufficient reserve degree. -/
def SharpXorCosts (flat : Raw → Op → Cmd) (r : Raw) (ρ : ℝ) (D : ℕ) : Prop :=
  let a := (dimensions r).1
  let W := (dimensions r).2
  ∃ d ≥ D, ∃ (extra : PhysicalWalshNode.Shape → ℕ) (c : ℝ), 0 ≤ c ∧
    Dispatch.XorRuns flat a W r.2 (nodeScan a W d extra) (nodeArena a W d) ∧
    ∀ t, withinWidth (a+1) t → (extra t : ℝ) ≤
      localTime (a+1) ρ c (RouterClock.logWidth t.w) 0 t.level (bitVolume (a+1) t)

/-- A larger proof allowance leaves the compiled instruction unchanged. -/
theorem SharpXorCosts.atDegree {flat : Raw → Op → Cmd} {r : Raw} {ρ : ℝ}
    (h : SharpXorCosts flat r ρ 0) (D : ℕ) : SharpXorCosts flat r ρ D := by
  obtain ⟨d,_,extra,c,hc,runs,bound⟩ := h
  refine ⟨max d D,le_max_right ..,extra,c,hc,?_,bound⟩
  have grown t : nodeArena (dimensions r).1 (dimensions r).2 d t ≤
      nodeArena (dimensions r).1 (dimensions r).2 (max d D) t :=
    max_le_max_right _ (allowance_mono (le_max_left d D) t)
  intro op tag hi hj apart
  exact (runs op tag hi hj apart).mono (fun i => Nat.add_le_add_right (grown _) _) (fun i => grown _)

def TotalXorCosts (flat : Raw → Op → Cmd) (r : Raw) : Prop :=
  ∃ scan arena, Dispatch.XorRuns flat (dimensions r).1 (dimensions r).2 r.2 scan arena

def TotalPiece {num den : ℕ} {r : Raw} (sel : Selected num den r) (c : Cmd) : Prop :=
  let hw : 0 < (dimensions r).2 := (show 0<2 by decide).trans_le sel.wide
  ∃ time space, Runs c time space (rawInput hw sel.plan) (rawOutput hw sel.plan)

/-- One invocation of certificate search and of the actual compiler generates
both the source and its correctness and cost witnesses. -/
theorem compiledPieceProfiles {Z : Type} [Primcodable Z]
    (flat : Z × Raw → Op → Cmd) (eff : Effective ltr (Function.uncurry flat))
    (M : ℕ) (bounded : ∀ r op, Within M (flat r op)) :
    ∃ (r : ℕ → Raw) (cmd : Z × ℕ → Cmd) (R D : ℕ), Computable r ∧ Effective ltr cmd ∧
      0 < R ∧ 1 ≤ D ∧ (∀ p,Within R (cmd p)) ∧
      ∃ sel : (j : ℕ) → Selected (j+3) (2*(j+2)) (r j), ∀ z j,
        (TotalXorCosts (fun a => flat (z,a)) (r j) → TotalPiece (sel j) (cmd (z,j))) ∧
        (SharpXorCosts (fun a => flat (z,a)) (r j) (Generator.midExponent j) D →
          PackedPieceRate (sel j) (cmd (z,j)) (Generator.midExponent j)) := by
  obtain ⟨r,cmd,R,D,hr,_,_,hc,hR,hD,reg,sel,total,rate⟩ := Node.compileRoutedTotalWith flat eff M bounded
  refine ⟨r,cmd,R,D,hr,hc,hR,hD,reg,sel,fun z j => ⟨?_,?_⟩⟩
  · rintro ⟨scan,arena,h⟩
    exact total z j scan arena h
  · rintro ⟨d,hd,extra,c,hc,run,bound⟩
    have eqn : (((j+3:ℕ):ℝ)/(2*(j+2):ℕ)) = Generator.midExponent j := by
      unfold Generator.midExponent
      push_cast
      have hj := Nat.cast_nonneg (α:=ℝ) j
      field_simp
      ring
    obtain ⟨K,_,ready⟩ := rate j d hd
    rw [eqn] at ready
    obtain ⟨B,hB,exec⟩ := ready z extra run c RouterClock.logWidth (fun _ => 0) hc
      RouterClock.one_le_logWidth (fun _ => le_rfl) bound
    exact ⟨B,4*K+c,K,d,hB,by positivity,exec⟩

end FixedLayer

end

end NearSquareRoot
end Computability
end OAI
