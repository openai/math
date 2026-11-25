import OAI.Computability.NearSquareRoot.PhysicalWalshEffectiveHeaders
import OAI.Computability.NearSquareRoot.PhysicalWalshSweep

/-! # Effective emitted source for the complete recursive Walsh-piece sweep

The same source emitter attaches a template-specific agenda generator before
the tail-recursive, record-preserving loop over the generated descriptors.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Space PhysicalWalshNode CommonRegisters GeneratorSyntax

noncomputable def sweepCmd (A W : ℕ) (step : Cmd) :=
  agendaCmd (List Dusk.Pair) (effectiveHeaders.choose (A,W)) step

theorem sweepCmd_effective {P : Type} [Primcodable P] {A W : P → ℕ} {step : P → Cmd}
    (ha : Computable A) (hw : Computable W) (hs : Effective ltr step) :
    Effective ltr (fun p => sweepCmd (A p) (W p) (step p)) := by
  obtain ⟨R,d,he,_⟩ := effectiveHeaders.choose_spec
  exact (KernelEffectiveFamily.effective_left (he.comp (ha.pair hw))).join
    (Sequence.walkCmd_effective Header.Wire (List Dusk.Pair) hs)

theorem sweepCmd_within (r : ℕ) : ∃ R, 0<R ∧
    ∀ (A W : ℕ) (step : Cmd), Within r step → Within R (sweepCmd A W step) := by
  obtain ⟨r₁,d,_,positive,h,rest⟩ := effectiveHeaders.choose_spec
  obtain ⟨r₂,pos,walk⟩ := Sequence.walkCmd_within Header.Wire (List Dusk.Pair) r
  refine ⟨max r₁ r₂,positive.trans_le (le_max_left ..),fun A W step hs => ?_⟩
  exact ⟨RegisterSelect.within_mono (le_max_left ..) _ (KernelEffectiveFamily.within_left positive (h (A,W))),
    RegisterSelect.within_mono (le_max_right ..) _ (walk step hs)⟩

/-- Run the effective agenda program with the certified individual step on
the actual trajectory and its integral sum of level-dependent clock charges. -/
theorem generatedSweepNamed {I : Type} {A W : ℕ} {step : Cmd} (hA : 1 < A) (hW : 0 < W)
    (k s w : I → ℕ) (v : I → ℕ → List Dusk.Pair) (t : I → ℕ → ℕ) (space : I → ℕ) :
    let L i := schedule A W hW (k i) (s i) (w i)
    (∀ i j, j ≤ (L i).length → size (v i j) ≤ space i) →
    EffectiveBoundedTask.Runs step (fun z : (i : I) × Fin (L i).length => t z.1 ((L z.1).get z.2).level)
        (fun z => space z.1) (fun z => send (Header.wire A ((L z.1).get z.2),v z.1 z.2))
        (fun z => send (Header.wire A ((L z.1).get z.2),v z.1 (z.2.val+1))) →
    ∃ d C : ℕ,
      let G i := C*(k i+s i+w i+1)^d+space i
      let clock i := 2*(G i+1) + ∑ j : Fin (walshPieceDigits A (s i)).length,
        (walshPieceDigits A (s i)).get j * (t i j+G i+1)
      EffectiveBoundedTask.Runs (sweepCmd A W step) clock G (fun i => send (((tally (k i),tally (s i)),tally (w i+1)),v i 0))
        (fun i => send (v i (L i).length)) := by
  intro L fit piece
  obtain ⟨R,d,_,_,_,headers⟩ := effectiveHeaders.choose_spec
  have hh := headers A W hA hW
  obtain ⟨J,hJ⟩ := hh.task.endpointSize
  let C := 2*(J+1)
  refine ⟨d,C,?_⟩
  have big (p : ℕ×ℕ×ℕ) : (p.1+p.2.1+p.2.2+1)^d ≤ C*(p.1+p.2.1+p.2.2+1)^d :=
    Nat.le_mul_of_pos_left _ (by dsimp [C]; omega)
  apply generatedSweepWith (header:=effectiveHeaders.choose (A,W)) (step:=step) d C hA hW
    (hh.mono big big) _ k s w v t space fit piece
  intro p
  let f := (p.1+p.2.1+p.2.2+1)^d
  have hz : 0 < f := Nat.pow_pos (Nat.succ_pos _)
  apply ((le_max_right _ _).trans (hJ p)).trans
  change J*(f+1) ≤ C*f
  calc
    J*(f+1) ≤ (J+1)*(2*f) := Nat.mul_le_mul (Nat.le_succ _) (by omega)
    _ = C*f := by unfold C; ring

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
