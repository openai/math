import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSelected
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalRealize

/-! # The four routed transitions of a selected native repair command -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.Selected

open IntegerMultiplication IntegerMultiplication.Code Interchange.Template InterchangeROM Space

variable {R V U L X : Type} [Field R] [Fintype V] [Fintype U]

/-- A physical chart stage and the two sparse sweeps name their recursive charges.
The sign correction consumes a generated mask and has no recursive charge. -/
structure Cases (x : Data) (t : Spec R V U x.m) (tag : X → Fin x.m → Bool)
    (fw bw : (X → R) → X → R) (advance : Bank R L X V → Bank R L X V)
    (wide : Bank R L X V → List Tree) (short : Bank R L X U → List Tree)
    (env : Env) (header : Tree) (stageCalls checkLanes childTime childCap childDepth : ℕ)
    (M chartFactor sweepFactor correctFactor : ℕ) : Prop where
  chart (z : Bank R L X V) : SweepBank.Run env (stage x) (packet header (wide z))
    (packet header (wide (advance z)))
    ⟨chartFactor*M+stageCalls*childTime,chartFactor*M+childCap,chartFactor*M+childDepth⟩
  forward (u v : Bank R L X U) : SweepBank.Run env (sweepLeaf x false)
    (packet header (short u ++ short v)) (packet header (short (sweep fw u) ++ short (sweep fw v)))
    ⟨sweepFactor*M+(2*checkLanes*x.m)*childTime,sweepFactor*M+childCap,sweepFactor*M+childDepth⟩
  correct (u v : Bank R L X U) : SweepBank.Run env (Selected.correct x)
    (packet header (short u ++ short v))
    (packet header (short (applyTag t tag false u v) ++ short (applyTag t tag true u v)))
    ⟨correctFactor*M,correctFactor*M,correctFactor*M⟩
  backward (u v : Bank R L X U) : SweepBank.Run env (sweepLeaf x true)
    (packet header (short u ++ short v)) (packet header (short (sweep bw u) ++ short (sweep bw v)))
    ⟨sweepFactor*M+(2*checkLanes*x.m)*childTime,sweepFactor*M+childCap,sweepFactor*M+childDepth⟩

/-- Classify a native transition by its leaf constructor, retaining the exact
multiplicity of child clocks and a single maximum child space bound. -/
theorem Cases.routed {x : Data} {t : Spec R V U x.m} {tag : X → Fin x.m → Bool}
    {fw bw : (X → R) → X → R} {advance : Bank R L X V → Bank R L X V}
    {wide : Bank R L X V → List Tree} {short : Bank R L X U → List Tree}
    {env : Env} {header : Tree} {n q time cap depth M chartFactor sweepFactor correctFactor : ℕ}
    (c : Cases x t tag fw bw advance wide short env header n q time cap depth M
      chartFactor sweepFactor correctFactor)
    {factor : ℕ} (hc : chartFactor ≤ factor) (hs : sweepFactor ≤ factor) (ht : correctFactor ≤ factor)
    (half : R) (a : Leaf) (u v : List Tree) (route : LocalTable.Lift.Routed a)
    (step : Transition t half tag fw bw advance wide short a u v) (r : Deck) (base : ℕ)
    (hd : DeckCap base r) :
    BoundedFits env (commands x a) (pile 0 (packet header u) r) (pile 0 (packet header v) r)
      (factor*M+price n q x.m (0,a)*time) (base+(factor*M+cap)) (factor*M+depth) := by
  have chart_le := Nat.mul_le_mul_right M hc
  have sweep_le := Nat.mul_le_mul_right M hs
  have correction_le := Nat.mul_le_mul_right M ht
  cases step with
  | stage z => exact (c.chart z r base hd).mono (by dsimp only [price]; omega) (by dsimp only; omega) (by dsimp only; omega)
  | forward z y =>
    exact (c.forward z y r base hd).mono (by dsimp only [price]; omega) (by dsimp only; omega) (by dsimp only; omega)
  | correct z y =>
    exact (c.correct z y r base hd).mono (by simp only [price,Nat.zero_mul,Nat.add_zero]; omega)
      (by dsimp only; omega) (by dsimp only; omega)
  | backward z y =>
    exact (c.backward z y r base hd).mono (by dsimp only [price]; omega) (by dsimp only; omega) (by dsimp only; omega)
  | duplicate | extract | restore | copyCube | finish => exact False.elim route

end InterchangeROMRepair.Physical.Selected

end NearSquareRoot
end Computability
end OAI
