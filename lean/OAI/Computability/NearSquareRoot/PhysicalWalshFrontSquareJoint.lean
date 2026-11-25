import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquare
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorEnds

/-! # Total and rate-sensitive executions of the same selected Walsh gate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code Space PhysicalWalsh GeneratorSyntax CommonRegisters

/-- Correct output with arbitrary costs on the inputs taking one branch. -/
def branchTotal {a W : ℕ} (g : Fin (a+1) × Fin (a+1)) (P : Shape → Prop) (c : Cmd) : Prop :=
  PhysicalWalshCompileInterior.Ends c (fun t : {t : XorInput W // P t.shape} =>
    send (Header.wire (a+1) t.val.shape,laneFlat (a+1) W t.val.shape t.val.row))
    (fun t => send (laneFlat (a+1) W t.val.shape (xor a g t.val.shape t.val.row)))

/-- Correct output on every shape, also for slower parameter choices. -/
def flatTotal {a W : ℕ} (g : Fin (a+1) × Fin (a+1)) (c : Cmd) : Prop :=
  PhysicalWalshCompileInterior.Ends c (fun t : XorInput W =>
    send (Header.wire (a+1) t.shape,laneFlat (a+1) W t.shape t.row))
    (fun t => send (laneFlat (a+1) W t.shape (xor a g t.shape t.row)))

private theorem chooseTotal {I : Type} (P : I → Prop) [DecidablePred P] (q r : I → Tree)
    {tag c d : Cmd} {V : I → ℕ} (head : ClosedRuns tag V V q (fun i => .fork (.atom (decide (P i))) (q i)))
    (small : PhysicalWalshCompileInterior.Ends c (fun i : {x // ¬ P x} => q i.val) (r ∘ Subtype.val))
    (large : PhysicalWalshCompileInterior.Ends d (fun i : {x // P x} => q i.val) (r ∘ Subtype.val)) :
    PhysicalWalshCompileInterior.Ends (tag.join (decodeBit c d)) q r := by
  obtain ⟨st,ss,slow⟩ := small
  obtain ⟨lt,ls,fast⟩ := large
  let T i := V i + (if h : P i then lt ⟨i,h⟩ else st ⟨i,h⟩)
  let S i := V i + (if h : P i then ls ⟨i,h⟩ else ss ⟨i,h⟩)
  have left : ClosedRuns c (T ∘ Subtype.val) (S ∘ Subtype.val)
      (fun i : {x // ¬ P x} => q i.val) (r ∘ Subtype.val) :=
    slow.mono (fun x => by simpa only [T,Function.comp_apply,dite_eq_right x.property] using Nat.le_add_left (st x) (V x.val))
      (fun x => by simpa only [S,Function.comp_apply,dite_eq_right x.property] using Nat.le_add_left (ss x) (V x.val))
  have right : ClosedRuns d (T ∘ Subtype.val) (S ∘ Subtype.val)
      (fun i : {x // P x} => q i.val) (r ∘ Subtype.val) :=
    fast.mono (fun x => by simpa only [T,Function.comp_apply,dite_eq_left x.property] using Nat.le_add_left (lt x) (V x.val))
      (fun x => by simpa only [S,Function.comp_apply,dite_eq_left x.property] using Nat.le_add_left (ls x) (V x.val))
  exact ⟨T,S,EffectiveBoundedTask.Runs.sequence
    (head.mono (fun _ => Nat.le_add_right ..) (fun _ => Nat.le_add_right ..))
    (chooseNamed P left right)⟩

/-- The selector, lower gate and native gate are physically identical in the
two conclusions. A slow candidate can carry its own arbitrary execution
bound, while a good candidate obtains the square-log clock and node arena. -/
theorem compileSquareGateJoint {Z : Type} [Primcodable Z] (a : Z → ℕ) (ha : Computable a)
    (small large : Z → Cmd) (es : Effective ltr small) (el : Effective ltr large) (R : ℕ)
    (regS : ∀ z, Within R (small z)) (regL : ∀ z, Within R (large z)) :
    ∃ (emit : Z → Cmd) (N e : ℕ), Effective ltr emit ∧ 0<N ∧ (∀ z, Within N (emit z)) ∧
      (∀ (z : Z) (W : ℕ) (ρ : ℝ) (arity : 4 ≤ a z) (d : ℕ), e ≤ d →
        let A := a z+1
        let g := Interior.axes (a z) arity
        branchRuns (W:=W) g (fun s => ¬ squareFits (a z) s)
          (nodeScan (a z) W d (ElementarySweep.extra A)) (nodeArena (a z) W d) (small z) →
        branchRuns (W:=W) g (squareFits (a z))
          (fun s => allowance A d s + Interior.extra (a z) W ρ s) (allowance A d) (large z) →
        PhysicalWalshCompileXorPacket.FlatRuns (W:=W)
          (nodeScan (a z) W d (squareExtra (a z) W ρ)) (nodeArena (a z) W d) g (emit z)) ∧
      ∀ z W (arity : 4 ≤ a z), let g := Interior.axes (a z) arity
        branchTotal (W:=W) g (fun s => ¬ squareFits (a z) s) (small z) →
        branchTotal (W:=W) g (squareFits (a z)) (large z) → flatTotal (W:=W) g (emit z) := by
  obtain ⟨tag,K,e,et,rt,ht⟩ := compileSquareSelector
  obtain ⟨N,ee,hN,reg,run⟩ := compileGateAt a (fun z => squareDegree (a z+1)) (tag ∘ a) K e (et.comp ha)
    (fun z => rt _) (fun z W d => ht (a z) W d) small large es el R regS regL
  refine ⟨_,N,e,ee,hN,reg,run,?_⟩
  intro z W arity g sm lg
  exact chooseTotal (fun t : XorInput W => squareFits (a z) t.shape) _ _
    (ht (a z) W e le_rfl) sm lg

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
