import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSelector
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildLiteral
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileScan
import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyProduct

/-! # Generating the native XOR selector across arities and reserve degrees -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code Staff Strip Carry PhysicalWalsh Space PhysicalWalshCompile
open PhysicalWalshCompileChild KernelEffectiveFamily CommonRegisters GeneratorSyntax Filter
open private batch wire level active width prefFigure suffix childBits from OAI.Computability.NearSquareRoot.PhysicalWalshCompileChildHeader
open private unpack easy_unpack from OAI.Computability.NearSquareRoot.PhysicalWalshFrontSelector

/-- Compile a test of the compact descriptor with both the descriptor and
the ordered lane preserved on the work tape. The test may use the literal
arity and second control parameter. -/
theorem compileTag (test : World → Bool) (hasTest : regime.Has test) :
    ∃ (emit : ℕ × ℕ → Cmd) (R e : ℕ),
    Effective ltr emit ∧ (∀ k, Within R (emit k)) ∧
    ∀ (a W D d : ℕ), e ≤ d →
      let v := fun t : XorInput W => allowance (a+1) d t.shape
      let packet := fun t : XorInput W =>
        Tree.fork (send (Header.wire (a+1) t.shape)) (send (laneFlat (a+1) W t.shape t.row))
      ClosedRuns (emit (a,D)) v v packet
        (fun t => .fork (.atom (test ⟨a,D,0,t.shape⟩)) (packet t)) := by
  let tested (t : World) := (test t,descriptor t)
  obtain ⟨N,e,hdr,he,hh,reg,body⟩ := configuredWith tested (hasTest.pair wire)
  obtain ⟨fin,hfin⟩ : ∃ c : Cmd, KernelEffectiveFamily.Runs c unpack := easy_unpack
  obtain ⟨R,hN,hr,hf⟩ := ((eventually_ge_atTop N).and
    ((eventually_gt_atTop 0).and (RegisterSelect.within_eventually fin))).exists
  let key (k : ℕ × ℕ) : Control := (k.1+1,k.2,0)
  have keyComp : Computable key := (Computable.succ.comp Computable.fst).pair
    (Computable.snd.pair (Computable.const 0))
  let build k := (PhysicalWalshCompile.left (hdr (key k))).join fin
  have effective : Effective ltr build := (KernelEffectiveFamily.effective_left (hh.comp keyComp)).join
    (effective_const ltr fin)
  refine ⟨build,R,e,effective,fun k => ⟨within_left hr (RegisterSelect.within_mono hN _ (reg _)),hf⟩,?_⟩
  intro a W D d ed
  let A := a+1
  let s (t : XorInput W) := t.shape
  let hd (t : XorInput W) := Header.wire A (s t)
  let row (t : XorInput W) := laneFlat A W (s t) t.row
  let u (t : XorInput W) : World := ⟨a,D,0,s t⟩
  let v (t : XorInput W) := allowance A d (s t)
  have pay {j : ℕ} (hj : j ≤ d) (t : XorInput W) : (Header.scale A (s t)+1)^j ≤ v t :=
    (Nat.pow_le_pow_right (by omega) hj).trans (Nat.le_add_left ..)
  have headerFits : Small v (send ∘ hd) := by
    refine ⟨1,fun t => ?_⟩
    have h := pay (he.trans ed) t
    change Header.scale A (s t) ≤ 1*(v t+1)
    rw [pow_one] at h
    omega
  have rowFits : Small v (send ∘ row) := by
    refine ⟨16,fun t => ?_⟩
    have h := SwapPrefix.stream_cost A W d (s t) _ t.row (SwapPrefix.length_le A W (s t))
    change size (row t) ≤ 16*v t+1 at h
    change size (row t) ≤ 16*(v t+1)
    omega
  obtain ⟨C,hC⟩ := body a D (0 : Fin (a+1))
  have check : Scan (hdr (key (a,D))) v (send ∘ hd) (fun t => send (tested (u t))) := by
    refine ⟨headerFits,C,fun t env park => ?_⟩
    exact ((hC (s t)).1 env park).mono (Nat.mul_le_mul_left C ((pay ed t).trans (Nat.le_succ _)))
  let z (t : XorInput W) := (tested (u t),row t)
  have first := check.park (send ∘ row) rowFits
  have out : Small v (send ∘ z) := first.output
  exact (first.seq (Scan.linear hfin z out)).closed

/-- One effective family of selector commands, indexed by the arity
predecessor and the reserve degree, applies at every batch width. Both the
degree of polynomial descriptor setup and the register cutoff are absolute. -/
theorem compileSelector : ∃ (emit : ℕ × ℕ → Cmd) (R e : ℕ),
    Effective ltr emit ∧ (∀ k, Within R (emit k)) ∧
    ∀ (a W D d : ℕ), e ≤ d →
      let v := fun t : XorInput W => allowance (a+1) d t.shape
      let packet := fun t : XorInput W =>
        Tree.fork (send (Header.wire (a+1) t.shape)) (send (laneFlat (a+1) W t.shape t.row))
      ClosedRuns (emit (a,D)) v v packet (fun t => .fork (.atom (decide
        (XorThreshold.cutoff D (Header.scale (a+1) t.shape) ≤ Interior.L (a+1) t.shape))) (packet t)) := by
  let test (t : World) := decide (XorThreshold.cutoff t.W (Header.scale (t.a+1) t.shape) ≤ Interior.L (t.a+1) t.shape)
  have q := scaleFigureOf (fun t : World => t.a+1) World.shape level active width prefFigure suffix
  exact compileTag test (hasComparison batch q childBits)

end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
