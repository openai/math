import OAI.Computability.NearSquareRoot.PhysicalWalshFrontDispatch
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSelectorNamed
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorPacket
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Emitting the live threshold branch around named front gates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode.FrontDispatch

open IntegerMultiplication Code Space PhysicalWalsh CommonRegisters GeneratorSyntax

/-- The threshold uses the actual encoded compact shape. -/
def fitsReserve (a D : ℕ) (s : Shape) : Prop :=
  XorThreshold.cutoff D (Header.scale (a+1) s) ≤ Interior.L (a+1) s

instance (a D : ℕ) (s : Shape) : Decidable (fitsReserve a D s) := inferInstanceAs (Decidable (_ ≤ _))

/-- A branch command is required to operate only on its reached shapes. The
tag, carried on the value stack by the selector, has been consumed. -/
def branchRuns {a W : ℕ} (g : Fin (a+1) × Fin (a+1)) (P : Shape → Prop)
    (T S : Shape → ℕ) (c : Cmd) : Prop :=
  ClosedRuns c (fun t : {t : XorInput W // P t.shape} => T t.val.shape)
    (fun t => S t.val.shape) (fun t => send (Header.wire (a+1) t.val.shape,laneFlat (a+1) W t.val.shape t.val.row))
    (fun t => send (laneFlat (a+1) W t.val.shape (xor a g t.val.shape t.val.row)))

/-- The test may compute its reserve from the current descriptor. -/
def SelectorRuns (a : ℕ) (D : Shape → ℕ) (e : ℕ) (tag : Cmd) : Prop :=
  ∀ W d, e ≤ d →
    let v := fun t : XorInput W => allowance (a+1) d t.shape
    let packet := fun t : XorInput W => send (Header.wire (a+1) t.shape, laneFlat (a+1) W t.shape t.row)
    ClosedRuns tag v v packet (fun t => .fork (.atom (decide (fitsReserve a (D t.shape) t.shape))) (packet t))

/-- The clock switches between the two exact branch costs at the live reserve. -/
noncomputable def branchClock (a W : ℕ) (ρ : ℝ) (D : Shape → ℕ) (s : Shape) :=
  FrontClock.extra (a+1) W ρ (D s) s

/-- A single control program handles either a literal reserve or one computed
from the current shape. -/
theorem compileGateAt {Z : Type} [Primcodable Z] (a : Z → ℕ) (D : Z → Shape → ℕ)
    (tag : Z → Cmd) (K e : ℕ) (testCode : Effective ltr tag) (rt : ∀ z, Within K (tag z))
    (runTag : ∀ z, SelectorRuns (a z) (D z) e (tag z))
    (small large : Z → Cmd) (es : Effective ltr small) (el : Effective ltr large) (R : ℕ)
    (regS : ∀ z, Within R (small z)) (regL : ∀ z, Within R (large z)) :
    let emit := fun z => (tag z).join (decodeBit (small z) (large z))
    ∃ N : ℕ, Effective ltr emit ∧ 0 < N ∧ (∀ z, Within N (emit z)) ∧
      ∀ (z : Z) (W : ℕ) (ρ : ℝ) (arity : 4 ≤ a z) (d : ℕ), e ≤ d →
        let A := a z+1
        let g := Interior.axes (a z) arity
        branchRuns (W:=W) g (fun s => ¬ fitsReserve (a z) (D z s) s)
          (nodeScan (a z) W d (ElementarySweep.extra A)) (nodeArena (a z) W d) (small z) →
        branchRuns (W:=W) g (fun s => fitsReserve (a z) (D z s) s)
          (fun s => allowance A d s + Interior.extra (a z) W ρ s) (allowance A d) (large z) →
        PhysicalWalshCompileXorPacket.FlatRuns (W:=W)
          (nodeScan (a z) W d (branchClock (a z) W ρ (D z))) (nodeArena (a z) W d) g (emit z) := by
  intro cmd
  let N := max R K + 1
  have pN : 0 < N := Nat.succ_pos _
  have leR : R ≤ N := (le_max_left ..).trans (Nat.le_succ _)
  have leK : K ≤ N := (le_max_right ..).trans (Nat.le_succ _)
  refine ⟨N,testCode.join (choose_effective es el),pN,fun z =>
    ⟨RegisterSelect.within_mono leK _ (rt _),
      choose_within pN (RegisterSelect.within_mono leR _ (regS z)) (RegisterSelect.within_mono leR _ (regL z))⟩,?_⟩
  intro z W ρ arity d de
  dsimp only
  intro hs hl
  let A := a z+1
  let g := Interior.axes (a z) arity
  let P (x : XorInput W) := fitsReserve (a z) (D z x.shape) x.shape
  let T (x : XorInput W) := nodeScan (a z) W d (branchClock (a z) W ρ (D z)) x.shape
  let S (x : XorInput W) := nodeArena (a z) W d x.shape
  let q (x : XorInput W) := send (Header.wire A x.shape,laneFlat A W x.shape x.row)
  let r (x : XorInput W) := send (laneFlat A W x.shape (PhysicalWalshNode.xor (a z) g x.shape x.row))
  have srun : ClosedRuns (small z) (T ∘ Subtype.val) (S ∘ Subtype.val)
      (fun t : {x // ¬ P x} => q t.val) (r ∘ Subtype.val) := by
    apply hs.mono _ (fun _ => le_rfl)
    intro t
    have lo : ElementarySchedule.slotWidth A t.val.shape < XorThreshold.cutoff (D z t.val.shape) (Header.scale A t.val.shape) :=
      Nat.lt_of_not_ge t.property
    simp only [T,Function.comp_apply,nodeScan,branchClock,FrontClock.extra,ite_eq_left lo,A,le_refl]
  have lrun : ClosedRuns (large z) (T ∘ Subtype.val) (S ∘ Subtype.val)
      (fun t : {x // P x} => q t.val) (r ∘ Subtype.val) := by
    apply hl.mono _ (fun _ => le_max_left ..)
    intro t
    have hi : ¬ ElementarySchedule.slotWidth A t.val.shape < XorThreshold.cutoff (D z t.val.shape) (Header.scale A t.val.shape) :=
      Nat.not_lt.mpr t.property
    change allowance _ _ _ + Interior.extra _ _ _ _ ≤ nodeArena _ _ _ _ + FrontClock.extra A W ρ (D z t.val.shape) _
    rw [FrontClock.extra,ite_eq_right hi]
    exact Nat.add_le_add_right (le_max_left ..) _
  have tagRun : ClosedRuns (tag z) T S q (fun x => .fork (.atom (decide (P x))) (q x)) :=
    (runTag z W d de).mono (fun _ => (le_max_left ..).trans (Nat.le_add_right ..)) (fun _ => le_max_left ..)
  exact EffectiveBoundedTask.Runs.sequence tagRun (chooseNamed P srun lrun)

/-- A single control program handles either a literal reserve or one computed
from the current shape. -/
theorem compileGateWith {Z : Type} [Primcodable Z] (a : Z → ℕ) (D : Z → Shape → ℕ)
    (tag : Z → Cmd) (K e : ℕ) (testCode : Effective ltr tag) (rt : ∀ z, Within K (tag z))
    (runTag : ∀ z, SelectorRuns (a z) (D z) e (tag z))
    (small large : Z → Cmd) (es : Effective ltr small) (el : Effective ltr large) (R : ℕ)
    (regS : ∀ z, Within R (small z)) (regL : ∀ z, Within R (large z)) :
    ∃ (emit : Z → Cmd) (N : ℕ), Effective ltr emit ∧ 0 < N ∧ (∀ z, Within N (emit z)) ∧
      ∀ (z : Z) (W : ℕ) (ρ : ℝ) (arity : 4 ≤ a z) (d : ℕ), e ≤ d →
        let A := a z+1
        let g := Interior.axes (a z) arity
        branchRuns (W:=W) g (fun s => ¬ fitsReserve (a z) (D z s) s)
          (nodeScan (a z) W d (ElementarySweep.extra A)) (nodeArena (a z) W d) (small z) →
        branchRuns (W:=W) g (fun s => fitsReserve (a z) (D z s) s)
          (fun s => allowance A d s + Interior.extra (a z) W ρ s) (allowance A d) (large z) →
        PhysicalWalshCompileXorPacket.FlatRuns (W:=W)
          (nodeScan (a z) W d (branchClock (a z) W ρ (D z))) (nodeArena (a z) W d) g (emit z) := by
  obtain ⟨N,ee,pN,reg,run⟩ := compileGateAt a D tag K e testCode rt runTag small large es el R regS regL
  exact ⟨_,N,ee,pN,reg,run⟩

/-- Any common parameter, including a table reservation, may specialize the
two emitted gates. The checked file includes the actual threshold test and
the reached branch, and has a single register cutoff and selector degree. -/
theorem compileGate {Z : Type} [Primcodable Z] (a D : Z → ℕ) (ha : Computable a) (hD : Computable D)
    (small large : Z → Cmd) (es : Effective ltr small) (el : Effective ltr large) (R : ℕ)
    (regS : ∀ z, Within R (small z)) (regL : ∀ z, Within R (large z)) :
    ∃ (emit : Z → Cmd) (N e : ℕ), Effective ltr emit ∧ 0 < N ∧ (∀ z, Within N (emit z)) ∧
      ∀ (z : Z) (W : ℕ) (ρ : ℝ) (arity : 4 ≤ a z) (d : ℕ), e ≤ d →
        let A := a z+1
        let g := Interior.axes (a z) arity
        branchRuns (W:=W) g (fun s => ¬ fitsReserve (a z) (D z) s)
          (nodeScan (a z) W d (ElementarySweep.extra A)) (nodeArena (a z) W d) (small z) →
        branchRuns (W:=W) g (fitsReserve (a z) (D z))
          (fun s => allowance A d s + Interior.extra (a z) W ρ s) (allowance A d) (large z) →
        PhysicalWalshCompileXorPacket.FlatRuns (W:=W)
          (nodeScan (a z) W d (FrontClock.extra A W ρ (D z))) (nodeArena (a z) W d) g (emit z) := by
  obtain ⟨tag,K,e,et,rt,ht⟩ := compileSelector
  obtain ⟨emit,N,ee,pN,reg,run⟩ := compileGateWith a (fun z _ => D z) (fun z => tag (a z,D z)) K e
    (et.comp (ha.pair hD)) (fun z => rt _) (fun z W d => ht (a z) W (D z) d) small large es el R regS regL
  exact ⟨emit,N,e,ee,pN,reg,run⟩


end PhysicalWalshNode.FrontDispatch

end NearSquareRoot
end Computability
end OAI
