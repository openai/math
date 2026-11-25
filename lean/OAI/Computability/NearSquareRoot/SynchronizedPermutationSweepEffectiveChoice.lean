import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepExecute
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveConjugate

/-! # Literal position tables and control vectors for the emitted Fourier batch -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes.PackedBatchHeader.PassPoint
open IntegerMultiplication Code Adic Strip Loom FixedPoint Controlled
open Controlled.PermutationLayout Space PositionProgram

noncomputable section

abbrev nativeWidth (p : PassPoint) := maskWidth p.high p.count (guardWidth p.k) p.suffix

/-- Actual emitted tables determine all representations up to the equality of
their induced action on the natural addresses. -/
structure Placement (p : PassPoint) where
  width : p.nativeWidth = p.k
  route : Equiv.Perm (Fin p.nativeWidth)
  flag : Block 2 p.high → Fin p.count → Bool
  tables : p.descriptor.2.1 = (Reflections.table route,Reflections.table route.symm)
  vector : ∀ z : Block 2 p.high, maskBits (p.descriptor.2,List.ofFn (Controlled.prefixBit z)) = List.ofFn (flag z)
  address : ∀ a, p.rank (castWord width (naturalStage route flag a)) =
    p.network.symm (p.rank (castWord width a))

/-- All data accessed by the native machine comes from the literal header.
This choice packages correctness witnesses for its physically read tables. -/
def placement (p : PassPoint) : Placement p := Classical.choice (show Nonempty (Placement p) from by
  let _ := BoxFin.modulus_neZero p.budget.valid
  obtain ⟨e,π,ctrl,mat,flags,_,pull,_⟩ := RealizesBatch.pull p.budget.valid p.long p.realizes
  exact ⟨⟨e,π,ctrl,mat,flags,fun a => pull (id : PackedAddress Unit p.fields → _) a⟩⟩)

theorem placementHas {X : Type} (point : X → PassPoint) :
    ((regime point).Has fun x => Reflections.table (point x).placement.route) ∧
    ((regime point).Has fun x => Reflections.table (point x).placement.route.symm) :=
  relocationTables (fun x => (point x).placement.route) (fun x => (point x).descriptor) (available point)
    (fun key => key.2.1) (Easy.snd.compose Easy.fst) (fun x => (point x).placement.tables)

theorem flagHas {X : Type} (point : X → PassPoint)
    (high : (regime point).Has fun x => tally (point x).high) :
    (fixedRowRegime (regime point) (fun x => (point x).high) high).Has
      (fun z => List.ofFn ((point z.1).placement.flag z.2)) := by
  have ready : (regime point).Has (fun x => (point x).descriptor.2) :=
    (available point).ez (show Easy (fun key : PlacedHeader => key.2) from Easy.snd)
  let rr := fixedRowRegime (regime point) (fun x => (point x).high) high
  have h := maskBits_has (fun x => (point x).high) high (fun x => (point x).descriptor.2) ready
  apply (congrArg (fun f => rr.Has f) (funext fun z => (point z.1).placement.vector z.2)).mp h

def nativePayload (s : Input) (a : Block 2 s.1.nativeWidth) :=
  Dusk.stock (s.2 (s.1.rank (castWord s.1.placement.width a)))

def charts (s : Input) := line 2 s.1.nativeWidth
def grain (s : Input) := Series.natural (2*(componentBits s.1.k+1))

def placedPayload (s : Input) (a : Block 2 s.1.nativeWidth) :=
  nativePayload s ((permuteNative s.1.placement.route).symm a)

def switchedPayload (s : Input) (a : Block 2 s.1.nativeWidth) :=
  placedPayload s (flatMask (H := guardWidth s.1.k-1) s.1.high 0 s.1.suffix s.1.placement.flag a)

private theorem stripe_width {a k : ℕ} (e : a = k) {U : Type} (u : Series U) (f : Block 2 k → U → Bead) :
    stripe (line 2 a) (fun z => strip u (f (castWord e z))) = stripe (line 2 k) (fun z => strip u (f z)) := by
  subst k
  rfl

theorem initialBeads (s : Input) : cloth charts grain nativePayload s = beads s :=
  stripe_width s.1.placement.width (grain s) (fun a => Dusk.stock (s.2 (s.1.rank a)))

theorem finalBeads (s : Input) :
    cloth charts grain (fun s a => nativePayload s (naturalStage s.1.placement.route s.1.placement.flag a)) s =
      beads (move s) := by
  refine Eq.trans ?_ (stripe_width s.1.placement.width (grain s)
    (fun a => Dusk.stock (s.2 (s.1.network.symm (s.1.rank a)))))
  apply congrArg (stripe _)
  funext a
  exact congrArg (fun addr => strip (grain s) (Dusk.stock (s.2 addr))) (s.1.placement.address a)

end
end Benes.PackedBatchHeader.PassPoint

end NearSquareRoot
end Computability
end OAI
