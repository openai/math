import OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorRoute
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorNative
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorHeaderRaw
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # Reusing a compact descriptor when the interior pass changes row length -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileXorRoute

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode PhysicalWalshCompile
open private Scans.atInput from OAI.Computability.NearSquareRoot.PhysicalWalshCompileSound
open private meter finish from OAI.Computability.NearSquareRoot.PhysicalWalshCompileXorRoute

/-- Keep a compact descriptor on the stack across an arbitrary named row
pass. The next pass may crop or extend the row. The three finite coefficients
bound the live descriptor, the initial row, and the intermediate row. -/
theorem Legal.rows_chain {K : Kit} {R : ℕ} (hk : Legal K R) {I : Type} (u : I → Shape)
    (T V : Shape → ℕ) (cost : ∀ s, V s ≤ T s)
    (h : I → Header.Wire) (x y z : I → List Dusk.Pair) {c d : Cmd}
    (first : ClosedRuns c (T ∘ u) (V ∘ u) (fun i => send (h i,x i)) (fun i => send (y i)))
    (second : ClosedRuns d (T ∘ u) (V ∘ u) (fun i => send (h i,y i)) (fun i => send (z i)))
    (Ch Cx Cy : ℕ) (bh : ∀ i, size (h i) ≤ Ch*(V (u i)+1))
    (bx : ∀ i, size (x i) ≤ Cx*(V (u i)+1)) (by_ : ∀ i, size (y i) ≤ Cy*(V (u i)+1)) :
    ClosedRuns (K.chain c d) (T ∘ u) (V ∘ u) (fun i => send (h i,x i)) (fun i => send (z i)) := by
  let m := meter cost
  have before := Scans.atInput (m:=m) (u:=u) hk.saves (fun i => (h i,x i)) (Ch+Cx+1)
    (fun i => by rw [size_prod]; dsimp only; have := bh i; have := bx i
                 change _ ≤ (Ch+Cx+1)*(V (u i)+1); simp only [Nat.add_mul,Nat.one_mul]; omega)
  have run1 : Runs c m 0 u (fun i => send (h i,x i)) (fun i => send (y i)) := Runs.closed first
  have keep := run1.left (fun i => send (h i)) Ch bh
  have middle := Scans.atInput (m:=m) (u:=u) hk.swaps (fun i => (y i,h i)) (Cy+Ch+1)
    (fun i => by rw [size_prod]; dsimp only; have := by_ i; have := bh i
                 change _ ≤ (Cy+Ch+1)*(V (u i)+1); simp only [Nat.add_mul,Nat.one_mul]; omega)
  have run2 : Runs d m 0 u (fun i => send (h i,y i)) (fun i => send (z i)) := Runs.closed second
  exact finish (((before.seq keep).seq middle).seq run2)

end PhysicalWalshCompileXorRoute

namespace PhysicalWalshCompileInterior

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode Interior SwapPrefix
open PhysicalWalshCompileXorRoute CommonRegisters GeneratorSyntax KernelPass.ComputableSyntax

/-- The real lane before padding and the cropped XOR result after the
canonical gate, at separate bounds for native time and all live rows. -/
def LargeOn (ρ : ℝ) (pred : PhysicalWalshNode.Shape → Prop) (d a W : ℕ) (ha : 4 ≤ a) (c : Cmd) : Prop :=
  let s (u : {t : XorInput W // pred t.shape}) := u.val.shape
  let V := allowance (a+1) d
  ClosedRuns c (fun u => V (s u)+extra a W ρ (s u)) (V ∘ s)
    (fun u => send (Header.wire (a+1) (s u),laneFlat (a+1) W (s u) u.val.row))
    (fun u => send (laneFlat (a+1) W (s u) (PhysicalWalshNode.xor a (axes a ha) (s u) u.val.row)))

/-- A large-node trace for a fixed polynomial table degree. -/
abbrev LargeRun (ρ : ℝ) (D d a W : ℕ) (ha : 4 ≤ a) (c : Cmd) : Prop :=
  LargeOn ρ (fun s => XorThreshold.cutoff D (Header.scale (a+1) s) ≤ L (a+1) s) d a W ha c

/-- Width and arity are both computed from the public finite template. -/
def dimensions (r : Raw) := (r.1, ((KernelPass.ComputableSyntax.Shape.algebra r.1).parse r.2).1.1)

theorem computable_dimensions : Computable dimensions :=
  Computable.fst.pair ((Computable.fst.comp Computable.fst).comp
    (KernelPass.ComputableSyntax.Shape.primrec_algebra.to_comp.comp Computable.fst Computable.snd))

theorem dimensions_eq (a W : ℕ) (ops : List Op) (hi : (Packed.decode (a+1) ops).i = W) :
    dimensions (a+1,ops) = (a+1,W) := by
  unfold dimensions
  rw [←Packed.decode_shape]
  exact congrArg (fun j => (a+1,j)) hi

/-- Wrap the padding, native rulers, native permutation, and final crop.
Each stage acts on the physical row passed by the previous stage. -/
theorem large_frame_on {K : Kit} {R : ℕ} (hk : Legal K R) {ρ : ℝ} {a W d : ℕ} {pred : PhysicalWalshNode.Shape → Prop}
    (ha : 4 ≤ a) (hd : 1 ≤ d) {pad head native crop : Cmd}
    (nativeRun : NativeOn a W ρ pred native)
    (padRun : let s (i : {t : XorInput W // pred t.shape}) := i.val.shape
      let V := allowance (a+1) d ∘ s
      ClosedRuns pad V V
        (fun i => send (Header.wire (a+1) (s i),laneFlat (a+1) W (s i) i.val.row))
        (fun i => send (Header.wire (a+1) (s i),padded (a:=a) i.val)))
    (headRun : let s (i : {t : XorInput W // pred t.shape}) := i.val.shape
      let V := allowance (a+1) d ∘ s
      ClosedRuns head V V
        (fun i => send (Header.wire (a+1) (s i),padded (a:=a) i.val))
        (fun i => .fork (rawHeader a W (s i)) (send (padded (a:=a) i.val))))
    (cropRun : let s (i : {t : XorInput W // pred t.shape}) := i.val.shape
      let V := allowance (a+1) d ∘ s
      ClosedRuns crop V V
        (fun i => send (Header.wire (a+1) (s i),stream (paddedSize (a+1) W (s i)) (moved (a:=a) i.val)))
        (fun i => send (laneFlat (a+1) W (s i) (moved (a:=a) i.val)))) :
    LargeOn ρ pred d a W ha (pad.join (K.chain (head.join native) crop)) := by
  let u (j : {t : XorInput W // pred t.shape}) := j.val.shape
  let V := allowance (a+1) d
  let T s := V s + extra a W ρ s
  let h i := Header.wire (a+1) (u i)
  let x (i : {t : XorInput W // pred t.shape}) := padded (a:=a) i.val
  let y (i : {t : XorInput W // pred t.shape}) := stream (paddedSize (a+1) W (u i)) (moved (a:=a) i.val)
  let z (i : {t : XorInput W // pred t.shape}) := laneFlat (a+1) W (u i) (moved (a:=a) i.val)
  have ss (i : {t : XorInput W // pred t.shape}) : V (u i) ≤ T (u i) := Nat.le_add_right ..
  have first : ClosedRuns head (T ∘ u) (V ∘ u) (fun i => send (h i,x i))
      (fun i => .fork (rawHeader a W (u i)) (send (x i))) :=
    headRun.mono ss (fun _ => le_rfl)
  have body : EffectiveBoundedTask.Runs native (T ∘ u) (V ∘ u)
      (fun i => .fork (rawHeader a W (u i)) (send (x i))) (fun i => send (y i)) := by
    apply EffectiveBoundedTask.Runs.bound (show EffectiveBoundedTask.Runs native _ _ _ _ from nativeRun) 1 4
    · intro i; change extra a W ρ (u i)+1 ≤ 1*(V (u i)+extra a W ρ (u i)+1); omega
    · intro i; change volume a W (u i)+1 ≤ 4*(V (u i)+1)
      have hv := volume_bound a W d (u i)
      change volume a W (u i) ≤ 4*V (u i) at hv
      omega
  have two := EffectiveBoundedTask.Runs.sequence first body
  have next := cropRun.mono ss (fun _ => le_rfl)
  have linked := hk.rows_chain u T V (fun s => Nat.le_add_right ..) h x y z two next 1 17 17
    (fun i => by
      change Header.scale (a+1) (u i) ≤ 1*(V (u i)+1)
      have e := Nat.pow_le_pow_right (n:=Header.scale (a+1) (u i)+1) (by omega) hd
      rw [pow_one] at e
      have q : (Header.scale (a+1) (u i)+1)^d ≤ V (u i) := Nat.le_add_left ..
      omega)
    (fun i => (stream_cost (a+1) W d (u i) _ (extend (a+1) W (u i) i.val.row) le_rfl).trans (by dsimp only [V]; omega))
    (fun i => (stream_cost (a+1) W d (u i) _ (moved (a:=a) i.val) le_rfl).trans (by dsimp only [V]; omega))
  have assembled := EffectiveBoundedTask.Runs.sequence (padRun.mono ss (fun _ => le_rfl)) linked
  change ClosedRuns _ (T ∘ u) (V ∘ u) _ _
  have eqn (i : {t : XorInput W // pred t.shape}) : z i = laneFlat (a+1) W (u i) (PhysicalWalshNode.xor a (axes a ha) (u i) i.val.row) :=
    actual_output a W ha (u i) i.val.positive i.val.row
  change ClosedRuns _ (T ∘ u) (V ∘ u) _ (fun i => send (z i)) at assembled
  rw [show (fun i => send (z i)) = (fun i => send (laneFlat (a+1) W (u i)
    (PhysicalWalshNode.xor a (axes a ha) (u i) i.val.row))) from funext fun i => congrArg send (eqn i)] at assembled
  exact assembled

end PhysicalWalshCompileInterior

end NearSquareRoot
end Computability
end OAI
