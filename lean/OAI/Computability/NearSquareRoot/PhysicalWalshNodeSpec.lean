import OAI.Computability.NearSquareRoot.PhysicalWalshNodeGuard
import OAI.Computability.NearSquareRoot.PhysicalWalshNodeHeader
import OAI.Computability.NearSquareRoot.PhysicalWalshDriver
import OAI.Computability.NearSquareRoot.PhysicalWalshCharges

/-! # A concrete recursive invocation on a flat stream of grid records

The semantic index carries divisibility and accumulator range proofs. The
machine sees only the compact descriptor and the list of marked complex grid
records. Its output is the recursively evaluated transform in the same order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication Code Space KernelPass PhysicalWalsh

variable {a W : ℕ} (hw : 0 < W) (p : Plan (a+1) W W)

/-- Ascending physical address order, with both components of each signed record. -/
def flat (A : ℕ) (s : Shape) (x : Data s) := (List.range (count A s)).map (Dusk.mark ∘ x)

/-- Encoded node packet received and returned by the linked recursive program. -/
def buffer (A : ℕ) (s : Shape) (x : Data s) := send (Header.wire A s, flat A s x)

/-- Unary layout scans charge actual record volume; descriptor-only arithmetic
is polynomial in the compact input size. -/
def allowance (A d : ℕ) (s : Shape) : ℕ :=
  (count A s+1)*(grow A s.level+s.w+1) + (Header.scale A s+1)^d

theorem allowance_mono {A d e : ℕ} (h : d ≤ e) (s : Shape) : allowance A d s ≤ allowance A e s :=
  Nat.add_le_add_left (Nat.pow_le_pow_right (by omega) h) _

/-- A well-framed, numerically representable single-row input to one piece. -/
structure Invocation where
  shape : Shape
  row : Data shape
  batches : W^shape.level ∣ shape.pref
  representable : Good hw p shape row

/-- A child keeps its record width, transforms exactly one shorter slot, and
has one whole parent lane as its input. -/
def childShape (A W : ℕ) (s v : Shape) : Prop :=
  0 < s.level ∧ W^s.level ∣ s.pref ∧ ∃ i : Fin A, v = descend A W i s

/-- The dispatch tag and both stack boundaries are specified by a concrete
recursive transform of actual input records. -/
def spec (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s) : RecSpec (Invocation hw p) Shape where
  world := Invocation.shape
  level := Shape.level
  child := childShape (a+1) W
  decreases := by rintro s v ⟨hs,_,i,rfl⟩; change s.level-1<s.level; omega
  payload i := buffer (a+1) i.shape i.row
  reply i := buffer (a+1) i.shape (run hw p i.shape i.row)
  scan := scan
  arena := arena
  arena_le := cost

/-- A recursive child request made from one reached valid lane. -/
def childInvocation (v : Invocation hw p) (positive : 0 < v.shape.level) (i : Fin (a+1))
    (r : Data v.shape) (good : Good hw p (descend (a+1) W i v.shape) r) : Invocation hw p :=
  ⟨descend (a+1) W i v.shape, r, child_divisible v.shape i positive v.batches, good⟩

/-- The full bit volume of a node. All descendants keep the same outer
record-width key; their exact number of records falls by `W`. -/
noncomputable def chargeLayout (scan arena : Shape → ℕ) (cost : ∀ s, arena s ≤ scan s) :
    ChargeLayout (spec hw p scan arena cost) W ℕ where
  key := Shape.w
  volume s := (count (a+1) s : ℝ) * (s.w+1)
  nonnegative _ := by positivity
  childKey := by rintro s v ⟨_,_,i,rfl⟩; rfl
  childLevel := by rintro s v ⟨h,_,i,rfl⟩; change s.level-1+1 = s.level; omega
  childVolume := by
    rintro s v ⟨h,hd,i,rfl⟩
    have eq := volume_split s i h hd
    have eq' : (W:ℝ)*count (a+1) (descend (a+1) W i s) = count (a+1) s := by exact_mod_cast eq
    change (count (a+1) (descend (a+1) W i s) : ℝ)*(s.w+1) ≤ _
    apply (le_div_iff₀ (show (0:ℝ)<W by exact_mod_cast hw)).mpr
    rw [← eq']; ring_nf; rfl

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
