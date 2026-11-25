import OAI.Computability.NearSquareRoot.CRTControlledEffectiveHighRow
import OAI.Computability.NearSquareRoot.PhysicalWalshXorRowEnds

/-! # Reading adopted full-array addresses in the named high-row packet

The inner physical program reads low positions in least-significant-bit
order. Converting those bits back to their native row block lets the same
row evaluator act on any order-preserving adopted view of the full array.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.MaskRowCommand

open IntegerMultiplication Code Adic Strip Loom NamedPacked PhysicalWalsh.XorWindow
open Controlled.PositionProgram
open private store_cart from OAI.Computability.NearSquareRoot.PhysicalWalshXorRowEnds

variable {P n k : ℕ} {U : Type}

/-- Interpret a low Boolean coordinate and a high native block at the
corresponding address in the original unpartitioned series. -/
noncomputable def rowInput (join : Adopt ((line 2 P).cart (line 2 n)) (line 2 k))
    (f : Block 2 k → U → Bead) : Input P n U :=
  fun bits high => f (join.cast (high,(nativeWord n).symm bits))

@[simp] theorem rowInput_lookup (join : Adopt ((line 2 P).cart (line 2 n)) (line 2 k))
    (f : Block 2 k → U → Bead) (hi : Block 2 P) (lo : Block 2 n) :
    rowInput join f (prefixBit lo) hi = f (join.cast (hi,lo)) := by
  unfold rowInput
  rw [← nativeWord_apply,Equiv.symm_apply_apply]

theorem store_input (u : Series U) (join : Adopt ((line 2 P).cart (line 2 n)) (line 2 k))
    (f : Block 2 k → U → Bead) :
    store u (rowInput join f) = stripe (line 2 k) (fun a => strip u (f a)) := by
  rw [←store_cart, join.packet]
  apply congrArg (stripe _)
  funext a
  simp only [rowInput_lookup,Prod.mk.eta,Function.comp_apply]

variable {X : Type} (r : Regime X) (P n k : X → ℕ) (hp : r.Has (tally ∘ P))
  {U : X → Type} (u : (x : X) → Series (U x))
  (join : (x : X) → Adopt ((line 2 (P x)).cart (line 2 (n x))) (line 2 (k x)))
  (f : (x : X) → Block 2 (k x) → U x → Bead)

theorem before_input (x : X) :
    beforeRows r P n hp u (fun x => rowInput (join x) (f x)) x =
      stripe (line 2 (P x)) (fun a => .fork ((fixedRowRegime r P hp).header ⟨x,a⟩)
        (stripe (line 2 (n x)) (fun b => strip (u x) (f x ((join x).cast (a,b)))))) := by
  simp only [beforeRows,rowInput_lookup]

theorem after_input (x : X) :
    afterRows P n u (fun x => rowInput (join x) (f x)) x =
      stripe (line 2 (P x)) (fun a => stripe (line 2 (n x)) (fun b => strip (u x) (f x ((join x).cast (a,b))))) := by
  simp only [afterRows,rowInput_lookup]

end Controlled.MaskRowCommand

end NearSquareRoot
end Computability
end OAI
