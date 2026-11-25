import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineNative
import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineNativeRows
import OAI.Computability.NearSquareRoot.InterchangeROMAddressBank

/-! # The affine address tests produce the physical masks of each opcode -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace AffineAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry
  IntegerMultiplication.Bits IntegerMultiplication.Strip IntegerMultiplication.Adic
  IntegerMultiplication.Port IntegerMultiplication.Loom IntegerMultiplication.Strip.Dims
open InterchangeROMAddress InterchangeAffineMask

variable {J : Type} [DecidableEq J] {n b f : ℕ} [NeZero b]
    (ord : J ≃ Fin n) (P G S : Tape) (hp : solid P) (hg : solid G) (hs : solid S)
    (hb : 2 ≤ b)

noncomputable def nativeFaces (x y : Spot J) (A B : Row ℕ) (k : Class ℕ) :
    Comparison × Comparison :=
  (comparison (f:=f) ord P G S hp hg hs hb x y (literal (b^f) A B k),
    comparison (f:=f) ord P G S hp hg hs hb x y (literal (b^f) B A k.swap))

theorem nativeFaces_masks (x y : Spot J) (A B : Row ℕ) (k : Class ℕ) :
    pairMasks Comparison.result (nativeFaces (f:=f) ord P G S hp hg hs hb x y A B k) =
    send (maskRows (arrays ord (line b f) P G S) (b^f) A B k
      (fun z => born (number (ask z x))) (fun z => born (number (ask z y)))) := by
  simp only [nativeFaces,pairMasks,answer,stripe_eq',maskRows,send_prod]

/-- The signed width starts with its optional mirror; `v` is the stream
presented to the positive carry-lane pass after that mirror. -/
noncomputable def widthBank (x : Spot J) (a : Span b) (v : Keys P G S J (Block b f) → Tree) :
    BankInput Comparison Comparison.result where
  rows := slotRows (oneStop ord x) a v
  faces := fun k => let w := widthRows a.neg a.top.count a.down.count
    nativeFaces ord P G S hp hg hs hb x x w.1 w.2 k (f:=f)
  correct k _ := by
    change pairMasks _ (nativeFaces (f:=f) ord P G S hp hg hs hb x x _ _ k) = _
    rw [nativeFaces_masks,slotRows_masks]
    have read : (oneStop (p:=b) (j:=f) (P:=P) (G:=G) (B:=S) ord x).read =
        fun z => ask z x := funext fun z => (one_use ord x z (ask z x)).1
    rw [read]

/-- Both faces of every shear color use the earlier and later coordinates
of the actual native view in physical order. -/
noncomputable def gatherBank (x y : Spot J) (early : Lag.early (ranking ord) x y) (a : Pinpoint b)
    (v : Keys P G S J (Block b f) → Tree) : BankInput Comparison Comparison.result where
  rows := axisRows (twoStops ord x y early) a v
  faces := fun k => nativeFaces (f:=f) ord P G S hp hg hs hb x y (pinRows a).1 (pinRows a).2 k
  correct k _ := by
    rw [nativeFaces_masks,axisRows_masks]
    have xy : (twoStops (p:=b) (j:=f) (P:=P) (G:=G) (B:=S) ord x y early).pair =
        fun z => (ask z x,ask z y) := funext fun z => (two_use ord x y early z (ask z x) (ask z y)).1
    rw [xy]

end AffineAddress

end NearSquareRoot
end Computability
end OAI
