import OAI.Optimization.LinearProgramming.Recovery.SupportContextFrame
import OAI.Optimization.LinearProgramming.Recovery.MaskedInput
import OAI.Optimization.LinearProgramming.Recovery.DenseEncoding
import OAI.Optimization.LinearProgramming.RAM.CallableRawTapes
import Mathlib.Tactic.IntervalCases

/-! The opposite equation basis and the live support flags form the ordinary input tape
for a masked-subspace test or the final witness solve over the same scalar field. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace SupportBundle

open RAM RAM.Callable Geometry Matrix SupportRAM

variable {h n : ℕ}

structure Context {K : Type} (E : Matrix (Fin h) (Fin n) K) (side : Bool) (src cap : ℕ) (m : Memory K) : Prop where
  scalarBase : m.index 55=src
  length : m.index 56=h*n+n
  dimBase : m.index 57=512
  dimLength : m.index 58=2
  capacity : m.index 60=cap
  height : m.index 512=h
  width : m.index 513=n
  sideBit : m.index 156=side.toNat
  marked : m.index 150=n
  flags : m.index 151=src+h*n
  basis : uniformRect h n src m=E

private theorem offset_lt (a : Fin h) (b : Fin n) : a.val*n+b.val < h*n := by
  have mul:=Nat.mul_le_mul_right n (Nat.succ_le_of_lt a.isLt)
  rw [Nat.succ_mul] at mul;omega

theorem Context.stable {K : Type} (E : Matrix (Fin h) (Fin n) K) (side : Bool) (src cap : ℕ) (hi : 256 ≤ src) :
    StableContext (src+h*n) n (Context E side src cap) := by
  intro a b ctx eq
  refine ⟨(eq.index 55 (by decide) (by decide) (by decide) (by decide)).trans ctx.scalarBase,
    (eq.index 56 (by decide) (by decide) (by decide) (by decide)).trans ctx.length,
    (eq.index 57 (by decide) (by decide) (by decide) (by decide)).trans ctx.dimBase,
    (eq.index 58 (by decide) (by decide) (by decide) (by decide)).trans ctx.dimLength,
    (eq.index 60 (by decide) (by decide) (by decide) (by decide)).trans ctx.capacity,
    (eq.index 512 (by decide) (by decide) (by decide) (by decide)).trans ctx.height,
    (eq.index 513 (by decide) (by decide) (by decide) (by decide)).trans ctx.width,
    (eq.index 156 (by decide) (by decide) (by decide) (by decide)).trans ctx.sideBit,
    (eq.index 150 (by decide) (by decide) (by decide) (by decide)).trans ctx.marked,
    (eq.index 151 (by decide) (by decide) (by decide) (by decide)).trans ctx.flags,?_⟩
  ext i j
  change b.data (src+i.val*n+j.val)=E i j
  have ofs:=offset_lt i j
  exact (eq.data _ (by omega) (by omega) (Or.inl (by omega))).trans (congrFun (congrFun ctx.basis i) j)

theorem Context.raw {K : Type} [Zero K] [One K] {E : Matrix (Fin h) (Fin n) K}
    {side : Bool} {src cap step : ℕ} {m : Memory K} {S : Finset (Fin n)}
    (c : Context E side src cap m) (state : Layout m (src+h*n) step S) :
    RawTapes m src 512 cap (MaskedInput.bundle E S) [h,n] := by
  refine ⟨c.scalarBase,by simpa [MaskedInput.bundle] using c.length,c.dimBase,c.dimLength,c.capacity,?_,?_⟩
  · intro j hj
    by_cases first : j < (encodedGramInput E).length
    · simpa only [MaskedInput.bundle,List.getElem_append_left first] using PairBuilder.dense_encoded m E c.basis j first
    · have reach : j < h*n+n:=by simpa [MaskedInput.bundle] using hj
      have after : h*n ≤ j:=by simpa using Nat.le_of_not_lt first
      let i : Fin n:=⟨j-h*n,by omega⟩
      have addr : src+j=src+h*n+i.val:=by dsimp [i];omega
      have flagAt:=state.2.2.2.2 i
      rw [addr,flagAt]
      simp only [MaskedInput.bundle,List.getElem_append_right (Nat.le_of_not_lt first),List.getElem_ofFn,length_encodedGramInput]
      rfl
  · intro j hj
    have small : j < 2:=by simpa using hj
    interval_cases j <;> first | exact c.height | exact c.width

end SupportBundle
end Recovery
end LinearProgramming
end Optimization
end OAI
