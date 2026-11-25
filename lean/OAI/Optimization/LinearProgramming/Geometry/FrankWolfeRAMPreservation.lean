import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeRAMBits
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeRAMIndexFrame

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace FWRAM

open RAM Matrix
open scoped Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

omit [LinearOrder K] [IsStrictOrderedRing K] in
theorem GradientSafe.mono {P R : K → Prop} {Q : Matrix (Fin n) (Fin n) K} {z : Fin n → K}
    (h : GradientSafe P Q z) (f : ∀ x, P x → R x) : GradientSafe R Q z :=
  ⟨fun r j => f _ (h.term r j), fun r p hp => f _ (h.prefix r p hp)⟩

omit [IsStrictOrderedRing K] in
theorem RoundSafe.mono {P R : K → Prop} {Q : Matrix (Fin n) (Fin n) K} {i : Fin n} {p : ℕ}
    (h : RoundSafe P Q i p) (f : ∀ x, P x → R x) : RoundSafe R Q i p := by
  refine ⟨f _ h.zero,f _ h.quarter,f _ h.one,f _ h.two,f _ h.denominator,f _ h.fraction,
    f _ h.successor,h.gradient.mono f,?_⟩
  intro j
  obtain ⟨hd,hm,ha⟩ := h.move j
  exact ⟨f _ hd,f _ hm,f _ ha⟩

omit [IsStrictOrderedRing K] in
theorem LabelSafe.mono {P R : K → Prop} {Q : Matrix (Fin n) (Fin n) K} {i : Fin n}
    (h : LabelSafe Q i P) (f : ∀ x, P x → R x) : LabelSafe Q i R :=
  ⟨f _ h.zero,f _ h.one,f _ h.quarter,fun j hj => f _ (h.natural j hj),
    fun j => f _ (h.cap j),fun p hp => (h.rounds p hp).mono f,h.finalGradient.mono f,
    f _ h.thousand,f _ h.scale,f _ h.scaleSq,f _ h.threshold,
    fun j => f _ (h.term j),fun k hk => f _ (h.prefix k hk)⟩

/-- Composable per-call contract. A caller can use one common register budget `W` across
arbitrarily many calls. The required size threshold depends on this residual matrix and its
dimension, independently of the values in the caller's saved cells. -/
theorem labelBlock_rational_framed (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) ℚ)
    (hs : Qᵀ=Q) (he : Q*Q=Q) (m : Memory ℚ) (B W : ℕ)
    (hm : m.AllData (fun x => ratBits x≤W)) (a : Addresses L i m)
    (hQ : ∀ r j : Fin n, m.data (L.matrix+r.val*n+j.val)=Q r j)
    (hb : ∀ r j : Fin n, ratBits (Q r j)≤B) (hw : labelBitWidth n B≤W) :
    ∃ t k, k+1≤labelTime n ∧ Block.Eval (Memory.AllData (fun x => ratBits x≤W)) labelBlock m k t ∧
      t.data 19=(if fwLabel Q i then 1 else 0) ∧ CallerFrame L m t ∧
      (∀ r, 35≤r → t.index r=m.index r) := by
  have safe := (labelSafe_rational Q i hs he B hb).mono (R:=fun x => ratBits x≤W)
    (fun _ hx => hx.trans hw)
  obtain ⟨t,k,hk,e,hf,hframe⟩ := labelBlock_framed L i Q hs he m _ hm a hQ safe
  refine ⟨t,k,hk,e,?_,hframe,fun _ hr => labelBlock_index_frame e hr⟩
  simpa [fwLabel,fwArray_correct,fwTolerance,energyThreshold] using hf

end FWRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
