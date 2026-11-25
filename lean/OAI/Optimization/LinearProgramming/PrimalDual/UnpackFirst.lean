import OAI.Optimization.LinearProgramming.PrimalDual.BridgeLayout
import OAI.Optimization.LinearProgramming.PrimalDual.Gather
import OAI.Optimization.LinearProgramming.PrimalDual.PassesRAM
import OAI.Optimization.LinearProgramming.PrimalDual.Layout

/-! Unpack the optimizer input and the first feasible point from the actual isolated
RAM return. The saved input ends immediately before the copied base point. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace Bridge

open RAM RAM.Tape RAM.Block

theorem FirstRegs.transfer {a b : Nat → Nat} {m d B : Nat}
    (r : FirstRegs a m d B) (h : ∀ i, 40 ≤ i → b i = a i) : FirstRegs b m d B := by
  rcases r with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩
  constructor <;> rwa [h _ (by decide)]

theorem ReturnRegs.transfer {a b : Nat → Nat} {m d : Nat}
    (r : ReturnRegs a m d) (h : ∀ i, 40 ≤ i → b i = a i) : ReturnRegs b m d := by
  rcases r with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h10,h11,h12,h13⟩
  constructor <;> rwa [h _ (by decide)]

def unpackFirst : Block :=
  .seq firstHeader (.seq (gather 2 42 44 48) (gather 2 40 45 43))

/-- Only two scalar windows and the layout's scratch word are modified. -/
theorem unpackFirst_correct {m d B H : Nat} (A : Matrix (Fin m) (Fin d) ℚ) (b : Fin m → ℚ)
    (c x₀ : Fin d → ℚ) (s : Memory ℚ) (safe : Good (fun q => ratBits q ≤ H) s)
    (hm : s.index 9=m) (hd : s.index 11=d) (hB : s.index 21=B)
    (saved : ∀ j < origLen m d, s.data (3+2*j) = optInputWord A b c j)
    (guest : ∀ j : Fin d, s.data (2*j.val) = x₀ j) :
    ∃ t k, Eval (Good (fun q => ratBits q ≤ H)) unpackFirst s k t ∧
      k ≤ 3+(termBudget firstTerms).eval (m+d+B)+8*origLen m d+8*d+10 ∧
      FirstRegs t.index m d B ∧
      (∀ j < origLen m d, t.data (origin m d+j) = optInputWord A b c j) ∧
      Holds t (origin m d+origLen m d) x₀ ∧
      (∀ i, jointBase m d ≤ i → t.data i = s.data i) := by
  obtain ⟨u,k,hhead,hk,ds,r⟩ := firstHeader_correct s safe m d B hm hd hB
  obtain ⟨_,enough,pointRoom,hi⟩ := origin_above m d
  obtain ⟨v,orig,out1,fr1,idx1⟩ := gather_correct 2 42 44 48 3 (origin m d) (origLen m d) u hhead.safe_end
    (by decide) (by decide) (by decide) r.odd r.orig r.inputLen (by decide) (by omega)
    (by omega) enough
  have r' := r.transfer (fun i h => idx1 i (by omega))
  obtain ⟨t,point,out2,fr2,idx2⟩ := gather_correct 2 40 45 43 0 (origin m d+origLen m d) d v orig.safe_end
    (by decide) (by decide) (by decide) r'.even r'.point r'.dreg (by decide) (by omega)
    (by omega) (by omega)
  refine ⟨t,_,hhead.seq (orig.seq point),by omega,r'.transfer (fun i h => idx2 i (by omega)),?_,?_,?_⟩
  · intro j hj
    exact (fr2 _ (by omega) (.inl (by omega))).trans
      ((out1 j hj).trans ((congrFun ds _).trans (saved j hj)))
  · intro i
    have addr : 2*i.val < origin m d := by omega
    have e := out2 i.val i.isLt
    rw [Nat.zero_add] at e
    exact e.trans ((fr1 _ (by omega) (.inl addr)).trans ((congrFun ds _).trans (guest i)))
  · intro i h
    unfold jointBase at h
    exact (fr2 _ (by omega) (.inr (by omega))).trans
      ((fr1 _ (by omega) (.inr (by omega))).trans (congrFun ds _))

end Bridge
end PrimalDual
end LinearProgramming
end Optimization
end OAI
