import OAI.Optimization.LinearProgramming.RAM.StrideCopy
import OAI.Optimization.LinearProgramming.PrimalDual.OutputSetup
import Mathlib.Tactic.Ring

/-! Gather a finite strided source into a dense window above it. The reserved
scratch scalar is 1, disjoint from all even guest slots and odd saved slots 3,5,… . -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Tape RAM.Block

def gather (stride ar dr nr : Nat) : Block :=
  .seq (CursorBind.script [.reg 0 ar,.reg 1 dr,.reg 3 nr]) (StrideCopy.block false 0 1 2 3 1 stride 1)

theorem gather_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K → Prop} (stride ar dr nr src dst n : Nat) (s : Memory K) (hs : Good P s)
    (_ha : 6 ≤ ar) (hd : 6 ≤ dr) (hn : 6 ≤ nr) (ha' : s.index ar = src)
    (hd' : s.index dr = dst) (hn' : s.index nr = n) (hstride : 0 < stride)
    (hsrc : ∀ j < n, src+stride*j ≠ 1) (hdst : 2 ≤ dst) (sep : src+stride*n ≤ dst) :
    ∃ t, Eval (Good P) (gather stride ar dr nr) s (n*(stride+6)+5) t ∧
      (∀ j < n, t.data (dst+j) = s.data (src+stride*j)) ∧
      (∀ k, k ≠ 1 → (k < dst ∨ dst+n ≤ k) → t.data k = s.data k) ∧
      ∀ k, 6 ≤ k → t.index k = s.index k := by
  let bs : List CursorBind := [.reg 0 ar,.reg 1 dr,.reg 3 nr]
  let u := CursorBind.install bs s
  have setup := CursorBind.run bs s hs
  have ud : u.data=s.data := rfl
  have u0 : u.index 0 = src := by simp [u,bs,CursorBind.install,CursorBind.apply,ha']
  have u1 : u.index 1 = dst := by
    simp [u,bs,CursorBind.install,CursorBind.apply,Memory.putIndex_ne _ (by omega : dr ≠ 0),hd']
  have u3 : u.index 3 = n := by
    simp [u,bs,CursorBind.install,CursorBind.apply,Memory.putIndex_ne _ (by omega : nr ≠ 0),
      Memory.putIndex_ne _ (by omega : nr ≠ 1),hn']
  have uf (k : Nat) (hk : 6 ≤ k) : u.index k = s.index k := by
    simp [u,bs,CursorBind.install,CursorBind.apply,Memory.putIndex_ne _ (by omega : k ≠ 0),
      Memory.putIndex_ne _ (by omega : k ≠ 1),Memory.putIndex_ne _ (by omega : k ≠ 3)]
  obtain ⟨t,run,out,frame,_,_,_,indices⟩ := StrideCopy.block_correct P u false 0 1 2 3 1 stride 1 n
    setup.safe_end u3 (by decide) (by decide) (by simp)
    (fun j hj => by simpa [u0] using hsrc j hj)
    (fun j _ => by simp [u1]; omega)
    (fun i j hij hj => by
      apply StrideCopy.forward_separated hstride (by decide) _ (hij.trans hj) hj
      exact Or.inl (by simpa only [u0,u1] using sep))
  refine ⟨t,?_,?_,?_,fun k hk => (indices k (by omega) (by omega) (by omega)).trans (uf k hk)⟩
  · have hcost : n*(stride+6)+5 = bs.length+(n*(stride+1+5)+2) := by
      change n*(stride+6)+5=3+(n*(stride+1+5)+2); ring
    rw [hcost]; exact setup.seq run
  · intro j hj
    simpa [u1,u0,ud] using out j hj
  · intro k h1 hw
    apply frame k h1
    intro j hj; simp [u1]; omega

end PrimalDual
end LinearProgramming
end Optimization
end OAI
