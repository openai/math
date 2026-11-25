import OAI.Optimization.LinearProgramming.PrimalDual.ScanRAM
import OAI.Optimization.LinearProgramming.PrimalDual.OutputSetup

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

open RAM RAM.Block RAM.Tape

namespace OutputPass

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

/-- Bind the three stream pointers and the length from permanent caller registers. -/
def bindScan (ar br dr nr : Nat) : List CursorBind :=
  [.reg 0 ar,.reg 1 br,.reg 2 dr,.reg 5 nr]

/-- Dot starts with a zero accumulator; the divisor in a normalizing pass is preserved. -/
def scanFromRegs (p : OutputPass) (ar br dr nr : Nat) : Block :=
  .seq (CursorBind.script (bindScan ar br dr nr)) (.seq
    (if p = .dot then .op (.const 3 0) else .skip) p.scan)

theorem scanFromRegs_correct (p : OutputPass) (n a b dst ar br dr nr : Nat)
    (s : Memory K) (hs : Good P s) (hz : P 0)
    (_hra : 6 ≤ ar) (hrb : 6 ≤ br) (hrd : 6 ≤ dr) (hrn : 6 ≤ nr)
    (hA : s.index ar = a) (hB : s.index br = b) (hD : s.index dr = dst) (hsz : s.index nr = n)
    (ha : 4 ≤ a) (hb : 4 ≤ b) (hd : 4 ≤ dst)
    (sepA : p = .dot ∨ a = dst ∨ a+n ≤ dst ∨ dst+n ≤ a)
    (sepB : p = .dot ∨ b = dst ∨ b+n ≤ dst ∨ dst+n ≤ b)
    (acc result : Nat → K) (acc0 : (if p = .dot then 0 else s.data 3) = acc 0)
    (hv : ∀ j < n, result j = p.returned (s.data (a+j)) (s.data (b+j)) (acc j))
    (hn : ∀ j < n, acc (j+1) = p.nextAccumulator (acc j) (result j))
    (hdiv : ∀ j < n, p = .normalize → acc j ≠ 0)
    (hvSafe : ∀ j < n, P (result j)) (haSafe : ∀ j ≤ n, P (acc j)) :
    ∃ t, Eval (Good P) (p.scanFromRegs ar br dr nr) s (10*n+6+(if p = .dot then 1 else 0)) t ∧
      t.data 3 = acc n ∧ (∀ k < n, p ≠ .dot → t.data (dst+k) = result k) ∧
      (∀ k, 4 ≤ k → (p = .dot ∨ k < dst ∨ dst+n ≤ k) → t.data k = s.data k) ∧
      (∀ k, 6 ≤ k → t.index k = s.index k) := by
  let u := CursorBind.install (bindScan ar br dr nr) s
  have init := CursorBind.run (bindScan ar br dr nr) s hs
  have u0 : u.index 0 = a := by simp [u,bindScan,CursorBind.install,CursorBind.apply,hA]
  have u1 : u.index 1 = b := by
    simp [u,bindScan,CursorBind.install,CursorBind.apply,Memory.putIndex_ne _ (by omega : br ≠ 0),hB]
  have u2 : u.index 2 = dst := by
    simp [u,bindScan,CursorBind.install,CursorBind.apply,Memory.putIndex_ne _ (by omega : dr ≠ 0),
      Memory.putIndex_ne _ (by omega : dr ≠ 1),hD]
  have u5 : u.index 5 = n := by
    simp [u,bindScan,CursorBind.install,CursorBind.apply,Memory.putIndex_ne _ (by omega : nr ≠ 0),
      Memory.putIndex_ne _ (by omega : nr ≠ 1),Memory.putIndex_ne _ (by omega : nr ≠ 2),hsz]
  have uf (k : Nat) (hk : 6 ≤ k) : u.index k = s.index k := by
    simp [u,bindScan,CursorBind.install,CursorBind.apply,Memory.putIndex_ne _ (by omega : k ≠ 0),
      Memory.putIndex_ne _ (by omega : k ≠ 1),Memory.putIndex_ne _ (by omega : k ≠ 2),
      Memory.putIndex_ne _ (by omega : k ≠ 5)]
  let w := if p = .dot then u.putData 3 0 else u
  have reset : Eval (Good P) (if p = .dot then .op (.const 3 0) else .skip) u
      (if p = .dot then 1 else 0) w := by
    by_cases hp : p = .dot
    · have hz' : P ((0 : ℚ) : K) := by simpa using hz
      have op := Eval.op_const u 3 0 init.safe_end (safe_data_write u init.safe_end 3 _ hz')
      simpa [w,hp] using op
    · simpa [w,hp] using (Eval.skip init.safe_end)
  have wi : w.index = u.index := by dsimp only [w]; split <;> rfl
  have wd (k : Nat) (hk : 4 ≤ k) : w.data k = s.data k := by
    dsimp only [w]; split
    · rw [Memory.putData_ne _ (by omega : k ≠ 3)]; rfl
    · rfl
  have w3 : w.data 3 = acc 0 := by
    have hu : u.data = s.data := rfl
    by_cases hp : p = .dot
    · simpa [w,hp] using acc0
    · simpa [w,hp,hu] using acc0
  obtain ⟨t,r,act,written,frame,idx⟩ := scan_correct p n a b dst w reset.safe_end
    ((congrFun wi 0).trans u0) ((congrFun wi 1).trans u1) ((congrFun wi 2).trans u2) ((congrFun wi 5).trans u5) ha hb hd sepA sepB acc result w3
    (fun j hj => by rw [wd _ (by omega),wd _ (by omega)]; exact hv j hj)
    hn hdiv hvSafe haSafe
  refine ⟨t,?_,act,written,fun k hk h => (frame k hk h).trans (wd k hk),
    fun k hk => (idx k hk).trans ((congrFun wi k).trans (uf k hk))⟩
  have hcost : 10*n+6+(if p = .dot then 1 else 0) = (bindScan ar br dr nr).length+
      ((if p = .dot then 1 else 0)+(10*n+2)) := by change 10*n+6+_ = 4+(_+(10*n+2)); omega
  rw [hcost]
  exact init.seq (reset.seq r)

end OutputPass
end PrimalDual
end LinearProgramming
end Optimization
end OAI
