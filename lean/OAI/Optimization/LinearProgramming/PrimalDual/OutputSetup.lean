import OAI.Optimization.LinearProgramming.PrimalDual.CopyRAM

/-! Binding the streaming block's cursor registers to caller-supplied high registers. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual

variable {K : Type*}

open RAM RAM.Block RAM.Tape

inductive CursorBind
  | reg (dst src : Nat)
  | literal (dst n : Nat)

namespace CursorBind

def instr : CursorBind → Instr
  | .reg d s => .addrCopy d s
  | .literal d n => .addrConst d n

def apply (b : CursorBind) (s : Memory K) : Memory K :=
  match b with
  | .reg d r => s.putIndex d (s.index r)
  | .literal d n => s.putIndex d n

def script (bindings : List CursorBind) : Block := .straight (bindings.map instr)
def install (bindings : List CursorBind) (s : Memory K) : Memory K :=
  bindings.foldl (fun t b => b.apply t) s

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

/-- Cursor initialization uses one real address instruction per binding. -/
theorem run (bs : List CursorBind) (s : Memory K) (hs : Good P s) :
    Eval (Good P) (script bs) s bs.length (install bs s) := by
  induction bs generalizing s with
  | nil => exact .skip hs
  | cons b bs ih =>
    have h : Eval (Good P) (.op b.instr) s 1 (b.apply s) := by
      cases b with
      | reg d r => exact eval_copyI s hs d r
      | literal d n => exact eval_constI s hs d n
    simpa [script,install,Block.straight,Nat.add_comm] using h.seq (ih _ h.safe_end)

end CursorBind

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {P : K → Prop}

/-- Copy n words using the three permanent registers sReg, dReg, nReg. Pointer
registers carry the first actual addresses for the selected traversal direction. -/
def copyFromRegs (rev : Bool) (sReg dReg nReg : Nat) : Block :=
  .seq (CursorBind.script [.reg 0 sReg,.reg 1 dReg,.reg 2 nReg,.literal 3 0]) (copyWindow rev)

theorem copyFromRegs_correct (rev : Bool) (n src dst sReg dReg nReg : Nat)
    (s : Memory K) (hs : Good P s) (_hsi : 6 ≤ sReg) (hdi : 6 ≤ dReg) (hni : 6 ≤ nReg)
    (hsrc : s.index sReg = startPointer rev src n) (hdst : s.index dReg = startPointer rev dst n)
    (hsize : s.index nReg = n) (hsep : src+n ≤ dst ∨ dst+n ≤ src)
    (hmode : if rev then 0 < src else 0 < dst) :
    ∃ t, Eval (Good P) (copyFromRegs rev sReg dReg nReg) s (7*n+5) t ∧
      (∀ k < n, t.data (dst+k) = s.data (src+k)) ∧
      (∀ a, a ≠ 0 → (a < dst ∨ dst+n ≤ a) → t.data a = s.data a) ∧
      (∀ k, 6 ≤ k → t.index k = s.index k) := by
  let bs : List CursorBind := [.reg 0 sReg,.reg 1 dReg,.reg 2 nReg,.literal 3 0]
  let u := CursorBind.install bs s
  have init := CursorBind.run bs s hs
  have ds : u.data = s.data := rfl
  have u0 : u.index 0 = s.index sReg := by simp [u,bs,CursorBind.install,CursorBind.apply]
  have u1 : u.index 1 = s.index dReg := by
    simp [u,bs,CursorBind.install,CursorBind.apply,Memory.putIndex_ne _ (by omega : dReg ≠ 0)]
  have u2 : u.index 2 = s.index nReg := by
    simp [u,bs,CursorBind.install,CursorBind.apply,Memory.putIndex_ne _ (by omega : nReg ≠ 0),
      Memory.putIndex_ne _ (by omega : nReg ≠ 1)]
  have u3 : u.index 3 = 0 := by simp [u,bs,CursorBind.install,CursorBind.apply]
  have uf (k : Nat) (hk : 6 ≤ k) : u.index k = s.index k := by
    simp [u,bs,CursorBind.install,CursorBind.apply,Memory.putIndex_ne _ (by omega : k ≠ 0),
      Memory.putIndex_ne _ (by omega : k ≠ 1),Memory.putIndex_ne _ (by omega : k ≠ 2),
      Memory.putIndex_ne _ (by omega : k ≠ 3)]
  obtain ⟨t,hr,hw,hf,hi⟩ := copyWindow_correct rev n src dst u init.safe_end (u0.trans hsrc) (u1.trans hdst)
    (u2.trans hsize) u3 hsep hmode
  refine ⟨t,?_,hw,hf,fun k hk => (hi k (by omega)).trans (uf k hk)⟩
  have hcost : 7*n+5 = bs.length+(n*(5+2)+1) := by change 7*n+5=4+(n*(5+2)+1); omega
  rw [hcost]
  exact init.seq hr

end PrimalDual
end LinearProgramming
end Optimization
end OAI
