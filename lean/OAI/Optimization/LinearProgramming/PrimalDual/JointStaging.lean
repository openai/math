import OAI.Optimization.LinearProgramming.RAM.RAMIndex
import OAI.Optimization.LinearProgramming.PrimalDual.CopyRAM
import Mathlib.Tactic.Linarith

/-! Move the original optimization input away from scalar register zero before running
subroutines which use scalar scratch space. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PrimalDual
namespace JointRAM

open RAM RAM.Block RAM.Tape

private inductive AddrMove where
  | set (r value : Nat)
  | cp (dst src : Nat)
  | inc (r : Nat)

namespace AddrMove

private def instr : AddrMove → Instr
  | .set r v => .addrConst r v
  | .cp d s => .addrCopy d s
  | .inc r => .incr r r

private def index (i : Nat → Nat) : AddrMove → Nat → Nat
  | .set r v => Function.update i r v
  | .cp d s => Function.update i d (i s)
  | .inc r => Function.update i r (i r+1)

private def after : List AddrMove → (Nat → Nat) → Nat → Nat
  | [], i => i
  | c::cs, i => after cs (index i c)

private def block (cs : List AddrMove) : Block := .straight (cs.map instr)

private theorem correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K → Prop} (cs : List AddrMove) (s : Memory K) (hs : Good P s) :
    Eval (Good P) (block cs) s cs.length ⟨s.data, after cs s.index⟩ := by
  induction cs generalizing s with
  | nil => exact .skip hs
  | cons x xs ih =>
    let t : Memory K := ⟨s.data,index s.index x⟩
    have op : Eval (Good P) (.op x.instr) s 1 t := by
      cases x <;> exact .op hs hs (fun _ => rfl)
    simpa only [t,after,block,List.map_cons,Block.straight,List.length_cons,Nat.add_comm 1] using
      op.seq (ih t op.safe_end)

end AddrMove

private def originalLength : AddressTerm 9 :=
  let m : AddressTerm 9 := .reg 0
  let d : AddressTerm 9 := .reg 1
  m*d+m+d

/-- Registers 10 and 11 save dimensions, 9 saves the scalar input length,
and 6 saves `length+2`, the new source base. -/
private def saveHeaders : List AddrMove :=
  [.cp 10 0,.cp 11 1,.cp 9 12,.cp 6 12,.inc 6,.inc 6,.cp 13 12]

/-- Save the destination base `2*length+2` in register 7 and initialize the copying ABI. -/
private def copyHeaders : List AddrMove :=
  [.cp 7 12,.inc 7,.inc 7,.set 0 0,.cp 1 6,.cp 2 9,.set 3 0]

private def restoreHeaders : List AddrMove := [.cp 0 10,.cp 1 11,.cp 2 6,.cp 3 7]

/-- The canonical input initially starts at zero. The staged input starts at `length+2`;
the output window starts immediately after it, at `2*length+2`. -/
def stageWindows : Block :=
  .seq (originalLength.code 12) (.seq (AddrMove.block saveHeaders) (.seq (addSub true 12)
    (.seq (AddrMove.block copyHeaders) (.seq (copyWindow false) (AddrMove.block restoreHeaders)))))

/-- This fixed block accepts the unshifted input tape and preserves exactly its entries at
the new source base. The bound covers the actual copying, addressing, and initial pointer setup. -/
theorem stageWindows_correct {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {P : K → Prop} (m d : Nat) (s : Memory K) (hs : Good P s)
    (hm : s.index 0 = m) (hd : s.index 1 = d) :
    let L := m*d+m+d
    ∃ t k, Eval (Good P) stageWindows s k t ∧ k ≤ 80*(m+d+1)^2 ∧
      t.index 0 = m ∧ t.index 1 = d ∧ t.index 2 = L+2 ∧ t.index 3 = 2*L+2 ∧
      ∀ i < L, t.data ((L+2)+i) = s.data i := by
  let L := m*d+m+d
  let env := fun i : Fin 9 => s.index i
  obtain ⟨k,u,he,hk,hu,hf,hl⟩ := originalLength.correct env 12 s (by decide) (fun _ => rfl) hs
  have hlen : u.index 12 = L := by change u.index 12 = s.index 0*s.index 1+s.index 0+s.index 1 at hl; simpa [hm,hd,L] using hl
  have hcost : k ≤ 12+(5+4*m)*d+4*m+4*d := by
    change k ≤ (1+(1+(4+(5+4*s.index 0)*s.index 1))+(1+(2+4*s.index 0)))+(1+(2+4*s.index 1)) at hk
    rw [hm,hd] at hk
    omega
  let v : Memory K := ⟨u.data, AddrMove.after saveHeaders u.index⟩
  have hsv := AddrMove.correct saveHeaders u he.safe_end
  have hv (i : Nat) (req : i=6 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13) :
      v.index i = if i=6 then L+2 else if i=10 then m else if i=11 then d else L := by
    have h0 := (hf 0 (by decide)).trans hm
    have h1 := (hf 1 (by decide)).trans hd
    rcases req with rfl|rfl|rfl|rfl|rfl|rfl <;>
      simp [v,saveHeaders,AddrMove.after,AddrMove.index,hlen,h0,h1]
  obtain ⟨l,w,hadd,hlcost,hw,hfront,hresult⟩ := addSub_correct true 12 v hsv.safe_end
  have hw12 : w.index 12 = L+L := by simpa [hv 12 (by decide),hv 13 (by decide)] using hresult
  have hwf (i : Nat) (h : i=6 ∨ i=9 ∨ i=10 ∨ i=11) :
      w.index i = if i=6 then L+2 else if i=10 then m else if i=11 then d else L :=
    (hfront i (by omega)).trans (hv i (by omega))
  let x : Memory K := ⟨w.data,AddrMove.after copyHeaders w.index⟩
  have hcx := AddrMove.correct copyHeaders w hadd.safe_end
  have hx6 := hwf 6 (by decide)
  have hx9 := hwf 9 (by decide)
  have hxa : x.index 0 = 0 ∧ x.index 1 = L+2 ∧ x.index 2 = L ∧ x.index 3 = 0 ∧
      x.index 6 = L+2 ∧ x.index 7 = 2*L+2 ∧ x.index 10=m ∧ x.index 11=d := by
    simp [x,copyHeaders,AddrMove.after,AddrMove.index,hw12,hwf 6 (by decide),hwf 9 (by decide),
      hwf 10 (by decide),hwf 11 (by decide),two_mul]
  obtain ⟨y,copy,hcp,_,hy⟩ := copyWindow_correct false L 0 (L+2) x hcx.safe_end
    hxa.1 hxa.2.1 hxa.2.2.1 hxa.2.2.2.1 (Or.inl (by omega)) (by simp)
  have hrest := AddrMove.correct restoreHeaders y copy.safe_end
  refine ⟨_,_,.seq he (.seq hsv (.seq hadd (.seq hcx (.seq copy hrest)))),?_,?_,?_,?_,?_,?_⟩
  · have hl' : l ≤ 2+4*L := by simpa [hv 13 (by decide)] using hlcost
    change k+(7+(l+(7+(L*(5+2)+1+4)))) ≤ _
    dsimp [L] at *
    nlinarith [Nat.zero_le (m^2),Nat.zero_le (d^2),Nat.zero_le (m*d)]
  · simpa [restoreHeaders,AddrMove.after,AddrMove.index] using (hy 10 (by decide)).trans hxa.2.2.2.2.2.2.1
  · simpa [restoreHeaders,AddrMove.after,AddrMove.index] using (hy 11 (by decide)).trans hxa.2.2.2.2.2.2.2
  · simpa [restoreHeaders,AddrMove.after,AddrMove.index] using (hy 6 (by decide)).trans hxa.2.2.2.2.1
  · simpa [restoreHeaders,AddrMove.after,AddrMove.index] using (hy 7 (by decide)).trans hxa.2.2.2.2.2.1
  · intro i hi
    exact (hcp i hi).trans ((congrFun hw (0+i)).trans (by simpa using congrFun hu i))

end JointRAM
end PrimalDual
end LinearProgramming
end Optimization
end OAI
