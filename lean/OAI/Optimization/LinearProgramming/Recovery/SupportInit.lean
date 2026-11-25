import OAI.Optimization.LinearProgramming.Recovery.SupportRAM
import OAI.Optimization.LinearProgramming.RAM.ArrayFill

/-! Initialize the marked-support window, including the anchor, on the actual RAM. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace SupportRAM

open RAM
open _root_.OAI.Optimization.LinearProgramming.Geometry (deleteCoordinates)

/-- Fill every scalar flag with one and position both cursors at coordinate one. -/
def initFlags : Block := .seq (.op (.const 150 1)) (.seq (fillBlock 150 151 153 152 150)
  (.seq (.op (.addrConst 152 1)) (.seq (.op (.addrCopy 153 151)) (.op (.incr 153 153)))))

def search (call : Block) : Block := .seq initFlags (program call)

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The matrix, its original right-hand side, and all other caller scalars outside the
flag window are preserved except the one named constant register. -/
theorem initFlags_spec (P : K → Prop) (one : P 1) (v : Memory K) (n base : ℕ) (hs : ∀ a, P (v.data a))
    (hn : v.index 150=n) (hb : v.index 151=base) (lo : 152 ≤ base) :
    ∃ t, Block.Eval (fun z => ∀ a, P (z.data a)) initFlags v (5*n+7) t ∧
      Layout t base 1 (Finset.univ : Finset (Fin n)) ∧
      (∀ a, a≠150 → (a < base ∨ base+n ≤ a) → t.data a=v.data a) ∧
      ∀ a, a≠152 → a≠153 → t.index a=v.index a := by
  let a := v.putData 150 (1 : K)
  have sa : ∀ i, P (a.data i) := by
    intro i
    by_cases h : i=150
    · subst i; simpa [a] using one
    · simpa [a,Memory.putData_ne _ h] using hs i
  have ea : Block.Eval (fun z => ∀ i, P (z.data i)) (.op (.const 150 1)) v 1 a := by
    simpa only [Rat.cast_one] using Block.Eval.op_const v 150 1 hs (by simpa only [Rat.cast_one] using sa)
  obtain ⟨b,eb,flags,frame,_,_,bidx⟩ := fillBlock_correct P a 150 151 153 152 150 n (by decide)
    (by decide) (by decide) hn (by change 150 < v.index 151; omega) sa
  let c := b.putIndex 152 1
  let d := c.putIndex 153 (c.index 151)
  let t := d.putIndex 153 (d.index 153+1)
  have sc : ∀ i, P (c.data i) := eb.safe_end
  have sd : ∀ i, P (d.data i) := eb.safe_end
  have st : ∀ i, P (t.data i) := eb.safe_end
  have ec := Block.Eval.op_addrConst (safe:=fun z=>∀ a,P (z.data a)) b 152 1 eb.safe_end sc
  have ed := Block.Eval.op_addrCopy (safe:=fun z=>∀ a,P (z.data a)) c 153 151 sc sd
  have et := Block.Eval.op_incr (safe:=fun z=>∀ a,P (z.data a)) d 153 153 sd st
  have b150 := (bidx 150 (by decide) (by decide)).trans hn
  have b151 := (bidx 151 (by decide) (by decide)).trans hb
  have run := ea.seq (eb.seq (ec.seq (ed.seq et)))
  refine ⟨t,?_,?_,?_,?_⟩
  · have clock : 1+((5*n+3)+(1+(1+1)))=5*n+7 := by omega
    rw [←clock]
    exact run
  · refine ⟨by simp [t,d,c,b150],by simp [t,d,c,b151],by simp [t,d,c],by simp [t,d,c,b151],?_⟩
    intro j
    simpa [t,d,c,a,hb] using flags j.val j.isLt
  · intro i hi hr
    change b.data i=v.data i
    exact (frame i (by simpa [a,hb] using hr)).trans (Memory.putData_ne _ hi _)
  · intro i h152 h153
    simpa [t,d,c,a,Memory.putIndex_ne _ h152,Memory.putIndex_ne _ h153] using bidx i h152 h153

/-- Startup plus the complete normal greedy scan: exactly the same final retained
coordinates as the mathematical decision-to-witness routine. -/
theorem search_spec (P : K → Prop) (zero : P 0) (one : P 1) {m base limit : ℕ}
    (oracle : Finset (Fin (m+1)) → Bool) (call : Block) (realizes : Realizes call P base limit oracle)
    (v : Memory K) (hs : ∀ a, P (v.data a)) (hn : v.index 150=m+1) (hb : v.index 151=base) (lo : 152 ≤ base) :
    ∃ t k, k ≤ 5*(m+1)+8+m*(limit+10) ∧ Block.Eval (fun z => ∀ a, P (z.data a)) (search call) v k t ∧
      Layout t base (m+1) (deleteCoordinates oracle ((List.finRange (m+1)).erase 0) Finset.univ).1 := by
  obtain ⟨a,e,h,_,_⟩ := initFlags_spec P one v (m+1) base hs hn hb lo
  obtain ⟨t,k,hk,ee,ht⟩ := marked_program_spec oracle call P zero realizes lo a e.safe_end h
  exact ⟨t,_,by omega,e.seq ee,ht⟩

end SupportRAM
end Recovery
end LinearProgramming
end Optimization
end OAI
