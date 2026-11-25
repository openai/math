import OAI.Optimization.LinearProgramming.Compression.ProxyResidentCode
import OAI.Optimization.LinearProgramming.RAM.Array

/-! Read one logical cache address and construct its nested physical representation. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ResidentInstall

open RAM GeneratorTable

variable {K : Type*}

/-- The generator service uses exactly these same address instructions on a
field-independent natural address bank. Every scalar of the ambient field is retained. -/
def applyAddressMove (m : Memory K) : SlotMove → Memory K
  | .copy d r => m.putIndex d (m.index r)
  | .incr d r => m.putIndex d (m.index r+1)
  | .decr d r => m.putIndex d (m.index r-1)
  | .constant d k => m.putIndex d k

def moveAddresses (m : Memory K) : List SlotMove → Memory K
  | [] => m
  | a::xs => moveAddresses (applyAddressMove m a) xs

@[simp] theorem applyAddressMove_data (m : Memory K) (a : SlotMove) : (applyAddressMove m a).data=m.data := by
  cases a <;> rfl

@[simp] theorem moveAddresses_data (m : Memory K) (xs : List SlotMove) : (moveAddresses m xs).data=m.data := by
  induction xs generalizing m with
  | nil => rfl
  | cons a xs ih => simp [moveAddresses,ih]

theorem runAddressMoves [Field K] [LinearOrder K] [IsStrictOrderedRing K] (P : K→Prop) (m : Memory K)
    (xs : List SlotMove) (hm : m.AllData P) :
    Block.Eval (Memory.AllData P) (slotMoves xs) m xs.length (moveAddresses m xs) := by
  induction xs generalizing m with
  | nil => exact .skip hm
  | cons a xs ih =>
    have safe : (applyAddressMove m a).AllData P := fun i => by
      rw [applyAddressMove_data];exact hm i
    have step : Block.Eval (Memory.AllData P) (.op a.instruction) m 1 (applyAddressMove m a) := by
      cases a with
      | copy d r => exact Block.Eval.op_addrCopy _ _ _ hm safe
      | incr d r => exact Block.Eval.op_incr _ _ _ hm safe
      | decr d r => exact Block.Eval.op_decr _ _ _ hm safe
      | constant d k => exact Block.Eval.op_addrConst _ _ _ hm safe
    simpa [slotMoves,moveAddresses,Nat.add_comm] using step.seq (ih (applyAddressMove m a) safe)

/-- The resident numeric layout uses logical addresses 60 and above. The external
controller's low port words are ignored while encoding the numerical caller. -/
def sourceAddress (j : ℕ) (s : Memory K) : ℕ := if j < 60 then 0 else s.index j

theorem encodeResidentAddress_spec [Field K] [LinearOrder K] [IsStrictOrderedRing K] (P : K → Prop) (s : Memory K) (j : ℕ)
    (hs : s.AllData P) (h0 : s.index 0 = j) (h14 : s.index 14 = 60) :
    ∃ t k, k ≤ 12*sourceAddress j s+11 ∧ Block.Eval (Memory.AllData P) encodeResidentAddress s k t ∧
      t.data = s.data ∧ t.index 7 = 4*sourceAddress j s+2 ∧
      ∀ i, i≠4 → i≠5 → i≠6 → i≠7 → t.index i = s.index i := by
  let x := sourceAddress j s
  let a := s.putIndex 4 x
  have ha : Block.Eval (Memory.AllData P) selectAddress s (if j<60 then 3 else 2) a := by
    unfold selectAddress
    by_cases lo : j<60
    · simp only [ite_eq_left lo]
      have write : Block.Eval (Memory.AllData P) (.op (.addrConst 4 0)) s 1 a := by
        simpa [a,x,sourceAddress,lo] using
          (Block.Eval.op_addrConst (safe := Memory.AllData P) s 4 0 hs hs)
      exact Block.Eval.branchTrue (b := .op (.addrLoad 4 0))
        (show (Cond.addrLT 0 14).test s=true by simp [Cond.test,h0,h14,lo]) write
    · simp only [ite_eq_right lo]
      have write : Block.Eval (Memory.AllData P) (.op (.addrLoad 4 0)) s 1 a := by
        simpa [a,x,sourceAddress,lo,h0] using
          (Block.Eval.op_addrLoad (safe := Memory.AllData P) s 4 0 hs hs)
      exact Block.Eval.branchFalse (a := .op (.addrConst 4 0))
        (show (Cond.addrLT 0 14).test s=false by simp [Cond.test,h0,h14,lo]) write
  obtain ⟨b,eb,b6,_,bi,bd⟩ := Call.doubleHeaderEntry_run (P := P) a 6 4 ha.safe_end
    (by decide) (by decide) (by decide)
  obtain ⟨c,ec,c7,_,ci,cd⟩ := Call.doubleHeaderEntry_run (P := P) b 7 6 eb.safe_end
    (by decide) (by decide) (by decide)
  let t := moveAddresses c plusTwo
  have et : Block.Eval (Memory.AllData P) (slotMoves plusTwo) c 2 t :=
    runAddressMoves P c plusTwo ec.safe_end
  have a4 : a.index 4 = x := by simp [a]
  have encoded : t.index 7 = 4*x+2 := by
    simp [t,plusTwo,moveAddresses,applyAddressMove,c7,b6,a4]
    omega
  refine ⟨t,_,?_,ha.seq (eb.seq (ec.seq et)),(moveAddresses_data c plusTwo).trans (cd.trans bd),encoded,?_⟩
  · change (if j<60 then 3 else 2)+((4*a.index 4+3)+((4*b.index 6+3)+2)) ≤ 12*x+11
    rw [b6,a4]
    split_ifs <;> omega
  · intro i h4 h5 h6 h7
    have ft : t.index i = c.index i := by simp [t,plusTwo,moveAddresses,applyAddressMove,h7]
    exact ft.trans ((ci i h5 h7).trans ((bi i h5 h6).trans (by simp [a,h4])))

end ResidentInstall
end Compression
end LinearProgramming
end Optimization
end OAI
