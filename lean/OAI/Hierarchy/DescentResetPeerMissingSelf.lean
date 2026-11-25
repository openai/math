import OAI.Hierarchy.DescentNativeBankLookup

namespace OAI
/-! # Testing a receiver against its three physical raw neighbor words -/
namespace Hierarchy.DescentResetPeerMissingSelf
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Fin.CommRing
variable {w P floor : ℕ}

def probe (peers : Bank) (P : ℕ) (here : Expr) (j : Fin 3) (rest : Expr) : Expr :=
  .branch .eq (.lookup peers (.op .add (.lit (j.val*P)) here)) here (.lit 0) rest

def missing (peers : Bank) (P : ℕ) (here : Expr) : Expr :=
  probe peers P here 0 (probe peers P here 1 (probe peers P here 2 (.lit 1)))

theorem fits (peers : Bank) (P : ℕ) (here : Expr) (bank : peers.Fits w floor) (arg : here.Fits w floor) :
    (missing peers P here).Fits w floor := by simp [missing,probe,Expr.Fits,bank,arg]

theorem work (peers : Bank) (P : ℕ) (here : Expr) :
    (missing peers P here).work=6*here.work+28 := by simp [missing,probe,Expr.work]; omega

theorem amount (peers : Bank) (P : ℕ) (here : Expr) :
    (missing peers P here).work ≤ 28*(here.work+1) := by rw [work]; omega

theorem read (peers : Bank) (P : ℕ) (here : Expr) (m : Memory w) (r : Word w)
    (v : Fin P) (row : Fin 3→Option (Fin P)) (bank : peers.Fits w floor)
    (size : 3*P ≤ peers.size) (wide : P < 2^w) (which_ : here.eval m r=(v.val:Word w))
    (words : ∀j : Fin 3,m (peers.base+j.val*P+v.val)=(((row j).elim P Fin.val : ℕ) : Word w)) :
    (missing peers P here).eval m r=if ∀j,row j≠some v then 1 else 0 := by
  have test (j : Fin 3) : Comparison.eq.test
      ((Expr.lookup peers (.op .add (.lit (j.val*P)) here)).eval m r) (here.eval m r)=decide (row j=some v) := by
    have index : (Expr.op .add (.lit (j.val*P)) here).eval m r=((j.val*P+v.val:ℕ):Word w) := by
      simp [Expr.eval,RowOp.opcode,BinaryOp.eval,which_,Nat.cast_add]
    have endRow : j.val*P+v.val < 3*P :=
      (Nat.add_lt_add_left v.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right P j.isLt)
    rw [DescentIssuedTerminalId.lookup_nat peers m r _ _ index (endRow.trans_le size) bank.2.1,
      ←Nat.add_assoc,words,which_]
    have comp (x : ℕ) (hx : x < 2^w) :
        Comparison.eq.test (x:Word w) (v.val:Word w)=decide (x=v.val) := by
      by_cases eq : x=v.val
      · simp [Comparison.test,eq]
      · have unequal : (x:Word w)≠(v.val:Word w):=fun h=>eq (by
          simpa [Fin.val_cast_of_lt hx,Fin.val_cast_of_lt (v.isLt.trans wide)] using congrArg Fin.val h)
        simp [Comparison.test,eq,unequal]
    cases hv : row j with
    | none=>simp [Option.elim,comp P wide,Nat.ne_of_gt v.isLt]
    | some t=>
      simp only [Option.elim_some,comp t.val (t.isLt.trans wide),Option.some.injEq,Fin.val_inj]
  have expand (j : Fin 3) (rest : Expr) : (probe peers P here j rest).eval m r=
      if row j=some v then 0 else rest.eval m r := by
    change (if Comparison.eq.test _ _ then (0:Word w) else rest.eval m r)=_
    rw [test]
    simp
  have three : (∀j,row j≠some v) ↔ row 0≠some v ∧ row 1≠some v ∧ row 2≠some v := by
    constructor
    · intro all; exact ⟨all 0,all 1,all 2⟩
    · rintro ⟨a,b,c⟩ j; fin_cases j <;> assumption
  simp only [missing,expand,Expr.eval,three]
  by_cases a : row 0=some v <;> by_cases b : row 1=some v <;> by_cases c : row 2=some v <;> simp [a,b,c]

end Hierarchy.DescentResetPeerMissingSelf

end OAI
