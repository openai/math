import OAI.ThreeFlat.RAM.TickTerminalRootRun
import OAI.ThreeFlat.RAM.TickTerminalPrimitiveSize

namespace OAI
/-! # Native instruction cost of selected-root replay -/

noncomputable section
namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPinsExpr PhysicalProcedure HistoryTerminalTape
open scoped Fin.CommRing BigOperators

private def addressTemplate : Arena := ⟨0,0,0,0,0,0,0,0,0,0,0,0⟩

private structure Prices where
  seed : ℕ
  commands : ℕ
  arguments : ℕ
  expression : ℕ

private def prices (W : ℕ) (A : Arena) : Prices :=
  ⟨(HeaderScan.closed (w:=W) (boot A)).binds, (generator W A true).binds,
    (generator W A false).binds, (TickTerminalPrimitive.expression W).binds⟩

private def allowance (p : Prices) : ℕ :=
  2000+100*(p.seed+p.commands+p.arguments+p.expression)

/-- Fixed numerical instruction allowances. Dynamic addresses enter only literal opcodes. -/
def rootFactor : ℕ := allowance (prices 1 addressTemplate)

open private pick seedList rd from OAI.ThreeFlat.RAM.TickTerminalRootRun

private theorem pick_price (i : Formula 1) (n : ℕ) (xs : List (Formula 1)) :
    (pick n xs i).work = (xs.map Formula.work).sum + xs.length*(i.work+2) + 1 := by
  induction xs generalizing n with
  | nil => simp [pick,Formula.work]
  | cons x xs ih =>
    simp only [pick,eqz,Formula.work,ih,List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    omega

private theorem seed_uniform (W : ℕ) (A : Arena) :
    (HeaderScan.closed (w:=W) (boot A)).binds=(HeaderScan.closed (w:=1) (boot addressTemplate)).binds := by
  have cols : (seedList A).map Formula.work=(seedList addressTemplate).map Formula.work := by
    simp only [seedList,List.map_cons,List.map_nil,rd,add,mul,Formula.work]
  have count : (seedList A).length=(seedList addressTemplate).length := rfl
  simp only [HeaderScan.binds_closed,boot,pick_price,cols,count,Formula.work]

private theorem generator_price (W : ℕ) (A : Arena) (cmd : Bool) :
    (generator W A cmd).binds=(formula cmd).work+∑ i : Fin 13, if i=0 then 1 else if i=5 then 2 else 1 := by
  let lower := if cmd then A.commands else A.arguments
  let args (i : Fin 13) : Term W 0 1 :=
    if i=0 then .literal ((A.seed+8:ℕ):Word W)
    else if i=5 then .binary .sub (.result 0) (.literal (lower:Word W)) else .literal 0
  have arg (i : Fin 13) : (args i).binds=(if i=0 then 1 else if i=5 then 2 else 1) := by
    by_cases head : i=0 <;> by_cases row : i=5 <;>
      simp only [args,head,row,show (5:Fin 13)≠0 by decide,ite_true,ite_false,Term.binary,Term.literal,Term.binds_letThen,Term.binds_rename,Term.binds]
  exact (Term.binds_instantiate (HeaderScan.closed (w:=W) (formula cmd)) args).trans
    (congrArg₂ Nat.add (HeaderScan.binds_closed (formula cmd)) (Finset.sum_congr rfl (fun i _ => arg i)))

private theorem generator_uniform (W : ℕ) (A : Arena) (cmd : Bool) :
    (generator W A cmd).binds=(generator 1 addressTemplate cmd).binds :=
  (generator_price W A cmd).trans (generator_price 1 addressTemplate cmd).symm

private theorem priced (s c a e h v : ℕ) :
    (4+26*(2*s+4)) + (13+(7*(h+2))*(2*c+4)) +
      (13+(7*(h+2))*(2*a+4)) + (6+19*(h+2)+v*(2*e+4)) + (6+5*4) ≤
      (2000+100*(s+c+a+e))*(1+h+v) := by
  ring_nf
  omega

private def stepCost (p : Prices) (h v : ℕ) : ℕ :=
  (4+26*(2*p.seed+4)) + (13+(7*(h+2))*(2*p.commands+4)) +
    (13+(7*(h+2))*(2*p.arguments+4)) + (6+19*(h+2)+v*(2*p.expression+4)) + (6+5*4)

private theorem prices_congr {s c a e s' c' a' e' : ℕ}
    (hs : s=s') (hc : c=c') (ha : a=a') (he : e=e') :
    Prices.mk s c a e = Prices.mk s' c' a' e' := by
  subst s'; subst c'; subst a'; subst e'; rfl

private theorem fixed_prices (W : ℕ) (A : Arena) : prices W A=prices 1 addressTemplate :=
  prices_congr (seed_uniform W A) (generator_uniform W A true)
    (generator_uniform W A false) (expression_uniform W)

private theorem oneCost_eq (W : ℕ) (A : Arena) (T : Root) (raw : ℕ→ℕ) :
    oneCost W A T raw = stepCost (prices W A) T.halves (TickTerminalPrimitive.words T raw) := rfl

private theorem repriced (p q : Prices) (n factor h v : ℕ)
    (eq : p=q) (actual : n=stepCost p h v) (cap : factor=allowance q) :
    n ≤ factor*(1+h+v) := by
  subst q
  subst n
  subst factor
  exact priced p.seed p.commands p.arguments p.expression h v

theorem work_bound (W : ℕ) (A : Arena) (T : Root) (raw : ℕ→ℕ) :
    oneCost W A T raw≤rootFactor*(1+T.halves+TickTerminalPrimitive.words T raw) :=
  repriced (prices W A) (prices 1 addressTemplate) (oneCost W A T raw) rootFactor
    T.halves (TickTerminalPrimitive.words T raw) (fixed_prices W A) (oneCost_eq W A T raw) rfl

end ThreeFlat.RAM.TickTerminalRoot

end
end OAI
