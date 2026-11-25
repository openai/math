import OAI.Optimization.LinearProgramming.RAM.FrameHeaders
import OAI.Optimization.LinearProgramming.RAM.Array
import OAI.Optimization.LinearProgramming.Geometry.GramEncoding

/-! Header for the final primal solve. The right side occupies the first m entries,
followed by the d rows of Aᵀ. The original LP and the recovered w remain readable. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PrimalOutput
open RAM RAM.Tape RAM.Call

def tableauBase (w m : ℕ) := w+(m+1)
def pointBase (w m d : ℕ) := tableauBase w m+(d+1)*m+1

private def headers : HeaderPlan 225 :=
  let m : AddressTerm 225:=.reg 28
  let d : AddressTerm 225:=.reg 29
  let raw : AddressTerm 225:=.reg 24
  let w : AddressTerm 225:=.reg 212
  [(220,raw+m*d),(221,w+1),(222,w+(m+1)),(55,.reg 222),(56,(d+1)*m),(57,.val 208),(58,.val 2),
    (208,d+1),(209,m),(210,(.reg 222)+(.reg 56)+1),(211,d),(14,.val 0),(31,d),(33,m),(35,(.reg 222)+m),(40,raw),(41,d)]

def headerBlock : Block:=HeaderPlan.code 230 headers
noncomputable def headerTime : Polynomial ℕ:=headers.budget

structure Header (m d raw w cap : ℕ) {K : Type*} (s : Memory K) : Prop where
  bSource : s.index 220=raw+m*d
  wSource : s.index 221=w+1
  rhsBase : s.index 222=tableauBase w m
  array : s.index 55=tableauBase w m
  words : s.index 56=(d+1)*m
  dimensionArray : s.index 57=208
  dimensionWords : s.index 58=2
  capacity : s.index 60=cap
  solverRows : s.index 208=d+1
  solverColumns : s.index 209=m
  destination : s.index 210=pointBase w m d
  objectiveWidth : s.index 211=d
  zero : s.index 14=0
  rows : s.index 31=d
  columns : s.index 33=m
  transpose : s.index 35=tableauBase w m+m
  matrix : s.index 40=raw
  stride : s.index 41=d
  originalRows : s.index 28=m

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem header_run (P : K→Prop) (s : Memory K) (m d raw w cap limit : ℕ) (good : s.AllData P)
    (i24 : s.index 24=raw) (i28 : s.index 28=m) (i29 : s.index 29=d) (i212 : s.index 212=w)
    (i60 : s.index 60=cap) (bounded : ∀j,s.index j ≤ limit) :
    ∃ t c,c ≤ headerTime.eval limit ∧ Block.Eval (Memory.AllData P) headerBlock s c t ∧
      Header m d raw w cap t ∧ t.data=s.data := by
  let env:=fun j : Fin 225=>s.index j.val
  obtain ⟨t,c,evaluated,clock,data,ind⟩:=headers.correct 230 (by decide) s env (fun _=>rfl) good
  have regs : Header (s.index 28) (s.index 29) (s.index 24) (s.index 212) (s.index 60)
      (⟨t.data,fun j=>if hj : j < 225 then headers.output env ⟨j,hj⟩ else t.index j⟩ : Memory K) :=
    ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  rw [i24,i28,i29,i212,i60] at regs
  have atReg (j : Fin 225) : t.index j.val=(if hj : j.val < 225 then headers.output env ⟨j.val,hj⟩ else t.index j.val) := by
    simpa only [dite_eq_left j.isLt] using ind j
  refine ⟨t,c,clock.trans (headers.cost_le _ _ (fun j=>bounded j.val)),evaluated,?_,data⟩
  exact ⟨(atReg 220).trans regs.bSource,(atReg 221).trans regs.wSource,(atReg 222).trans regs.rhsBase,
    (atReg 55).trans regs.array,(atReg 56).trans regs.words,(atReg 57).trans regs.dimensionArray,(atReg 58).trans regs.dimensionWords,
    (atReg 60).trans regs.capacity,(atReg 208).trans regs.solverRows,(atReg 209).trans regs.solverColumns,
    (atReg 210).trans regs.destination,(atReg 211).trans regs.objectiveWidth,(atReg 14).trans regs.zero,
    (atReg 31).trans regs.rows,(atReg 33).trans regs.columns,(atReg 35).trans regs.transpose,
    (atReg 40).trans regs.matrix,(atReg 41).trans regs.stride,(atReg 28).trans regs.originalRows⟩

end PrimalOutput
end Recovery
end LinearProgramming
end Optimization
end OAI
