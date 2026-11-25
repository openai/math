import OAI.Hierarchy.DescentPackedFieldGather

namespace OAI
/-! # Physical counters, packed input and output addresses of one reset root -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section

structure RootArena where
  start : ℕ
  counters : ℕ
  rows : ℕ

namespace RootArena
def span (n : ℕ) := 2^(Nat.clog 2 n)
theorem le_span (n : ℕ) : n ≤ span n:=Nat.le_pow_clog (by decide) n
def stride (a : RootArena) := span a.counters+2*span a.rows
def first (a : RootArena) (i : ℕ) := a.start+a.stride*i
def middle (a : RootArena) (i : ℕ) := a.first i+span a.counters
def output (a : RootArena) (i : ℕ) := a.middle i+span a.rows
theorem end_row (a : RootArena) (i : ℕ) : a.output i+span a.rows=a.first (i+1) := by
  simp only [output,middle,first,Nat.mul_succ,stride]
  omega
end RootArena

structure RootTerms (N : ℕ) where
  tables : Fin N→Tables
  reads : Fin N→Expr
  menu : Banks

end
end Hierarchy.DescentSixParty.Chronology

end OAI
