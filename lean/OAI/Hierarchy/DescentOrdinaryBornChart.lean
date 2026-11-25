import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Fixed ordinary-date storage for all original newborn p-words -/
namespace Hierarchy.DescentOrdinaryBorn
open DescentSIMDLookup ProtocolRAM
structure Chart where
  blocks : ℕ
  cap : ℕ
  names : ℕ
  widths : ℕ
  bits : ℕ
  args : ℕ
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  grain : ℕ
  scale : ℕ
  demand : ℕ

namespace Chart
variable (B : Chart)
def donors := B.blocks*B.cap
def chipBits := (4+5*(3+1+B.names)+10*B.widths)*B.donors
def fields := ((B.donors*6)*B.args)*7
def rows := B.hosts*chunks B.groups B.lanes
def pitch := 2^Nat.clog 2 B.rows
def bookWords := (1+B.fields)*(2*2^((B.chipBits*1+B.chipBits)*B.lanes))
def output (base : ℕ) := base+B.bookWords
def endAddress (base : ℕ) := B.output base+B.fields*B.pitch
def index : (((Fin B.donors×Fin 6)×Fin B.args)×Fin 7) ≃ Fin B.fields :=
  (Equiv.prodCongr ((Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv) (Equiv.refl _)).trans finProdFinEquiv
def bank (base : ℕ) (x : Fin B.blocks) (t : Fin B.cap) (j : Fin 6) (a : Fin B.args) (f : Fin 7) : Bank :=
  ⟨B.output base+(B.index (((finProdFinEquiv (x,t),j),a),f)).val*B.pitch,Nat.clog 2 B.rows⟩
theorem affine (base : ℕ) : B.endAddress base=base+B.endAddress 0 := by simp [endAddress,output, Nat.add_assoc]
theorem order (base : ℕ) : base≤B.output base ∧ B.output base≤B.endAddress base:=⟨Nat.le_add_right ..,Nat.le_add_right ..⟩
theorem seats : B.rows≤B.pitch :=Nat.le_pow_clog (by decide) _
end Chart
end Hierarchy.DescentOrdinaryBorn

end OAI
