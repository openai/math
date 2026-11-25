import OAI.Hierarchy.DescentOperandInputCast
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # Shared lane conversions for the original root, coordinate and halo words -/
namespace Hierarchy.DescentOperandPublicCasts
open DescentSIMDLookup DescentPackedZip ProtocolRAM DescentDatedAddressBook
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Plan where
  rootBits : ℕ
  stemBits : ℕ
  metaBits : ℕ
  bits : ℕ
  lanes : ℕ

namespace Plan
variable (P : Plan)
def width (i : Fin 3) := if i=0 then P.rootBits else if i=1 then P.stemBits else P.metaBits
def bound :=max P.rootBits (max P.stemBits P.metaBits)
theorem small (i : Fin 3) : P.width i≤P.bound :=by
  unfold width bound
  split_ifs <;> omega
def words :=3*(2*2^(P.bound*P.lanes))
def ticks :=4+10*P.words
def endAddress (base : ℕ) :=base+P.words
def program (base w : ℕ) :=DescentOperandInputCast.program P.width P.bits P.bound P.lanes base w
def image {w : ℕ} (base : ℕ) (m : Memory w) :=DescentOperandInputCast.image P.width P.bits P.bound P.lanes base m
def expr (base : ℕ) (i : Fin 3) (s : Expr) :=DescentOperandInputCast.expr P.width P.bits P.bound P.lanes base i s

theorem any {w} (base : ℕ) (m : Memory w) (room : P.endAddress base<2^w) :
    (P.program base w).Exec m (P.image base m) P.ticks ∧ CheapCode (P.program base w) ∧
    (∀z,z<base ∨ P.endAddress base≤z→P.image base m z=m z) :=
  let r:=DescentOperandInputCast.any P.width P.bits P.bound P.lanes base m P.small room
  ⟨r.1,r.2.1,r.2.2.1⟩

theorem issued {w H G} (base : ℕ) (i : Fin 3) (s : Expr) (m : Memory w)
    (x : Fin H→Fin G→Cell (P.width i)) (fit : s.Fits w base) (held : Source s x P.lanes m)
    (room : P.endAddress base<2^w) :
    (P.expr base i s).Fits w (P.endAddress base) ∧
    Source (P.expr base i s) (fun h g=>((x h g).val : Cell P.bits)) P.lanes (P.image base m) :=
  DescentOperandInputCast.issued P.width P.bits P.bound P.lanes base i s m x P.small fit held room

theorem extent (base : ℕ) : P.endAddress base=base+P.endAddress 0 := by simp [endAddress]

open Filter in
theorem rate {ι : ℕ→Type*} (p : ∀h,ι h→Plan)
    (expBound : ∃A : ℕ,∀ᶠ h:ℕ in atTop,∀i,(p h i).bound*(p h i).lanes≤A*h) :
    Bounded (fun h i=>(p h i).endAddress 0) ∧ Bounded (fun h i=>(p h i).ticks) :=by
  rcases expBound with ⟨A,cover⟩
  have a:= (Bounded.const (ι:=ι) 3).mul ((Bounded.const (ι:=ι) 2).mul (Bounded.pow_of_linear cover))
  exact ⟨by simpa only [endAddress,Nat.zero_add,words] using a,
    (Bounded.const 4).add ((Bounded.const 10).mul a)⟩

end Plan
end
end Hierarchy.DescentOperandPublicCasts

end OAI
