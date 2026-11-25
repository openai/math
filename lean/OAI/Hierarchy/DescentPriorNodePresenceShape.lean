import OAI.Hierarchy.DescentPackedUnaryPages
import OAI.Hierarchy.DescentOrdinaryRoleRetile

namespace OAI
/-! All occupied recipe nodes under the original positive role token convention. -/
namespace Hierarchy.DescentPriorNodePresence
open DescentSIMDLookup DescentSixParty.Chronology ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
structure Chart where
  blocks : ℕ
  nodes : ℕ
  hosts : ℕ
  groups : ℕ
  tokenBits : ℕ
  bits : ℕ
  roleLanes : ℕ
  operandLanes : ℕ
namespace Chart
variable (C : Chart)
def presence (val : Cell (C.tokenBits*C.nodes)) (_ : Cell 0) : Cell (1*C.nodes):=
  encode 1 C.nodes (fun j=>if ((encode C.tokenBits C.nodes).symm val j).val=0 then 0 else 1)
def expand (val : Cell (1*C.nodes)) (_ : Cell 0) : Cell (C.bits*C.nodes):=
  encode C.bits C.nodes (fun j=>(((encode 1 C.nodes).symm val j).val : Cell C.bits))
private theorem zero_encoded (a n : ℕ) : encode a n (fun _=>0)=0:=by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin n=>(0:Cell a))).val=0
  simp []
theorem presence_zero : C.presence 0 0=0:=by
  have z:=(encode C.tokenBits C.nodes).symm_apply_eq.mpr (zero_encoded C.tokenBits C.nodes).symm
  simp [presence,z,zero_encoded]
theorem expand_zero : C.expand 0 0=0:=by
  have z:=(encode 1 C.nodes).symm_apply_eq.mpr (zero_encoded 1 C.nodes).symm
  simp [expand,z,zero_encoded]
def readings (v : Cell (C.tokenBits*C.nodes)):=C.expand (C.presence v 0) 0
theorem at_node (v : Cell (C.tokenBits*C.nodes)) (j : Fin C.nodes):
    (encode C.bits C.nodes).symm (C.readings v) j=if ((encode C.tokenBits C.nodes).symm v j).val=0 then 0 else 1:=by
  simp only [readings,expand,presence,Equiv.symm_apply_apply]
  split <;>rfl
def mask : DescentPackedUnaryPages.Shape:=⟨C.blocks,C.hosts,C.groups,C.roleLanes,C.tokenBits*C.nodes,1*C.nodes⟩
def convert : DescentOrdinaryRoleRetile.Layout:=⟨C.blocks,C.hosts,C.groups,C.roleLanes,C.operandLanes,1*C.nodes⟩
def pages : DescentPackedUnaryPages.Shape:=⟨2*C.blocks,C.hosts,C.groups,C.operandLanes,1*C.nodes,C.bits*C.nodes⟩
def maskEnd (base : ℕ):=C.mask.finish base
def tileEnd (base : ℕ):=C.convert.roof (C.maskEnd base)
def out (base : ℕ):=C.pages.start (C.tileEnd base)
def endAddress (base : ℕ):=C.pages.finish (C.tileEnd base)
def rows:=C.hosts*chunks C.groups C.operandLanes
def bank (base : ℕ) (f : Fin 2) (x : Fin C.blocks):=C.pages.bank (C.tileEnd base) (finProdFinEquiv (f,x))
def input (base : ℕ) (arity : Fin C.blocks→Bank) (j : Fin (2*C.blocks)):Bank:=
  let p:Fin 2×Fin C.blocks:=finProdFinEquiv.symm j
  if p.1=0 then C.convert.bank (C.maskEnd base) p.2 else arity p.2
def test (j : Fin (2*C.blocks)):Bool:=decide ((finProdFinEquiv.symm j : Fin 2×Fin C.blocks).1=0)
def phase (base : ℕ) (role arity : Fin C.blocks→Bank) (w : ℕ) : NativePhase w:=
  ((C.mask.phase C.presence base role (fun _=>true) w).seq
    (C.convert.phase (C.maskEnd base) (C.mask.bank base) w)).seq
    (C.pages.phase C.expand (C.tileEnd base) (C.input base arity) C.test w)
def program (base : ℕ) (role arity : Fin C.blocks→Bank) (w : ℕ):=(C.phase base role arity w).program
theorem translated (base : ℕ) : C.endAddress base=base+C.endAddress 0:=by
  unfold endAddress tileEnd maskEnd
  rw [C.pages.translated (C.convert.roof (C.mask.finish base)),C.pages.translated (C.convert.roof (C.mask.finish 0)),
    C.convert.translated (C.mask.finish base),C.convert.translated (C.mask.finish 0),C.mask.translated base]
  omega
theorem lower (base : ℕ) : base≤C.endAddress base:=by rw [C.translated];exact Nat.le_add_right ..
theorem starts (base : ℕ) : base≤C.maskEnd base ∧ C.maskEnd base≤C.tileEnd base ∧ C.tileEnd base≤C.out base ∧
    C.out base≤C.endAddress base:=⟨C.mask.base_le base,C.convert.base_le _,Nat.le_add_right ..,
      (Nat.le_add_right ..).trans (Nat.le_add_right ..)⟩
theorem upper (base : ℕ) : C.endAddress base=C.out base+(2*C.blocks)*C.rows+2^Nat.clog 2 (C.rows+1):=rfl
theorem address (base : ℕ) (f : Fin 2) (x : Fin C.blocks) :
    (C.bank base f x).base=C.out base+(f.val*C.blocks+x.val)*C.rows:=by
  simp only [bank,DescentPackedUnaryPages.Shape.bank,finProdFinEquiv_apply_val,out,rows,pages,
    DescentPackedUnaryPages.Shape.rows,Nat.add_comm,Nat.mul_comm]
end Chart
end
end Hierarchy.DescentPriorNodePresence

end OAI
