import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # Physical row addresses for the two permanent node metadata fields -/
namespace Hierarchy.DescentDatedNodeMetadata
open DescentSIMDLookup ProtocolRAM
noncomputable section
structure Chart where
  blocks : ℕ
  nodes : ℕ
  hosts : ℕ
  groups : ℕ
  bits : ℕ
  lanes : ℕ
namespace Chart
variable (v : Chart)
def names:=2*v.blocks
def jobs:=v.names*v.nodes
def rows:=v.hosts*chunks v.groups v.lanes
def rounded:=2^Nat.clog 2 (v.rows+1)
def slot (f : Fin 2) (x : Fin v.blocks) : Fin v.names:=finProdFinEquiv (f,x)
def job (f : Fin 2) (x : Fin v.blocks) (n : Fin v.nodes) : Fin v.jobs:=finProdFinEquiv (v.slot f x,n)
def scalarEnd (base : ℕ):=base+v.jobs*v.rows
def dictionary:=(v.nodes+1)*2^((v.bits*v.nodes+v.bits)*v.lanes)
def output (base : ℕ):=v.scalarEnd base+max v.dictionary v.rounded
def endAddress (base : ℕ):=v.output base+v.names*v.rows+v.rounded
def bank (base : ℕ) (f : Fin 2) (x : Fin v.blocks) : Bank:=
  ⟨v.output base+(v.slot f x).val*v.rows,Nat.clog 2 (v.rows+1)⟩
def seedBank (base : ℕ) (f : Fin 2) (x : Fin v.blocks) : Bank:=⟨base+(v.slot f x).val*v.rows,Nat.clog 2 (v.rows+1)⟩
def seedEnd (base : ℕ):=base+v.names*v.rows+v.rounded

/-- Shared paid-count and positive-span dictionaries; the source spans may use a distinct field width. -/
def inputsEnd (base payBits spanBits : ℕ) :=base+(v.nodes+1)*(2*2^(max payBits (spanBits+v.bits)*v.lanes))
def metadataEnd (base payBits spanBits : ℕ) :=v.endAddress (v.inputsEnd base payBits spanBits)
/-- The ordinary predecessor presents one vector of node digits per span field.
One finite local digit extractor is shared across every genuine argument. -/
def digitEnd (base spanBits : ℕ) :=base+v.nodes*2^((spanBits*v.nodes)*v.lanes)
def ordinaryEnd (base payBits spanBits : ℕ) :=v.metadataEnd (v.digitEnd base spanBits) payBits spanBits

theorem translate (base : ℕ) : v.endAddress base=base+v.endAddress 0 :=by simp only [endAddress,output,scalarEnd,Nat.zero_add,Nat.add_assoc]
theorem seed_translate (base : ℕ) : v.seedEnd base=base+v.seedEnd 0 :=by simp only [seedEnd,Nat.zero_add,Nat.add_assoc]
end Chart
end
end Hierarchy.DescentDatedNodeMetadata

end OAI
