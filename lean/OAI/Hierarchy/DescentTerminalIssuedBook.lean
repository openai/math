import OAI.Hierarchy.DescentTerminalRecipeRows
import OAI.Hierarchy.DescentTerminalLocalPortBook

namespace OAI
/-! # Readback from true chronological bundle lists in the local port record -/
namespace Hierarchy.DescentTerminalLocalPortBook
open DescentTerminalRecipeRows DescentTerminalBinPack DescentTerminalRouteRows Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.Routing CallPool
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {G V M A a W q : ℕ}

structure Room (t : Site) (G V M A : ℕ) : Prop where
  groups : t.groups≤G
  nodes : t.nodes≤V
  size : ∀g,t.size g≤M
  arity : ∀v,t.arity v≤A

def issue (t : Site) (f : Room t G V M A) (cables : t.Name→Word a) (args : t.Arg→Word a) : Book G V M A a where
  groupCount:=⟨t.groups,by have:=f.groups;omega⟩
  nodeCount:=⟨t.nodes,by have:=f.nodes;omega⟩
  groupSize g:=if h:g.val<t.groups then ⟨t.size ⟨g.val,h⟩,by have:=f.size ⟨g.val,h⟩;omega⟩ else 0
  nodeArity v:=if h:v.val<t.nodes then ⟨t.arity ⟨v.val,h⟩,by have:=f.arity ⟨v.val,h⟩;omega⟩ else 0
  portName g i:=if hg:g.val<t.groups then if hi:i.val<t.size ⟨g.val,hg⟩ then cables ⟨⟨g.val,hg⟩,⟨i.val,hi⟩⟩ else 0 else 0
  operand v i:=if hv:v.val<t.nodes then if hi:i.val<t.arity ⟨v.val,hv⟩ then args ⟨⟨v.val,hv⟩,⟨i.val,hi⟩⟩ else 0 else 0

variable (t : Site) (f : Room t G V M A) (cables : t.Name→Word a) (args : t.Arg→Word a)
local notation "book" => issue t f cables args
theorem size_live (g : Fin t.groups) : (book).size g=t.size g := by
  unfold Book.size
  dsimp only [issue]
  split
  · rfl
  · rename_i h
    exact (h g.isLt).elim
theorem arity_live (v : Fin t.nodes) : (book).arity v=t.arity v  := by
  unfold Book.arity
  dsimp only [issue]
  split
  · rfl
  · rename_i h
    exact (h v.isLt).elim

end
end Hierarchy.DescentTerminalLocalPortBook

end OAI
