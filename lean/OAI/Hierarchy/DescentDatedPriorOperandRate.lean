import OAI.Hierarchy.DescentDatedPriorOperand
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # All normalized prior-pointer scalar loads in the nonterminal ordinary branch -/
namespace Hierarchy.DescentDatedPriorOperand.Layout
open DescentDatedAddressBook DescentSIMDLookup Filter
variable {ι : ℕ→Type*}
structure ScalarRoom (l : ∀h,ι h→Layout) where
  blocks : Bounded (fun h i=>(l h i).blocks)
  nodes : Bounded (fun h i=>(l h i).nodes)
  arities : Bounded (fun h i=>(l h i).operands)
  hosts : Bounded (fun h i=>(l h i).hosts)
  groups : Bounded (fun h i=>(l h i).groups)
  lanes : Bounded (fun h i=>(l h i).lanes)
  width : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,let v:=l h i;
    ((v.size+2)*v.nodes)*v.lanes≤K*h ∧ (11*(v.size+2))*v.lanes≤K*h

theorem extent_rate (l : ∀h,ι h→Layout) (b : ScalarRoom l) : Bounded (fun h i=>(l h i).endAddress 0) := by
  obtain ⟨K,fit⟩:=b.width
  have table:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).1)
  have decoder:=Bounded.pow_of_linear (K:=K) (fit.mono fun h hh i=>(hh i).2)
  have join : Bounded (fun h i=>(l h i).splicePage) := by
    apply decoder.of_le
    intro h i
    apply Nat.pow_le_pow_right (by decide)
    apply Nat.mul_le_mul_right
    omega
  have batch : Bounded (fun h i=>chunks (l h i).groups (l h i).lanes) :=
    (b.groups.add b.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows_ : Bounded (fun h i=>(l h i).rows) :=b.hosts.mul batch
  have rowCap : Bounded (fun h i=>(l h i).rowCap) :=(rows_.add (Bounded.const 1)).padded
  have span : Bounded (fun h i=>(l h i).span) :=rows_.padded
  have print:=b.nodes.mul table
  have used:=(((Bounded.const 7).mul b.arities).mul b.nodes).mul rows_
  have prices:=((((((print.add used).add rowCap).add ((Bounded.const 4).mul join)).add
    ((Bounded.const 2).mul span)).add ((Bounded.const 12).mul decoder)).add ((Bounded.const 3).mul rowCap))
  simpa only [endAddress,Nat.zero_add,jobs,siteWords,dictionary,columns,resolverPage] using
    (b.blocks.mul (b.nodes.mul b.arities)).mul prices

end Hierarchy.DescentDatedPriorOperand.Layout

end OAI
