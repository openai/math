import OAI.Hierarchy.DescentOperandVectorArena
import OAI.Hierarchy.DescentDatedDonorArea

namespace OAI
/-! # The authentic seven-field argument vector at the end of the chosen ordinary donor pass -/
namespace Hierarchy
open DescentDatedAddressBook DescentSIMDLookup DescentVectorBookReshape Filter
noncomputable section
namespace DescentOperandVectorArena.Layout
variable {ι : ℕ→Type*}
structure ScalarRoom (L : ∀h,ι h→Layout) where
  operands : Bounded (fun h i=>(L h i).operands)
  normalized : Bounded (fun h i=>(L h i).normalizedRows)
  hosts : Bounded (fun h i=>(L h i).hosts)
  lows : Bounded (fun h i=>(L h i).lows)
  groups : Bounded (fun h i=>(L h i).groups)
  radix : Bounded (fun h i=>(L h i).radix)
  lanes : Bounded (fun h i=>(L h i).lanes)
  fit : ∃K : ℕ,∀ᶠ h:ℕ in atTop,∀i,let a:=L h i;
    a.stateBits≤K*h ∧ (a.bookBits*a.radix)*a.lanes≤K*h

theorem extent_rate (L : ∀h,ι h→Layout) (b : ScalarRoom L) : Bounded (fun h i=>(L h i).endAddress 0) := by
  obtain ⟨K,hw⟩:=b.fit
  have state:=Bounded.pow_of_linear (K:=K) (hw.mono fun h hh i=>(hh i).1)
  have book:=Bounded.pow_of_linear (K:=K) (hw.mono fun h hh i=>(hh i).2)
  have batch : Bounded (fun h i=>chunks (L h i).groups (L h i).lanes) :=
    (b.groups.add b.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have channels:=(Bounded.const 7).mul b.operands
  have chunk:=(b.hosts.mul b.lows).mul batch
  have archive:=channels.mul (b.lows.mul (b.hosts.mul batch))
  have output:=channels.mul (b.radix.mul chunk)
  have sheets:=b.radix.mul book
  have norm:=b.normalized
  have total:=((((((((Bounded.const 8).mul state).add (channels.mul norm)).add
    ((Bounded.const 2).mul norm)).add ((Bounded.const 2).mul archive)).add
    ((Bounded.const 3).mul sheets)).add ((Bounded.const 5).mul output)).add
    ((Bounded.const 2).mul chunk)).add (Bounded.const 20)
  apply total.of_le
  intro h i
  simpa only [Nat.zero_add,srcWords,dstWords,chunkRows,dictWords,pageCount,sourceWords,rows,dictionaryWords] using
    DescentOperandVectorArena.bound (L h i) 0

end DescentOperandVectorArena.Layout
end
end Hierarchy

end OAI
