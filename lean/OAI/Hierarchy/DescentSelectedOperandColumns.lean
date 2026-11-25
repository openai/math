import OAI.Hierarchy.DescentRetainedOperandDateTables
import OAI.Hierarchy.DescentPhysicalOperandLaneSum
import OAI.Hierarchy.DescentResetRetainedCableValue

namespace OAI
/-! Query and all seven operand columns at the same physical output of the native lookup books. -/
namespace Hierarchy.DescentResetOperandSetup.Chart
open ProtocolRAM DescentPackedZip DescentSIMDLookup DescentOperandFamilyBook DescentResetOperandSetup
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (C : DescentResetOperandSetup.Chart) {H G w : ℕ} (base : ℕ) (s : C.Sources) (f : C.Laws)
  (m : Memory w) (x : Fin C.placement.blocks) (arg : Fin C.retained.args) (node : Fin C.retained.nodes)
  (old : Fin C.inputs→Expr) (rotor : Fin 4→Expr) (surface : Fin C.fallbackInputs→Expr)
set_option quotPrecheck false
local notation "mem" => (C.code base w s f).image m
local notation "j" => (finProdFinEquiv (arg,node) : Fin C.members)
local notation "cable" => C.cable

private theorem packedZero (b M : ℕ) (m : Memory w) :
    Source (.lit 0) (fun (_ : Fin H) (_ : Fin G)=>(0:Cell b)) M m:=by
  intro row
  change (0:Word w)=((data (fun (_:Fin H) (_:Fin G)=>(0:Cell b)) row).val:Word w)
  have zero : (data (fun (_:Fin H) (_:Fin G)=>(0:Cell b)) row).val=0:=by
    change (finFunctionFinEquiv (fun i:Fin M=>if _ : row.2.val*M+i.val<G then (0:Cell b) else 0)).val=0
    simp
  simp [zero]

theorem selected_query (row : Fin H→Fin G→(cable).Input) (private_ public_ target : Values H G C.queryBits)
    (space : C.endAddress base<2^w) (fit : ∀i,(old i).Fits w (C.casts base))
    (seen : ∀i,Source (old i) (fun h g=>row h g i) C.lanes mem)
    (priv : Source (expr f.rotorQuery C.lanes (C.rotorQuery base) j rotor) private_ C.lanes mem)
    (pub : Source (expr f.fallbackQuery C.lanes (C.fallbackQuery base) j surface) public_ C.lanes mem)
    (owner : ∀h g,(target h g=(cable).query (row h g) ∧ private_ h g=0 ∧ public_ h g=0) ∨
      ((cable).query (row h g)=0 ∧ target h g=private_ h g ∧ public_ h g=0) ∨
      ((cable).query (row h g)=0 ∧ private_ h g=0 ∧ target h g=public_ h g)) :
    Source (C.selected base f none x arg node old rotor surface) target C.lanes mem:=by
  exact select_three _ _ _ _ _ _ _ _ ((C.carried_pages base s f m space old row fit seen).1.2) priv pub owner

theorem selected_field (field : Fin 7) (row : Fin H→Fin G→(cable).Input)
    (prior private_ public_ target : Values H G C.fieldBits)
    (space : C.endAddress base<2^w) (fit : ∀i,(old i).Fits w (C.casts base))
    (seen : ∀i,Source (old i) (fun h g=>row h g i) C.lanes mem)
    (previous : Source (C.oldValue base x arg node field) prior C.lanes mem)
    (priv : Source (expr f.rotorFields C.lanes (C.rotorFields base) (finProdFinEquiv (field,j)) rotor) private_ C.lanes mem)
    (pub : Source (expr f.fallbackFields C.lanes (C.fallbackFields base) (finProdFinEquiv (field,j)) surface) public_ C.lanes mem)
    (total : ∀h g,(target h g).val=(prior h g).val+((cable).priceField field (row h g)).val+
      (private_ h g).val+(public_ h g).val) :
    Source (C.selected base f (some field) x arg node old rotor surface) target C.lanes mem:=by
  let ce:=if field=2 ∨ field=3 then expr (cable).prices C.lanes (C.find base) (if field=2 then 0 else 1) old else .lit 0
  let amount:=fun h g=>(cable).priceField field (row h g)
  have costs:= (C.carried_pages base s f m space old row fit seen).2
  have selectedCost : Source ce amount C.lanes mem:=by
    by_cases two:field=2
    · simpa [ce,amount,DescentResetRetainedCableLaw.Shape.priceField,two] using (costs 0).2
    by_cases three:field=3
    · simpa [ce,amount,DescentResetRetainedCableLaw.Shape.priceField,three] using (costs 1).2
    · simpa [ce,amount,DescentResetRetainedCableLaw.Shape.priceField,two,three] using
        (packedZero (H:=H) (G:=G) (cable).fieldBits C.lanes mem)
  have bound (h g) := (target h g).isLt
  let oldPart : Values H G C.fieldBits:=fun h g=>⟨(prior h g).val+(amount h g).val,by
    have := total h g;have := bound h g;dsimp [amount];omega⟩
  let newPart : Values H G C.fieldBits:=fun h g=>⟨(private_ h g).val+(public_ h g).val,by
    have := total h g;have := bound h g;omega⟩
  exact sum_source mem target oldPart newPart _ _
    (sum_source mem oldPart prior amount _ _ previous selectedCost (fun _ _=>rfl))
    (sum_source mem newPart private_ public_ _ _ priv pub (fun _ _=>rfl))
    (fun h g=>by simpa [oldPart,newPart,amount,Nat.add_assoc] using total h g)

end
end Hierarchy.DescentResetOperandSetup.Chart

end OAI
