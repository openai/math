import OAI.Hierarchy.DescentResetBlockFields
import OAI.Hierarchy.DescentBundleLanes
import OAI.Hierarchy.DescentLaneGates
import OAI.Hierarchy.DescentBundleWireArguments

namespace OAI
/-! # Every newly installed bank or relay argument reads an incident cable -/
namespace Hierarchy.DescentResetFreshWires
open DescentSixParty DescentKernelHistory DescentBundleHistory DescentLaneGates DescentOrderedWords
open DescentResetPointerFields DescentRouterBank DescentResetAttachments Computability.BorderVNP.Crossing
open scoped Classical
noncomputable section
variable {p d : ℕ} {P T : Type} {bits : P→ℕ} {N : Network d P bits}

section Install
variable {n k L Y : ℕ} {H Q : Type} [Fintype H] [Fintype Q] (base : Network n P bits)
    (home : base.Site→H) (group : Bool→base.Edge→Q)
    (bank : Network k (Bool×Q) (publicWidth group base.width)) (key : base.Edge↪Fin L)
    (whole : ∀e,p∣base.width e) (hp : 0<p)
local notation "graph_" => DescentResetTrunks.network base home group bank

omit [Fintype Q] in
/-- The ordered installer turns a bank's attached public socket into one selected
old stem and preserves a bank cable as the corresponding internal cable. -/
theorem bank_wire (v : bank.Site) (ref : BlockRef p (boundaryWidth bank v)) :
    ∃e : Incident (graph_) (.inr v),((bankBlockMap base home group bank key whole hp v).map ref).port=.inl e :=by
  let f:=bankField hp base home group bank key whole v ref
  have same : f=(bankBlockMap base home group bank key whole hp v).map ref :=firstBlock_eq hp _ _ ref
  rw [←same]
  suffices cable : ∃e,Sum.map Subtype.val Subtype.val f.port=Sum.inl e by
    obtain ⟨e,he⟩:=cable
    cases eqn : f.port with
    | inl a=>exact ⟨a,rfl⟩
    | inr a=>simp [eqn] at he
  rcases ref with ⟨a|socket,word,fit⟩
  · exact ⟨_,congrArg Prod.fst (bank_at_wire hp base home group bank key whole v a word fit)⟩
  · exact ⟨_,congrArg Prod.fst (bank_at_pin hp base home group bank key whole v socket word fit)⟩

omit [Fintype Q] in
theorem pulled_wires {U : Type} (v : bank.Site) {r : BitRecipe U (Boundary bank v) (boundaryWidth bank v)}
    (sh : Shape p r) (u : r.Node) (exposed : ∀j g i,∃ref,((sh.chunk u j g).get i)=.inl ref) :
    OnlyWires (N:=graph_) (v:=.inr v) (sh.reroute (bankBlockMap base home group bank key whole hp v)) u :=by
  intro j g i
  change IsWire (N:=graph_) (.inr v) (Sum.map _ id ((sh.chunk u j g).get i))
  obtain ⟨ref,read⟩:=exposed j g i
  obtain ⟨e,found⟩:=bank_wire base home group bank key whole hp v ref
  rw [read,Sum.map_inl]
  exact ⟨_,e,rfl,found⟩

omit [Fintype Q] in
theorem installed_wires (v : bank.Site) (program : Program Y p (boundaryWidth bank v))
    (units : Boundary bank v→ℕ) (lengths : ∀a,boundaryWidth bank v a=units a*p) (u : program.Node) :
    OnlyWires (N:=graph_) (v:=.inr v) ((ofProgram units lengths hp program).reroute (bankBlockMap base home group bank key whole hp v)) u :=by
  intro j g i
  let sh:=ofProgram units lengths hp program
  change IsWire (N:=graph_) (.inr v) (Sum.map _ id ((sh.chunk u j g).get i))
  cases pick : (sh.chunk u j g).get i with
  | inl ref=>
    obtain ⟨e,found⟩:=bank_wire base home group bank key whole hp v ref
    exact ⟨_,e,rfl,found⟩
  | inr h=>exact nomatch h.port

omit [Fintype Q] in
theorem relay_wires (h : H) (u : DescentNamedContact.Fibre (DescentResetTrunks.moved base home) h) :
    OnlyWires (N:=graph_) (v:=.inl (true,h)) (relayShape base home group bank key whole hp h) u :=by
  intro s j i
  by_cases back : s.val=0
  · simp [relayShape,back,Slice.whole,IsWire]
  · simp [relayShape,back,Slice.whole,IsWire]; exact u.property

end Install
end
end Hierarchy.DescentResetFreshWires

end OAI
