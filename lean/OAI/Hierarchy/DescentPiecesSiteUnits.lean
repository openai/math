import OAI.Hierarchy.DescentStageUnitCap

namespace OAI
/-! # Preserving each physical endpoint column under core unbundling -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open DescentCableUnbundling
open scoped Classical BigOperators
noncomputable section
variable {F : Type*} [Field F] {d : ℕ} {P Atom : Type*} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (q : ℕ) (m : W.graph.Edge→ℕ) (fit : ∀e∈W.core,W.graph.width e=m e*q)
local notation "Z" => W.pieces q m fit
local notation "origin" => original W.graph W.core m

omit [Field F] in
/-- A core cable is replaced by `m e` copies of width `q`, each with the same old endpoint. -/
theorem pieces_weighted (weight : W.graph.Edge→ℕ) :
    (∑e : (Z).graph.Edge,weight (origin e)*(Z).graph.width e)=∑e : W.graph.Edge,weight e*W.graph.width e := by
  classical
  let debit (e : W.graph.Edge) := weight e*W.graph.width e
  change (∑e : ({e : W.graph.Edge // e∉W.core} ⊕ Row W.graph W.core m),
    weight (origin e)*(network W.graph W.core m q).width e)=_
  rw [Fintype.sum_sum_type,Fintype.sum_sigma]
  have cores : (∑t : {e : W.graph.Edge // e∈W.core},∑_j : Fin (m t.val),weight t.val*q)=
      ∑t : {e : W.graph.Edge // e∈W.core},debit t.val := by
    apply Finset.sum_congr rfl;intro t _
    simp [debit,fit t.val t.property,mul_comm,mul_left_comm]
  change (∑t : {e : W.graph.Edge // e∉W.core},debit t.val)+
    (∑t : {e : W.graph.Edge // e∈W.core},∑_j : Fin (m t.val),weight t.val*q)=_
  rw [cores,←Finset.sum_subtype W.core (fun _=>Iff.rfl) debit,
    ←Finset.sum_subtype W.coreᶜ (fun _=>Finset.mem_compl) debit]
  exact Finset.sum_compl_add_sum W.core debit

omit [Field F] in
theorem pieces_siteUnits (hub : W.graph.Site→Bool) (rec : W.graph.Site→List Atom)
    (wire β hist : ℕ) (v : W.graph.Site) :
    (Z).siteUnits hub rec wire β hist v=W.siteUnits hub rec wire β hist v := by
  let credit (endpoint : W.graph.Edge→W.graph.Site) (e : W.graph.Edge) :=
    if v=endpoint e then wire*(if hub (endpoint e) then β else 1) else 0
  have algebra (endpoint : W.graph.Edge→W.graph.Site) (e : W.graph.Edge) (n : ℕ) :
      (if v=endpoint e then wire*n*(if hub (endpoint e) then β else 1) else 0)=credit endpoint e*n := by
    by_cases h : v=endpoint e <;> simp [h,credit,mul_right_comm]
  unfold siteUnits
  change (∑e : (Z).graph.Edge,if v=W.graph.src (origin e) then wire*(Z).graph.width e*(if hub (W.graph.src (origin e)) then β else 1) else 0)+
      (∑e : (Z).graph.Edge,if v=W.graph.dst (origin e) then wire*(Z).graph.width e*(if hub (W.graph.dst (origin e)) then β else 1) else 0)+_= _
  simp_rw [algebra W.graph.src,algebra W.graph.dst]
  rw [pieces_weighted,pieces_weighted]

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
