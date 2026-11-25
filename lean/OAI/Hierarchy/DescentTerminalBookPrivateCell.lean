import OAI.Hierarchy.DescentTerminalBookExteriorCount

namespace OAI
/-! # A resident cable grain has exactly one physical input coordinate -/
namespace Hierarchy.DescentTerminalLocalPortBook.Board
open DescentSixParty DescentCompiler DescentSharedCableNames DescentColonies DescentChosenRouter
open DescentTerminalPortChart DescentTerminalPeerChronology DescentTerminalPointerDigits
open DescentKernelHistory DescentTerminalGraphRows Computability.BorderVNP.Crossing
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

variable {F P V : Type} [Field F] [Fintype P] [Fintype V] [DecidableEq V] {groups d k i p scale:ℕ}
    {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F} {price ε:ℝ}
    (A:GroupStage W G price ε (Fin groups) V k) (S:AtomSchedule) (ready:A.StateBounds S i)
    (native:W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (names:Stage.Host (Fin groups) V k↪ℕ)
    (coords:Function.Injective (fun s=>(A.pos s,A.block s))) (v:W.graph.Site) (pin:Attached W.graph v↪ℕ)
    (hp:0<p) (whole:A.z*G.b=scale*p)
local notation "ord" => native.trans Fin.valEmbedding
local notation "cell" => Stage.home A v
local notation "panel" => Stage.signedPanel A ord S ready names cell
local notation "info" => Stage.live A ord S ready names cell
local notation "labels" => DescentTerminalPortChart.rank A ord S ready names v pin
local notation "index" => number W.graph p v labels

include coords in
omit [Fintype P] in
theorem recover_incident (u:A.CellPorts (cell).1.1 (cell).1.2 (cell).2) :
    ∃e:Incident W.graph v,∃j:Fin (A.grainCount e.val),Stage.recover A cell u=⟨e.val,j⟩ := by
  rcases u with ⟨⟨e,ep,eb⟩,j⟩|⟨⟨e,ep,eb⟩,j⟩
  · exact ⟨⟨e,Or.inl (coords (Prod.ext ep eb))⟩,j,rfl⟩
  · exact ⟨⟨e,Or.inr (coords (Prod.ext ep eb))⟩,j,rfl⟩

omit [Fintype P] in
theorem port_for (e:Incident W.graph v) (j:Fin (A.grainCount e.val)) :
    ∃u:A.CellPorts (cell).1.1 (cell).1.2 (cell).2,Stage.recover A cell u=⟨e.val,j⟩ := by
  rcases e.property with hs|ht
  · exact ⟨.inl ⟨⟨e.val,congrArg A.pos hs,congrArg A.block hs⟩,j⟩,rfl⟩
  · exact ⟨.inr ⟨⟨e.val,congrArg A.pos ht,congrArg A.block ht⟩,j⟩,rfl⟩

include ready hp whole in
omit [Fintype P] in
theorem fine_word (e:Incident W.graph v) (j:Fin (A.grainCount e.val)) (l:Fin scale) :
    j.val*scale+l.val<poolBatchCount (W.graph.width e.val) p := by
  rw [repetitions A S ready hp scale whole]
  have hi:=Nat.mul_le_mul_right scale j.isLt
  rw [Nat.succ_mul] at hi
  omega

omit [Fintype P] in
theorem live_slot (s:Fin (2*A.cap)) (z:Stage.Live A.degree A.cap) (hit:panel s=some z) :
    ∃u:A.CellPorts (cell).1.1 (cell).1.2 (cell).2,info u=z := by
  by_cases yes:∃u,Stage.signed A ord S ready (cell).1 (cell).2 u=s
  · obtain ⟨u,rfl⟩:=yes
    exact ⟨u,Option.some.inj ((Stage.signed_read A ord S ready names cell u).symm.trans hit)⟩
  · rw [Stage.signed_empty A ord S ready names cell s (not_exists.mp yes)] at hit
    contradiction

include coords hp whole in
theorem choose_live (e:Incident W.graph v) (j:Fin (poolBatchCount (W.graph.width e.val) p)) :
    ∃(s:Fin (2*A.cap)) (z:Stage.Live A.degree A.cap) (l:Fin scale),
      panel s=some z ∧ operandOffset panel z scale l.val=(index ⟨.inl e,j⟩).val := by
  have small : j.val < A.grainCount e.val * scale :=
    lt_of_lt_of_eq j.isLt (repetitions A S ready hp scale whole e.val)
  have pos:0<scale:=by by_contra! zero;have :=Nat.eq_zero_of_le_zero zero;simp_all
  let u:Fin (A.grainCount e.val):=⟨j.val/scale,(Nat.div_lt_iff_lt_mul pos).2 small⟩
  let l:Fin scale:=⟨j.val%scale,Nat.mod_lt _ pos⟩
  obtain ⟨a,match_⟩:=port_for A v e u
  have num:=cable_operand_read A S ready native names coords v pin hp whole a e u match_ l
  have arg:(⟨u.val*scale+l.val,fine_word A S ready v hp whole e u l⟩ : Fin (poolBatchCount (W.graph.width e.val) p))=j := by
    apply Fin.ext;simpa only [u,l,Nat.mul_comm (j.val/scale) scale] using Nat.div_add_mod j.val scale
  refine ⟨_, _, l, Stage.signed_read A ord S ready names cell a, ?_⟩
  exact num.trans (congrArg (fun q : Fin (poolBatchCount (W.graph.width e.val) p) =>
    (index ⟨.inl e, q⟩).val) arg)

include coords hp whole in
theorem candidate_word (s:Fin (2*A.cap)) (z:Stage.Live A.degree A.cap) (l:Fin scale) (hit:panel s=some z) :
    ∃(u:A.CellPorts (cell).1.1 (cell).1.2 (cell).2) (e:Incident W.graph v) (j:Fin (A.grainCount e.val)),
      info u=z ∧ Stage.recover A cell u=⟨e.val,j⟩ ∧
      operandOffset panel z scale l.val=(index ⟨.inl e,⟨j.val*scale+l.val,fine_word A S ready v hp whole e j l⟩⟩).val :=
  let ⟨u,eqn⟩:=live_slot A S ready native names v _ _ hit
  let ⟨e,j,match_⟩:=recover_incident A coords v u
  ⟨u,e,j,eqn,match_,eqn ▸ cable_operand_read A S ready native names coords v pin hp whole u e j match_ l⟩

omit [Field F] [Fintype P] in
private theorem partial_sum (w:Incident W.graph v→ℕ) (label:Incident W.graph v→ℕ) (e:Incident W.graph v) :
    (∑a:Incident W.graph v,if label a<label e then w a else 0)+w e≤∑a,w a := by
  let xs:=Finset.univ.filter fun a=>label a<label e
  have no:e∉xs:=by simp [xs]
  rw [←Finset.sum_filter]
  change (∑a∈xs,w a)+w e≤_
  rw [add_comm,←Finset.sum_insert no]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros;omega)

include coords hp whole in
theorem inside (e:Incident W.graph v) (j:Fin (poolBatchCount (W.graph.width e.val) p)) :
    (index ⟨.inl e,j⟩).val<(grains panel).card*scale := by
  obtain ⟨s,z,l,live,offset⟩:=choose_live A S ready native names coords v pin hp whole e j
  obtain ⟨a,edge,g,entry,recovered,val⟩:=candidate_word A S ready native names coords v pin hp whole s z l live
  subst z
  have truth:=grain_read A ord S ready names v a edge g recovered
  let base:=labels (.inl edge)
  have id:(grain (info a)).1=base:=by
    dsimp only [base]
    rw [positive_rank A ord S ready names v pin edge (Nat.zero_lt_of_lt g.isLt)]
    exact congrArg Prod.fst truth
  have within:(info a).within.val=g.val:=congrArg Prod.snd truth
  have cap:=partial_sum (W:=W) v (fun e=>A.grainCount e.val) (fun e=>labels (.inl e)) edge
  have pre:=lower_grains A ord S ready names v coords base pin
  rw [←pre,←all_grains A ord S ready names v coords] at cap
  have upper:=Nat.mul_le_mul_right scale cap
  have step:=Nat.mul_le_mul_right scale g.isLt
  rw [Nat.succ_mul] at step
  rw [Nat.add_mul] at upper
  rw [←offset,operandOffset,id,within]
  omega

end
end Hierarchy.DescentTerminalLocalPortBook.Board

end OAI
