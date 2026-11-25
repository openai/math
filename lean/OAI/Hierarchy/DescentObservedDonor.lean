import OAI.Hierarchy.DescentDonorChipLookup
import OAI.Hierarchy.DescentOrdinaryDonorSample
import OAI.Hierarchy.DescentPackedActorHeads

namespace OAI
/-! # Recover the ordinary private-volume donor from the resolved old addresses -/
namespace Hierarchy.DescentRawCablePanel
open DescentSIMDLookup DescentSixParty DescentSharedCableNames DescentCableDonorNames DescentHostDirectory
open Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing
noncomputable section

private theorem idxOf_map_test {U A B : Type*} [BEq A] [LawfulBEq A] [BEq B] [LawfulBEq B]
    (xs : List U) (u : U) (p : U→A) (q : U→B)
    (agree : ∀v∈xs,p v=p u ↔ q v=q u) : (xs.map p).idxOf (p u)=(xs.map q).idxOf (q u) := by
  induction xs with
  | nil => rfl
  | cons v xs ih =>
    have here:=agree v (by simp)
    have next:=ih (fun t ht=>agree t (by simp [ht]))
    by_cases h:p v=p u
    · simp [h,here.mp h]
    · have no:=mt here.mpr h
      simp [h,no,next]

variable {I P C V F J : Type} [Fintype I] [DecidableEq I] [Fintype V] [DecidableEq V]
    [Field F] [Fintype J] [DecidableEq J] {d : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable {k hCode i a : ℕ}
variable (A : GroupStage W G price ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
    (pick : I×Fin 2↪W.graph.Edge) (layout : Bool) (pack : W.graph.Site→C)
variable (key : Merged W.graph pick layout pack→Key (J×V)) (hub : J×V→Bool) (slots : ℕ) (profile : I→Profile G.C)
local notation "N" => W.graph
local notation "K" => fun u : W.graph.Site => key (newSite W.graph pick layout pack (Sum.inl u))
local notation "c" => normBits A.cap G.b G.C G.k

omit [DecidableEq I] [Field F] in
private theorem observed_terms (e : W.graph.Edge) (z : W.graph.Site→LocalActor) :
    observations (z ((N).src e)) (z ((N).dst e)) ((first pick e).map (fun j t=>z (StarKeys.endpoint (N) pick j t)))=
      (terms pick e).map z := by
  cases f:first pick e with
  | none => simp [observations,terms,f]
  | some j => simp [observations,terms,f]

omit [DecidableEq I] in
/-- Recode the short ranks *within this very donor*. Equality of true sites
is supplied by the common four-step roster. Each emitted actor node then uses
the original pre/post hub flag and exact dyadic number. -/
theorem observed_eq (e : Stage.Positive A) (z : W.graph.Site→LocalActor)
    (stable : ∀u∈terms pick e.val,∀v∈terms pick e.val,(z u).rank=(z v).rank ↔ (K u).1=(K v).1)
    (hubs : ∀u∈terms pick e.val,(z u).hub=hub (K u).1)
    (addresses : ∀u∈terms pick e.val,((z u).node,(z u).pack)=(DescentPacking.PackedMatch.Local.heap (K u).2.1,(K u).2.2)) :
    let tags:=(first pick e.val).map (fun j t=>z (StarKeys.endpoint (N) pick j t))
    observedDonor slots a c (z ((N).src e.val)) (z ((N).dst e.val)) tags
        (GadgetNetwork.selected (N) pick e.val).isSome layout
        ⟨normalized A profile (.inl e.val),normalized_fits A S ready profile _⟩ (Fin.ofNat (2^c) G.b)
        (fun t=>((first pick e.val).map (fun j=>(⟨normalized A profile (.inr (.inr (j,t))),
          normalized_fits A S ready profile _⟩:Cell c))).getD 0)=
      measuredDonor (hCode:=hCode) A S ready pick layout pack key hub slots profile
        (relative pick layout pack key) e := by
  classical
  intro tags
  let rows:=observations (z ((N).src e.val)) (z ((N).dst e.val)) tags
  have mapRows : rows=(terms pick e.val).map z := observed_terms pick e.val z
  have enc (u : W.graph.Site) (inside : u∈terms pick e.val) : actorWord slots a rows (z u)=
      rooted hCode slots 3 a hub (K u) (relative pick layout pack key e.val u) := by
    have eqidx:=idxOf_map_test (terms pick e.val) u (fun v=>(z v).rank) (fun v=>(K v).1)
      (fun v hv=>stable v hv u inside)
    obtain ⟨node,slab⟩:=Prod.mk.inj (addresses u inside)
    simp only [actorWord,mapRows,List.map_map,Function.comp_def,eqidx,hubs u inside,node,slab,
      rooted,relative,SiteDecode.localNumber,packedNumber,zero_mul,zero_add,
      DescentPacking.PackedMatch.Local.heap,nodeNumber]
    rw [Fin.ofNat_eq_cast]
  have born (t : Fin 3) : (tags.map (fun f=>actorWord slots a rows (f t))).getD 0=
      ((first pick e.val).map (fun j=>rooted hCode slots 3 a hub (K (StarKeys.endpoint (N) pick j t))
        (relative pick layout pack key e.val (StarKeys.endpoint (N) pick j t)))).getD 0 := by
    cases found:first pick e.val with
    | none => simp [tags,found]
    | some j =>
      have yes:=first_spec pick found
      have member : StarKeys.endpoint (N) pick j t∈terms pick e.val := yes ▸ term_mem pick j t
      simpa only [tags,found,Option.map_some,Option.getD_some] using enc _ member
  have flags : tags.isSome=(first pick e.val).isSome := by simp [tags]
  unfold observedDonor measuredDonor
  dsimp only
  rw [flags,enc _ (source_mem pick _),enc _ (target_mem pick _),funext born]

end
end Hierarchy.DescentRawCablePanel

end OAI
