import OAI.Hierarchy.DescentPackedOwnerWord
import OAI.Hierarchy.DescentPackedMatchNeeds
import OAI.Hierarchy.DescentColoredHost

namespace OAI
/-! # Reading an old actor's thin-pack slot from its colony's packed blocks -/
namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup
open scoped Classical
noncomputable section

private theorem readPack_decisions {U C D : Type} [Fintype C] [DecidableEq C] [DecidableEq D]
    (traffic : U→C→ℕ) (home : U→C) (B : ℕ) (thin thick : C→List U)
    (addr : U→D) (nod : ∀c,(thin c).Nodup) (u : U)
    (unique : ∀v∈thin (home u),addr v=addr u→v=u) :
    readPack ((thinPacks (live traffic) B (thin (home u))).map (List.map addr)) (addr u)=
      (match packLabel traffic home B thin thick u with
       | .inl _=>0 | .inr t=>t.2.val+1) := by
  let c := home u
  let q := slabPacking traffic B (thin c) (thick c)
  rw [←q.order]
  let rows := (q.decisions.map Prod.fst).map (List.map addr)
  have lengthEq : rows.length=q.decisions.length := by simp [rows]
  have entry (j : Fin rows.length) : addr u∈rows.get j ↔ u∈(q.decisions.get (j.cast lengthEq)).1 := by
    have localRow : rows.get j=(q.decisions.get (j.cast lengthEq)).1.map addr := by simp [rows,List.get_eq_getElem]
    rw [localRow,List.mem_map]
    constructor
    · rintro ⟨v,member,value⟩
      have inThin : v∈thin c := by
        rw [←thin_stream traffic B (thin c) (thick c)]
        exact List.mem_flatten.mpr ⟨_,List.mem_map_of_mem (f:=Prod.fst) (List.get_mem _ (j.cast lengthEq)),member⟩
      exact unique v inThin value ▸ member
    · intro member
      exact ⟨u,member,rfl⟩
  change readPack rows (addr u)=_
  unfold readPack
  cases found : (List.finRange rows.length).find? (fun i=>decide (addr u∈rows.get i)) with
  | none=>
    have absent : ¬∃j : Fin q.decisions.length,u∈(q.decisions.get j).1 := by
      rintro ⟨j,hj⟩
      let l := j.cast lengthEq.symm
      have hit : addr u∈rows.get l := (entry l).mpr hj
      exact (List.find?_eq_none.mp found l (List.mem_finRange l)) (decide_eq_true hit)
    unfold packLabel
    rw [dite_eq_right absent]
    rfl
  | some j=>
    have hit : addr u∈rows.get j := of_decide_eq_true
      (List.find?_some (p:=fun i : Fin rows.length => decide (addr u∈rows.get i)) found)
    rw [packLabel_slot traffic home B thin thick nod rfl (j.cast lengthEq) ((entry j).mp hit)]
    rfl

namespace Stage
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "Dest" => target A native S ready names
variable (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 +
        (scanColorAt he A.stage u).toNat)
include fit winner

/-- The physical locator returns the native slab ordinal for every old site,
including isolated old sites and all currently unmatched thin packs. -/
theorem original_pack (s : Shape) (coord : Function.Injective (fun z=>(A.pos z,A.block z)))
    (order : ∀u v,A.pos u=A.pos v→ originalId W.graph.Site u<originalId W.graph.Site v→A.block u<A.block v)
    (df : A.degree<2^short) (room : ∀h x (e : PackedCensus.Out W A.pos A.block h x),bin (panel h) (Dest (h,x) e) x<s.bins)
    (u : W.graph.Site) :
    readPack (packs (panel (A.pos u)) s.bins A.cap (heap (addr (home u)).2)) (A.block u)=
      (packAddress W.graph W.core home color A.cap addr (coloredPack W.graph W.core home color A.cap u)).2.2 := by
  have physical : packs (panel (addr (home u)).1) s.bins A.cap (heap (addr (home u)).2) =
      (thinPacks (live T) A.cap (thinList home color (home u))).map (List.map A.block) :=
    physical_packs (short:=short) (a:=a) A native S ready names win next he fit winner s coord order df room (home u)
  have atHost := congrArg
    (fun h : J×V => packs (panel h) s.bins A.cap (heap (addr (home u)).2)) (source_host A he u).symm
  refine (congrArg (fun rows : List (List (Fin (2^k))) => readPack rows (A.block u))
    (atHost.trans physical)).trans ?_
  have inject (v : W.graph.Site) (hv : v∈thinList home color (home u)) (eqn : A.block v=A.block u) : v=u := by
    have field := (mem_colorSites home color false (home u) v).mp hv
    apply coord
    exact Prod.ext ((source_host A he v).symm.trans
      ((congrArg (fun c : ScanColonies he A.stage => (addr c).1) field.1).trans (source_host A he u))) eqn
  have eqn:=readPack_decisions T home A.cap (thinList home color) (thickList home color) A.block (colorSites_nodup home color false) u inject
  refine eqn.trans ?_
  change _=(packAddress W.graph W.core home color A.cap addr (packLabel T home A.cap (thinList home color) (thickList home color) u)).2.2
  cases packLabel T home A.cap (thinList home color) (thickList home color) u <;> rfl

end Stage
end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
