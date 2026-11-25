import OAI.Hierarchy.DescentResetWindowScope
import OAI.Hierarchy.DescentResetSignedScan
import OAI.Hierarchy.DescentResetWindowPriority
import OAI.Hierarchy.DescentResetLocalRoster

namespace OAI
/-! # Three native weighted positions at the actual reset parent and sign -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e=>(coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw index S B.valid rawSite
local notation "renameEdge" => DescentPhysicalOrder.rename sparse
local notation "next" => B.reblock.result
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "stream'" => Stage.stream A ord
local notation "board" => Stage.source A ord
local notation "wt" => weight B
local notation "grains" => emit B
local notation "piece'" => piece B
local notation "base'" => first B


open scoped BigOperators
open DescentNextSignedWindow
local notation "C₀" => blocks B
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "live" => fun e : (coarse).graph.Edge=>e∈(coarse).core
local notation "fit" => Stage.measured A ord S B.next.valid
variable (names : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k ↪ ℕ)

/-- The other endpoint is in the actual measured neighbor list, including a
self-loop precisely when the reset installed a self neighbor. -/
theorem otherNear (h₀ : Host) (x : Local C₀ h₀) : other C₀ h₀ x∈Stage.near A h₀ := by
  have ends:=Stage.connected A ord ((C₀).order ⟨x.val,⟨0,x.property.1⟩⟩)
  rw [(C₀).atSource,(C₀).atTarget] at ends
  unfold other
  split
  next own=>simpa only [←own] using ends.1
  next different=>simpa only [←x.property.2.resolve_left different] using ends.2

def shortParent (h₀ : Host) (x : Local C₀ h₀) : Parent where
  peer:=((Halo.fromRank (Stage.near A) names (Stage.near_room A)).slot h₀ ⟨other C₀ h₀ x,otherNear B h₀ x⟩).val
  group:=(sourceClass B h₀ x).val
  ticket:=(sourceTicket B x.val x.property.1).val
  units:=(C₀).count x.val

theorem short_peer (h₀ : Host) (x y : Local C₀ h₀) :
    (shortParent B names h₀ x).peer=(shortParent B names h₀ y).peer ↔ other C₀ h₀ x=other C₀ h₀ y := by
  constructor
  · intro same
    exact congrArg Subtype.val (((Halo.fromRank (Stage.near A) names (Stage.near_room A)).slot h₀).injective (Fin.ext same))
  · intro same
    exact congrArg (fun t : ↥(Stage.near A h₀)=>((Halo.fromRank (Stage.near A) names (Stage.near_room A)).slot h₀ t).val)
      (Subtype.ext same)

theorem short_before (h₀ : Host) (a b : Local C₀ h₀) : precedes (shortParent B names h₀ a) (shortParent B names h₀ b) ↔
    (C₀).first a.val<(C₀).first b.val := by
  rw [←priority_lt B h₀ a b,Fin.lt_def,priority_val,priority_val]
  exact (DescentCableDonorNames.digit_lt (sourceTicket B a.val a.property.1).isLt (sourceTicket B b.val b.property.1).isLt).symm

variable {m : ℕ} (address : ∀h : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k, Local (blocks B) h ↪ Fin m)
def shortRow (h₀ : Host) (slot : Fin m) := (DescentResetLocalRoster.origin C₀ h₀ (address h₀) slot).map (shortParent B names h₀)

def sumAt (peer : Bool) (h₀ : Host) (x : Local C₀ h₀) :=
  ∑i : Fin m,contribution peer (some (shortParent B names h₀ x)) (shortRow B names address h₀ i)

theorem sum_locals (peer : Bool) (h₀ : Host) (x : Local C₀ h₀) :
    sumAt B names address peer h₀ x=∑y : Local C₀ h₀,
      if (C₀).first y.val<(C₀).first x.val ∧ (peer=true → (C₀).parallel ((C₀).src x.val) ((C₀).dst x.val) y.val)
      then (C₀).count y.val else 0 := by
  let f (y : Local C₀ h₀):=contribution peer (some (shortParent B names h₀ x)) (some (shortParent B names h₀ y))
  have go:=DescentResetLocalRoster.origin_sum C₀ h₀ (address h₀) f
  calc
    _=∑i : Fin m,(DescentResetLocalRoster.origin C₀ h₀ (address h₀) i).elim 0 f:=by
      apply Finset.sum_congr rfl
      intro j _
      unfold shortRow
      cases DescentResetLocalRoster.origin C₀ h₀ (address h₀) j <;> rfl
    _=∑y : Local C₀ h₀,f y:=go
    _=_:=by
      apply Finset.sum_congr rfl
      intro y _
      change (if precedes (shortParent B names h₀ y) (shortParent B names h₀ x) ∧
        (peer=true→(shortParent B names h₀ y).peer=(shortParent B names h₀ x).peer)
        then (C₀).count y.val else 0) = _
      simp only [short_before B names h₀ y x,short_peer B names h₀ y x,other_parallel C₀ h₀ x y]

private theorem sum_on (h₀ : Host) (price : (coarse).graph.Edge→ℕ)
    (off : ∀e,¬(0<(C₀).count e ∧ ((C₀).src e=h₀ ∨ (C₀).dst e=h₀))→price e=0) :
    (∑v : Local C₀ h₀,price v.val)=∑e,price e := by
  rw [←Finset.sum_subtype (Finset.univ.filter (fun e=>(0<(C₀).count e ∧ ((C₀).src e=h₀ ∨ (C₀).dst e=h₀)))) (by simp) price,
    Finset.sum_filter]
  exact Finset.sum_congr rfl (fun e _=>by split <;> simp_all)

theorem incident_position (h₀ : Host) (x : Local C₀ h₀) : sumAt B names address false h₀ x=
    ((Stage.source A ord).position fit h₀ (Incidence.candidate C₀ h₀ x ⟨0,x.property.1⟩)).val := by
  rw [sum_locals,Incidence.initial]
  let fee (e : (coarse).graph.Edge):=if ((C₀).src e=h₀ ∨ (C₀).dst e=h₀) ∧ (C₀).first e<(C₀).first x.val then (C₀).count e else 0
  have off (e) (miss : ¬(0<(C₀).count e ∧ ((C₀).src e=h₀ ∨ (C₀).dst e=h₀))) : fee e=0 := by
    unfold fee
    split
    next hit => exact Nat.eq_zero_of_not_pos (fun positive => miss ⟨positive,hit.1⟩)
    next => rfl
  rw [←sum_on B h₀ fee off]
  apply Finset.sum_congr rfl
  intro e _
  simp [fee,e.property.2]

theorem shared_position (h₀ : Host) (x : Local C₀ h₀) : sumAt B names address true h₀ x=
    (Stage.source A ord).serial ((C₀).src x.val) ((C₀).dst x.val) ((C₀).order ⟨x.val,⟨0,x.property.1⟩⟩) := by
  rw [sum_locals,(C₀).first_serial]
  let fee (e : (coarse).graph.Edge):=if (C₀).parallel ((C₀).src x.val) ((C₀).dst x.val) e ∧ (C₀).first e<(C₀).first x.val then (C₀).count e else 0
  have off (e) (miss : ¬(0<(C₀).count e ∧ ((C₀).src e=h₀ ∨ (C₀).dst e=h₀))) : fee e=0 := by
    unfold fee
    split
    next hit=>
      have ends:=hit.1
      have here:=x.property.2
      unfold Blocks.parallel at ends
      grind
    next=>rfl
  rw [←sum_on B h₀ fee off]
  apply Finset.sum_congr rfl
  intro e _
  simp [fee,and_comm]

theorem three_fields (h₀ : Host) (f₀ : Roster.Face A ord C₀ h₀) :
    let e:=f₀.val.1
    let rec_:=DescentResetWindowFields.record A ord S B.next.valid C₀ live h₀ f₀
      (DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ h₀ f₀)
    let x:=Roster.resident A ord C₀ h₀ f₀
    let origin : Local C₀ ((C₀).src e):=⟨e,f₀.property.1,.inl rfl⟩
    sumAt B names address false h₀ x=rec_.position ∧ sumAt B names address true h₀ x=rec_.shared ∧
      sumAt B names address false ((C₀).src e) origin=rec_.atSource ∧ rec_.count=(coarse).graph.width e/(Z).unit := by
  exact ⟨incident_position B names address ..,shared_position B names address ..,
    incident_position B names address ..,weight_quotient B _⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
