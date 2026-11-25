import OAI.Hierarchy.DescentResetFieldAssembler
import OAI.Hierarchy.DescentResetNativeWindows
import OAI.Hierarchy.DescentResetWindowEmittedSources
import OAI.Hierarchy.DescentPackedMatchRoster

namespace OAI
/-! # The two endpoint classes, self and real cable flags on the mixed reset candidate mesh -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
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
open DescentResetWindowResidentSources DescentResetFieldAssembler
open private filter_eq_of_iff from OAI.Hierarchy.DescentResetWindowResidentSources
local notation "roster" h => sources A h
local notation "near" h => Stage.near A h
local notation "entry" => (Z).rawHostRank T vertexCode
local notation "oldRank" => (entry).trans Fin.valEmbedding

def localClass (h₀ v : Host) : ℕ:=((roster h₀).filter (fun u=>hostKey B u<hostKey B v)).card

/-- The source ordering used by the numeric reset compiler. Only comparisons
inside one fixed group and low block are observed in a signed packet. -/
def fieldNames : Host↪ℕ:=DescentPacking.PackedMatch.Local.Stage.cableNames k
  (groupRank (Fin.valEmbedding (n:=groups)) oldRank)

def «meta» (h₀ : Host) : Option (Local C₀ h₀)→Meta
  | none=>.blank
  | some x=>⟨true,localClass B h₀ ((C₀).src x.val),localClass B h₀ ((C₀).dst x.val),localClass B h₀ h₀,
      decide (h₀∉near h₀),decide (x.val∈(coarse).core),(C₀).count x.val⟩

theorem localClass_src (h₀ : Host) (x : Local C₀ h₀) :
    localClass B h₀ ((C₀).src x.val)=(sourceClass B h₀ x).val:=rfl

theorem destination_mem (h₀ : Host) (x : Local C₀ h₀) : (C₀).dst x.val∈roster h₀ := by
  rcases x.property.2 with src|dst
  · have connected:=(Stage.connected A ord ((C₀).order ⟨x.val,⟨0,x.property.1⟩⟩)).1
    rw [(C₀).atSource,(C₀).atTarget,src] at connected
    exact Finset.mem_insert_of_mem connected
  · exact Finset.mem_insert.mpr (.inl dst)

theorem class_host (h₀ v : Host) (yes : v∈roster h₀) :
    localClass B h₀ v=((insert h₀.1.2 ((A).near h₀.1.2)).filter (fun u=>oldRank u<oldRank v.1.2)).card := by
  have atV : hostAt h₀ v.1.2=v:=by
    rw [sources_as_map A] at yes
    obtain ⟨s,_,eqn⟩:=Finset.mem_map.mp yes
    rw [←eqn];rfl
  have compare (u : B.next.V) : hostKey B (hostAt h₀ u)<hostKey B v ↔ oldRank u<oldRank v.1.2:=by
    calc
      _ ↔ hostKey B (hostAt h₀ u)<hostKey B (hostAt h₀ v.1.2):=by rw [atV]
      _ ↔ _ := by
        change (h₀.1.1.val*pitch oldRank+oldRank u)*2^k+h₀.2.val <
          (h₀.1.1.val*pitch oldRank+oldRank v.1.2)*2^k+h₀.2.val ↔ _
        simp only [Nat.add_lt_add_iff_right,Nat.mul_lt_mul_right (Nat.two_pow_pos k),Nat.add_lt_add_iff_left]
  unfold localClass
  rw [sources_as_map A,Finset.filter_map,Finset.card_map]
  apply congrArg Finset.card
  exact filter_eq_of_iff _ compare

theorem self_missing (h₀ : Host) : h₀∉(near h₀) ↔ h₀.1.2∉(A).near h₀.1.2 := by
  rcases h₀ with ⟨⟨g,v⟩,x⟩
  apply not_congr
  constructor
  · intro mem
    obtain ⟨v₁, hv₁, eq₁⟩ := Finset.mem_map.mp mem
    obtain ⟨v₂, hv₂, eq₂⟩ := Finset.mem_map.mp hv₁
    have eq := congrArg (fun t : Host => t.1.2) eq₁
    change v₁.2 = v at eq
    have atV := congrArg Prod.snd eq₂
    change v₂ = v₁.2 at atV
    exact (atV.trans eq) ▸ hv₂
  · intro mem
    exact Finset.mem_map.mpr ⟨(g,v),Finset.mem_map.mpr ⟨v,mem,rfl⟩,rfl⟩

theorem class_lt (h₀ a b : Host) (ha : a∈roster h₀) (hb : b∈roster h₀) :
    localClass B h₀ a<localClass B h₀ b ↔ hostKey B a<hostKey B b := by
  let r:=Ends.neighborOrder (sources A) (fieldNames B) (sources_room A) h₀
  have pos (v : ↥(roster h₀)) : (r v).val=localClass B h₀ v.val:=
    DescentPacking.PackedMatch.Local.Stage.nb_val (sources A) (fieldNames B) (sources_room A) h₀ v
  rw [←pos ⟨a,ha⟩,←pos ⟨b,hb⟩]
  exact (((roster h₀).map (fieldNames B)).orderIsoOfFin rfl).symm.lt_iff_lt

theorem class_eq (h₀ a b : Host) (ha : a∈roster h₀) (hb : b∈roster h₀) :
    localClass B h₀ a=localClass B h₀ b ↔ a=b := by
  refine ⟨fun same=>?_,congrArg (localClass B h₀)⟩
  apply (fieldNames B).injective
  rcases lt_trichotomy (hostKey B a) (hostKey B b) with lt|eqn|gt
  · exact ((class_lt B h₀ a b ha hb).2 lt).ne same |>.elim
  · exact eqn
  · exact ((class_lt B h₀ b a hb ha).2 gt).ne same.symm |>.elim

theorem meta_face (h₀ : Host) (x : Local C₀ h₀) (side : Bool) :
    face side («meta» B h₀ (some x))=true ↔ (if side then (C₀).dst x.val else (C₀).src x.val)=h₀ := by
  have self : h₀∈roster h₀:=Finset.mem_insert_self ..
  cases side
  · simpa [face,«meta»] using class_eq B h₀ ((C₀).src x.val) h₀ (source_mem A ord C₀ h₀ x) self
  · simpa [face,«meta»] using class_eq B h₀ ((C₀).dst x.val) h₀ (destination_mem B h₀ x) self

theorem meta_peer (h₀ : Host) (x : Local C₀ h₀) :
    peer («meta» B h₀ (some x))=(shortParent B (fieldNames B) h₀ x).peer := by
  let y:=other C₀ h₀ x
  have near_ : y∈near h₀:=otherNear B h₀ x
  have member : y∈roster h₀ := Finset.mem_insert_of_mem near_
  have self : h₀∈roster h₀:=Finset.mem_insert_self ..
  have oppositeAt : opposite («meta» B h₀ (some x))=localClass B h₀ y:=by
    have sameClass := class_eq B h₀ ((C₀).src x.val) h₀ (source_mem A ord C₀ h₀ x) self
    by_cases chosen : (C₀).src x.val=h₀
    · simp only [opposite, «meta», y, other, ite_eq_left chosen]
      exact ite_eq_left (sameClass.mpr chosen)
    · simp only [opposite, «meta», y, other, ite_eq_right chosen]
      exact ite_eq_right (fun eq => chosen (sameClass.mp eq))
  have num : (shortParent B (fieldNames B) h₀ x).peer=((near h₀).filter (fun u=>hostKey B u<hostKey B y)).card:=
    DescentPacking.PackedMatch.Local.Stage.nb_val (Stage.near A) (fieldNames B) (Stage.near_room A) h₀ ⟨y,near_⟩
  rw [num,peer,oppositeAt]
  change localClass B h₀ y-(decide (decide (h₀∉near h₀)=true ∧ localClass B h₀ h₀<localClass B h₀ y)).toNat=_
  have classOrder := class_lt B h₀ h₀ y self member
  by_cases contains : h₀∈near h₀
  · simp [localClass,sources,contains,Finset.insert_eq_of_mem contains]
  · by_cases lt : hostKey B h₀<hostKey B y
    · have miss : h₀∉(near h₀).filter (fun u=>hostKey B u<hostKey B y):=fun h=>contains (Finset.mem_filter.mp h).1
      simp only [classOrder.mpr lt, and_true]
      simp [localClass,sources,Finset.filter_insert,contains,lt,miss]
    · have notLess : ¬localClass B h₀ h₀<localClass B h₀ y := fun h => lt (classOrder.mp h)
      simp only [show ¬(decide (h₀∉near h₀)=true ∧ localClass B h₀ h₀<localClass B h₀ y) from fun h => notLess h.2, decide_false, Bool.toNat_false, Nat.sub_zero]
      simp [localClass,sources,Finset.filter_insert,lt]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
