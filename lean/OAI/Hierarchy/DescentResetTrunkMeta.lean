import OAI.Hierarchy.DescentResetTrunkRelay

namespace OAI
/-! # Live and blank words in the single public trunk slot -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


open DescentResetFieldAssembler DescentIssuedFallbackPanel DescentNextSignedWindow
local notation "rows" => blocks B
local notation "End" => (old).graph.Edge
local notation "Home" => (T).home
local notation "full" => totalLocal B
local notation "AC" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "before" => input.order.trans Fin.valEmbedding
local notation "half" => 2^(S.groupWidth k tail i+k-(T).commonDepth)*(2*(AC).cap)


def trunkCandidate : Fin full:=⟨stemsCount B,by unfold totalLocal;omega⟩

def trunkUnits (t : (Z).Fallback):=∑j,(incomingBit B ((rows).dst (trunkParent B t)) j).toNat

theorem trunk_units (t : (Z).Fallback) : (rows).count (trunkParent B t)=trunkUnits B t:=by
  have positive : 0<(Z).unit:=by rw [B.unit,←B.next.grain];exact Nat.mul_pos B.next.placement.unitPos G.base_pos
  have amount:=congrArg RawFields.width ((Z).trunkFields T t)
  change (coarse).graph.width (trunkParent B t)=Fintype.card {i : End // Home ((old).graph.dst i)=t}*(Z).unit at amount
  change weight B _=_
  rw [weight_quotient,amount,Nat.mul_div_cancel _ positive]
  exact (relay_bits B t).symm

theorem trunk_mark (t : (Z).Fallback) :
    decide (trunkParent B t∈(coarse).core)=((T).code t).2.2.isSome := by
  have badge:=congrArg RawFields.core ((Z).trunkFields T t)
  change decide (trunkParent B t∈(coarse).core)=!((T).hub t) at badge
  rw [badge]
  have known:=(T).hubShape t
  cases opt : ((T).code t).2.2 <;> cases bit : (T).hub t <;> simp_all

theorem at_trunk {u : Host} (x : Local rows u)
    (hit : localOrigin B u (trunkCandidate B)=some x) : ∃t,x.val=trunkParent B t := by
  rcases x with ⟨wire,member⟩
  obtain ⟨tag,rfl⟩:=(motherNames B).symm.surjective wire
  have n : (localRoster B u ⟨_,member⟩).val=stemsCount B := congrArg Fin.val ((local_read B u _ ⟨_,member⟩).mp hit)
  rcases tag with ⟨side,e⟩ | t | c | g
  · have eqn := (stem_number B u side e member).symm.trans n
    have low : (finProdFinEquiv (finTwoEquiv.symm side,finProdFinEquiv
        (localAddress AC before S input.valid digitsIn B.frame.basis side (beforeStem B e)))).val < stemsCount B :=
      Fin.isLt _
    exact (low.ne eqn).elim
  · exact ⟨t,rfl⟩
  · have eqn := (contact_number B u c member).symm.trans n
    omega
  · have eqn := (private_number B u g member).symm.trans n
    omega

/-- The shape decoder has no successful terminal for a nontrunk host. -/
theorem trunk_no_row (u : Host)
    (absent : ∀t, (rows).src (trunkParent B t)≠u ∧ (rows).dst (trunkParent B t)≠u) :
    «meta» B u (localOrigin B u (trunkCandidate B))=.blank:=by
  cases hit : localOrigin B u (trunkCandidate B) with
  | none=>rfl
  | some x=>
    obtain ⟨t,tag⟩:=at_trunk B x hit
    have incident:=x.property.2
    rw [tag] at incident
    exact False.elim (incident.elim (absent t).1 (absent t).2)

def trunkHeader (units src dst here : Nat) (selfAbsent core : Bool) : Meta:=
  if units=0 then .blank else ⟨true,src,dst,here,selfAbsent,core,units⟩

/-- This also covers a genuine emitted terminal with no incoming grain.
Its two physical host names still exist; only its port record is blank. -/
theorem trunk_meta (u : Host) (t : (Z).Fallback)
    (atEnd : (rows).src (trunkParent B t)=u ∨ (rows).dst (trunkParent B t)=u) :
    let e:=trunkParent B t
    «meta» B u (localOrigin B u (trunkCandidate B))=trunkHeader (trunkUnits B t)
      (localClass B u ((rows).src e)) (localClass B u ((rows).dst e))
      (localClass B u u) (decide (u∉Stage.near B.next.placement u)) ((T).code t).2.2.isSome := by
  dsimp only
  have units:=trunk_units B t
  by_cases empty : trunkUnits B t=0
  · rw [trunkHeader,ite_eq_left empty]
    cases hit : localOrigin B u (trunkCandidate B) with
    | none=>rfl
    | some x=>
      obtain ⟨t',origin⟩:=at_trunk B x hit
      have touching:=x.property.2
      rw [origin] at touching
      obtain rfl:=trunk_eq B atEnd touching
      have nonzero:=x.property.1
      rw [origin,units,empty] at nonzero
      omega
  · have yes : DescentResetLocalRoster.active rows u (trunkParent B t):=⟨by rw [units];omega,atEnd⟩
    let x : Local rows u:=⟨trunkParent B t,yes⟩
    have visible : localOrigin B u (trunkCandidate B)=some x:=(local_read B u _ x).2 (Fin.ext (trunk_number B u t yes))
    rw [visible,trunkHeader,ite_eq_right empty]
    simp only [«meta»,x,units,trunk_mark]

theorem trunk_host_words (t : (Z).Fallback) :
    let e:=trunkParent B t
    let n:=DescentRelativeContacts.shortName (T).commonDepth ((T).code t)
    let g₀:=DescentChosenRouter.coarseName (T).commonDepth ((T).code t)
    ((Z).commonName T ((coarse).graph.src e)=.trunk false n ∧ (Z).commonName T ((coarse).graph.dst e)=.trunk true n) ∧
      ((Z).blockId T ((coarse).graph.src e)).val=g₀ ∧ ((Z).blockId T ((coarse).graph.dst e)).val=g₀ := by
  dsimp only
  have dataFields:=(Z).trunkFields T t
  have ids:=(Z).trunkArchive T vertexCode birth t
  exact ⟨⟨congrArg RawFields.src dataFields,congrArg RawFields.dst dataFields⟩,
    congrArg (fun r : ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×Bool=>r.2.2.2.1) ids,
    congrArg (fun r : ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×Bool=>r.2.2.2.2.1) ids⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
