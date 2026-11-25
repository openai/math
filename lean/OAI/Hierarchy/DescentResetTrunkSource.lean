import OAI.Hierarchy.DescentResetTrunkMeta
import OAI.Hierarchy.DescentResetTrunkIssue
import OAI.Hierarchy.DescentResetStencilActors

namespace OAI
/-! # The measured reset actor selects the two ends of the unique raw trunk -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSharedCableNames DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "addresses" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
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



open DescentPackedZip DescentSIMDLookup DescentResetTrunkIssue ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
local notation "Node₀" => Node (Z).V ((Z).V×DescentContacts.Endpoint (2^(Z).n)) (DescentCommonPalette.rotor (Z).graph).Site
local notation "short" t:arg => DescentRelativeContacts.shortName (T).commonDepth ((T).code t)
local notation "high_" u:arg => (addresses).symm ((u).1.1,(u).2)
local notation "hi_" t:arg => DescentChosenRouter.coarseName (T).commonDepth ((T).code t)
local notation "touch" u:arg t:arg => ((rows).src (trunkParent B t)=u ∨ (rows).dst (trunkParent B t)=u)

/-- Numerical receiver identity is its original short host key plus its original
coarse block. This statement is valid on every allocated host and low digit. -/
def trunkCoordinate (u : Host) : Node₀×Block (T).commonDepth :=(u.1.2.val,high_ u)

theorem trunkCoordinate_injective : Function.Injective (trunkCoordinate B) := by
  rintro ⟨⟨j,x⟩,l⟩ ⟨⟨k,y⟩,r⟩ eqn
  have name:=congrArg Prod.fst eqn
  have addr:=(addresses).symm.injective (congrArg Prod.snd eqn)
  rcases Prod.mk.inj addr with ⟨rfl,rfl⟩
  have xy : x=y:=Subtype.ext name
  cases xy
  rfl

theorem trunk_side (t : (Z).Fallback) (s : Bool) :
    let e:=trunkParent B t
    let end_:=if s then (rows).dst e else (rows).src e
    (trunkCoordinate B end_).1=.trunk s (short t) ∧ (trunkCoordinate B end_).2.val=hi_ t := by
  have heads:=trunk_host_words B t
  cases s
  · change ((Stage.home B.next.placement (hop ((coarse).graph.src _))).1.2.val=_) ∧
      ((addresses).symm ((Stage.home B.next.placement (hop ((coarse).graph.src _))).1.1,
        (Stage.home B.next.placement (hop ((coarse).graph.src _))).2)).val=_
    rw [named_home,Equiv.symm_apply_apply]
    exact ⟨heads.1.1,heads.2.1⟩
  · change ((Stage.home B.next.placement (hop ((coarse).graph.dst _))).1.2.val=_) ∧
      ((addresses).symm ((Stage.home B.next.placement (hop ((coarse).graph.dst _))).1.1,
        (Stage.home B.next.placement (hop ((coarse).graph.dst _))).2)).val=_
    rw [named_home,Equiv.symm_apply_apply]
    exact ⟨heads.1.2,heads.2.2⟩

/-- A true terminal test is the already-issued actor stencil bit at a trunk name;
the same low digit and group give the actual peer, even at zero traffic. -/
def trunkTest (u : Host) : Prop:=
  match (trunkCoordinate B u).1 with
  | .trunk s z=> (Z).emits T (.trunk s z) (high_ u)
  | _ => False

theorem trunk_test (u : Host) : trunkTest B u ↔ ∃t : (Z).Fallback,touch u t := by
  constructor
  · intro test
    cases kind : (trunkCoordinate B u).1 with
    | trunk s z=>
      obtain ⟨t,name,coarseBlock⟩ : ∃t, short t=z ∧ hi_ t=(high_ u).val:=by
        simpa only [trunkTest,kind,ResetInput.emits] using test
      have head:=trunk_side B t s
      have eqn:=trunkCoordinate_injective B (Prod.ext (head.1.trans ((congrArg (Node.trunk s) name).trans kind.symm))
        (Fin.ext (head.2.trans coarseBlock)))
      exact ⟨t,by cases s <;> simp_all⟩
    | good=>simp [trunkTest,kind] at test
    | fall=>simp [trunkTest,kind] at test
  · rintro ⟨t,atEnd⟩
    let accept (code : Node₀) : Prop := match code with
      | .trunk sign label => (Z).emits T (.trunk sign label) (high_ u)
      | _ => False
    have found (sign : Bool) (eqn : (trunkCoordinate B u).1=.trunk sign (short t))
        (addr : (high_ u).val=hi_ t) : trunkTest B u :=
      Eq.mpr (congrArg accept eqn) (show accept (.trunk sign (short t)) from ⟨t,rfl,addr.symm⟩)
    rcases atEnd with rfl|rfl
    · exact found false (trunk_side B t false).1 (trunk_side B t false).2
    · exact found true (trunk_side B t true).1 (trunk_side B t true).2

/-- A semantic name for the fiber selected by the measured bit. No native
lookup is indexed by this type. Source and relay use the two public keys. -/
def acceptedTrunk (u : Host) : Option (Z).Fallback:=
  if h : trunkTest B u then some ((trunk_test B u).1 h).choose else none

theorem accepted_hit (u : Host) (t : (Z).Fallback) :
    acceptedTrunk B u=some t ↔ touch u t:=by
  unfold acceptedTrunk
  split
  next h=>
    have yes:=((trunk_test B u).1 h).choose_spec
    rw [Option.some.injEq]
    constructor
    · rintro rfl;exact yes
    · exact trunk_eq B yes
  next neg=>simp only [reduceCtorEq,false_iff];exact fun live=>neg ((trunk_test B u).2 ⟨t,live⟩)

def trunkShape (u : Host) : Meta:=
  match acceptedTrunk B u with
  | none=>.blank
  | some t=>
    let e:=trunkParent B t
    ⟨true,localClass B u ((rows).src e),localClass B u ((rows).dst e),localClass B u u,
      decide (u∉Stage.near B.next.placement u),((T).code t).2.2.isSome,0⟩

def relayRows (u : Host) (j : Fin half) : Meta:=
  match acceptedTrunk B u with
  | none=>.blank
  | some t=>let relay:=(rows).dst (trunkParent B t)
            «meta» B relay (localOrigin B relay (incomingCandidate B j))

theorem trunk_shape_live (u : Host) : (trunkShape B u).live=true ↔ trunkTest B u := by
  by_cases yes : trunkTest B u
  · have present : acceptedTrunk B u = some ((trunk_test B u).1 yes).choose := dite_eq_left yes
    simp [trunkShape,present,yes]
  · have blank : acceptedTrunk B u = none := dite_eq_right yes
    simp [trunkShape,blank,Meta.blank,yes]

theorem trunk_shape_core (u : Host) (s z) (kind : (trunkCoordinate B u).1=.trunk s z)
    (occupied : trunkTest B u) : (trunkShape B u).core=z.2.2.isSome:=by
  obtain ⟨t,atEnd⟩:=(trunk_test B u).1 occupied
  rw [trunkShape,(accepted_hit B u t).2 atEnd]
  rcases atEnd with left|right
  · subst u
    have eqnName:=((trunk_side B t false).1.symm.trans kind)
    have tag := congrArg (fun p : (Z).V×DescentContacts.Endpoint (2^(Z).n)=>p.2.2.isSome) (Node.trunk.inj eqnName).2
    exact tag
  · subst u
    have eqnName:=((trunk_side B t true).1.symm.trans kind)
    have tag := congrArg (fun p : (Z).V×DescentContacts.Endpoint (2^(Z).n)=>p.2.2.isSome) (Node.trunk.inj eqnName).2
    exact tag

theorem trunk_completed (u : Host) :
    DescentResetTrunkIssue.complete (trunkShape B u) (∑j,(face false (relayRows B u j)).toNat)=
      «meta» B u (localOrigin B u (trunkCandidate B)) := by
  cases selected : acceptedTrunk B u with
  | none=>
    have empty : ∀t,(rows).src (trunkParent B t)≠u ∧ (rows).dst (trunkParent B t)≠u:=by
      intro t
      have no : ¬(touch u t):=fun h => Option.some_ne_none t (((accepted_hit B u t).2 h).symm.trans selected)
      exact not_or.mp no
    simp [trunkShape,relayRows,selected,DescentResetTrunkIssue.complete,Meta.blank,trunk_no_row B u empty,face]
  | some t=>
    have endpoints:=(accepted_hit B u t).1 selected
    rw [trunk_meta B u t endpoints]
    unfold trunkShape relayRows
    simp only [selected]
    have countRead (n a b c : ℕ) (empty coreBit : Bool) :
        DescentResetTrunkIssue.complete ⟨true,a,b,c,empty,coreBit,0⟩ n = trunkHeader n a b c empty coreBit := by
      cases n <;> simp [DescentResetTrunkIssue.complete,trunkHeader]
    exact countRead (trunkUnits B t) _ _ _ _ _

/-- The result is the original cable's seven fields even if this physical cell
was never occupied or its terminal has no positive-width trunk. -/
theorem trunk_source {X H G₀ M b w₀ : ℕ} (base : ℕ) (head : Fin X→Expr) (stems : Fin X→Fin half→Expr)
    (focus : Fin X→Fin H→Fin G₀→Host) (m : Memory w₀)
    (early : ∀x,(head x).Fits w₀ base) (slots : ∀x j,(stems x j).Fits w₀ base)
    (heads : ∀x,Source (head x) (fun h g=>DescentResetFieldAssembler.raw b (trunkShape B (focus x h g))) M m)
    (bits : ∀x j,Source (stems x j) (fun h g=>DescentResetFieldAssembler.raw b (relayRows B (focus x h g) j)) M m)
    (bounded : ∀x h g l,DescentResetFieldAssembler.digits (trunkShape B (focus x h g)) l<2^b)
    (stemRoom : ∀x j h g l,DescentResetFieldAssembler.digits (relayRows B (focus x h g) j) l<2^b)
    (limit : ∀x h g,(∑j,(face false (relayRows B (focus x h g) j)).toNat)<2^b)
    (room : DescentResetTrunkIssue.endAddress base b M<2^w₀) :
    let top:=DescentResetTrunkIssue.endAddress base b M
    let done:=DescentResetTrunkIssue.memory base b M m
    (DescentResetTrunkIssue.program base b M w₀).Exec m done (4+10*(3*2^(DescentResetTrunkIssue.width b M))) ∧
      (∀x,(issue base b M (head x) (stems x)).Fits w₀ top) ∧
      (∀x,Source (issue base b M (head x) (stems x)) (fun h g=>let u:=focus x h g
        DescentResetFieldAssembler.raw b («meta» B u (localOrigin B u (trunkCandidate B)))) M done) ∧
      (∀a,a<base ∨ top≤a→done a=m a) ∧ DescentStaticWordColumn.names (DescentResetTrunkIssue.program base b M w₀)=
        15*(3*2^(DescentResetTrunkIssue.width b M)+1) ∧ CheapCode (DescentResetTrunkIssue.program base b M w₀) := by
  simpa only [trunk_completed] using DescentResetTrunkIssue.run (b:=b) base head stems m
    (fun x h g=>trunkShape B (focus x h g)) (fun x j h g=>relayRows B (focus x h g) j)
    early slots heads bits bounded stemRoom limit room

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
