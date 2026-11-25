import OAI.Hierarchy.DescentResetCandidateMeta
import OAI.Hierarchy.DescentResetWindowStemOrder

namespace OAI
/-! # The one public reset trunk counts actual incoming original stem slots at its relay -/
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

def incomingCandidate (j : Fin half) : Fin full :=
  Fin.castLE (by change stemsCount B≤totalLocal B;unfold totalLocal;omega)
    (finProdFinEquiv (finTwoEquiv.symm true,j))

def incomingIndex (e : End) : Fin half:=finProdFinEquiv
  (localAddress AC before S input.valid digitsIn B.frame.basis true (beforeStem B e))

/-- The true endpoint at which every incoming old stem starts is the
relay of its actual terminal.  No loop or parallel edge is suppressed. -/
theorem incoming_home (t : (Z).Fallback) (e : End) :
    (rows).src (stemParent B (true,e))=(rows).dst (trunkParent B t) ↔ Home ((old).graph.dst e)=t := by
  let names:=installedNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
  have a : names ((coarse).graph.src (stemParent B (true,e)))=.inl (true,Home ((old).graph.dst e)):=by
    have dataFields:=sourceFields_read (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables (stemParent B (true,e))
    change physicalFields _ _ _ _ _ _ _ _=sourceFields _ _ _ _ _ ((wires) ((wires).symm _)) at dataFields
    exact congrArg RawFields.src (dataFields.trans (congrArg (sourceFields (old) (T).home (placement).input (T).hub (Z).bank) ((wires).apply_symm_apply (.inl (true,e)))))
  have b : names ((coarse).graph.dst (trunkParent B t))=.inl (true,t):=by
    have dataFields:=sourceFields_read (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables (trunkParent B t)
    change physicalFields _ _ _ _ _ _ _ _=sourceFields _ _ _ _ _ ((wires) ((wires).symm _)) at dataFields
    exact congrArg RawFields.dst (dataFields.trans (congrArg (sourceFields (old) (T).home (placement).input (T).hub (Z).bank) ((wires).apply_symm_apply (.inr (.inl t)))))
  constructor
  · intro coords
    have ids:=congrArg names ((hop).injective (B.next.valid.coordinates coords))
    rw [a,b] at ids
    exact congrArg Prod.snd (Sum.inl.inj ids)
  · intro home
    have ids:=names.injective (a.trans ((congrArg (fun z=>Sum.inl (true,z)) home).trans b.symm))
    exact congrArg (fun u=>Stage.home B.next.placement (hop u)) ids

theorem stem_one (s : Bool) (e : End) : (rows).count (stemParent B (s,e))=1 := by
  have pos : 0<(Z).unit:=by rw [B.unit,←B.next.grain];exact Nat.mul_pos B.next.placement.unitPos G.base_pos
  have dataFields:=(Z).stemFields T s e
  have amount : (coarse).graph.width (stemParent B (s,e))=(Z).unit:=congrArg RawFields.width dataFields
  change weight B _=_
  rw [weight_quotient,amount,Nat.div_self pos]

theorem incoming_origin (u : Host) (j : Fin half) (x : DescentParallelBase.Local rows u)
    (present : localOrigin B u (incomingCandidate B j)=some x) :
    ∃e : End,x.val=stemParent B (true,e) ∧ incomingIndex B e=j := by
  rcases x with ⟨wire,hx⟩
  obtain ⟨tag,rfl⟩:=(motherNames B).symm.surjective wire
  have whereAt:=(local_read B u _ ⟨_,hx⟩).mp present
  have low : (localRoster B u ⟨_,hx⟩).val < stemsCount B :=
    lt_of_eq_of_lt (congrArg Fin.val whereAt) (finProdFinEquiv (finTwoEquiv.symm true,j)).isLt
  rcases tag with ⟨side,e⟩ | t | c | g
  · have tagAt:=stem_number B u side e hx
    have pack : finProdFinEquiv (finTwoEquiv.symm side,finProdFinEquiv
        (localAddress AC before S input.valid digitsIn B.frame.basis side (beforeStem B e)))=
      finProdFinEquiv (finTwoEquiv.symm true,j):=
      Fin.ext (tagAt.symm.trans (congrArg Fin.val whereAt))
    have coords:=finProdFinEquiv.injective pack
    obtain rfl:=finTwoEquiv.symm.injective (congrArg Prod.fst coords)
    exact ⟨e,rfl,congrArg Prod.snd coords⟩
  · have impossible:=lt_of_eq_of_lt (trunk_number B u t hx).symm low
    omega
  · have impossible:=lt_of_eq_of_lt (contact_number B u c hx).symm low
    omega
  · have impossible:=lt_of_eq_of_lt (private_number B u g hx).symm low
    omega

def incomingBit (u : Host) (j : Fin half) : Bool :=
  face false («meta» B u (localOrigin B u (incomingCandidate B j)))

theorem relay_bits (t : (Z).Fallback) :
    let u:=(rows).dst (trunkParent B t)
    (∑j,(incomingBit B u j).toNat)=Fintype.card {e : End // Home ((old).graph.dst e)=t} := by
  intro u
  let fibre:={e : End // Home ((old).graph.dst e)=t}
  have activeHere (e : fibre) : DescentResetLocalRoster.active rows u (stemParent B (true,e.val)) :=
    ⟨by rw [stem_one];decide,Or.inl ((incoming_home B t e.val).2 e.property)⟩
  let resident (e : fibre) : DescentParallelBase.Local rows u:=⟨stemParent B (true,e.val),activeHere e⟩
  have whereAt (e : fibre) : localRoster B u (resident e)=incomingCandidate B (incomingIndex B e.val):=
    Fin.ext (stem_number B u true e.val (activeHere e))
  let address : fibre↪Fin half:=⟨fun e=>incomingIndex B e.val,fun e f ident=>by
    have h:=(localRoster B u).injective ((whereAt e).trans ((congrArg (incomingCandidate B) ident).trans (whereAt f).symm))
    have tags:=(motherNames B).symm.injective (congrArg Subtype.val h)
    exact Subtype.ext (congrArg Prod.snd (Sum.inl.inj tags))⟩
  have read (e : fibre) : incomingBit B u (address e)=true:=by
    exact (congrArg (fun slot => face false («meta» B u slot))
      ((local_read B u _ (resident e)).2 (whereAt e))).trans
      ((meta_face B u (resident e) false).2 ((incoming_home B t e.val).2 e.property))
  have miss (j : Fin half) (yes : incomingBit B u j=true) : ∃e : fibre,address e=j:=by
    unfold incomingBit at yes
    cases hit : localOrigin B u (incomingCandidate B j) with
    | none=>simp [hit,«meta»,face,Meta.blank] at yes
    | some x=>
      rw [hit] at yes
      obtain ⟨e,is,eqn⟩:=incoming_origin B u j x hit
      have atSource:=(meta_face B u x false).1 yes
      rw [is] at atSource
      exact ⟨⟨e,(incoming_home B t e).1 atSource⟩,eqn⟩
  calc
    _ = ∑j ∈ Finset.univ.image address,(incomingBit B u j).toNat:=by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro j _ off
      cases h : incomingBit B u j with
      | false=>rfl
      | true=>obtain ⟨e,rfl⟩:=miss j h;exact False.elim (off (Finset.mem_image.mpr ⟨e,Finset.mem_univ _,rfl⟩))
    _ = ∑e : fibre, (incomingBit B u (address e)).toNat:=Finset.sum_image address.injective.injOn
    _ = _ := by simp [read,fibre]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
