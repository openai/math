import OAI.Hierarchy.DescentPrivateLocalRoster
import OAI.Hierarchy.DescentResetLocalRoster

namespace OAI
/-! # A concrete local roster on the named and reblocked reset graph -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks DescentSharedCableNames
open scoped Classical
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

def motherNames : (coarse).graph.Edge ≃
    (Bool×(old).graph.Edge) ⊕ ((Z).Fallback ⊕ ((placement).Contact ⊕ PrivateOccurrence B)) := wires

def stemParent (x : Bool×(old).graph.Edge) : (coarse).graph.Edge := (motherNames B).symm (.inl x)
def trunkParent (t : (Z).Fallback) : (coarse).graph.Edge := (motherNames B).symm (.inr (.inl t))
def contactParent (c₀ : (placement).Contact) : (coarse).graph.Edge := (motherNames B).symm (.inr (.inr (.inl c₀)))

theorem private_parent (x : PrivateOccurrence B) :
    (motherNames B).symm (.inr (.inr (.inr x)))=privateWire B x := rfl

/-- The hardware cell at a receiver gives the old host and coarse coordinate
on either end of an incoming cable. -/
theorem endpoint_root (e : (coarse).graph.Edge) :
    receiverRoot B ((blocks B).src e)=
      (position (Z).graph ((Z).commonName T ((coarse).graph.src e)),(Z).blockId T ((coarse).graph.src e)) ∧
    receiverRoot B ((blocks B).dst e)=
      (position (Z).graph ((Z).commonName T ((coarse).graph.dst e)),(Z).blockId T ((coarse).graph.dst e)) := by
  have cell (v : (coarse).graph.Site) :
      receiverRoot B (Stage.home B.next.placement (hop v))=
        (position (Z).graph ((Z).commonName T v),(Z).blockId T v) := by
    exact (congrArg (receiverRoot B) (named_home B v)).trans (receiverRoot_site B v)
  exact ⟨cell _,cell _⟩

theorem stem_receiver_root (s : Bool) (j : (old).graph.Edge) :
    let e:=stemParent B (s,j)
    let t:=(T).home (ends (old).graph s j)
    receiverRoot B ((blocks B).src e)=(((T).code t).1,(Z).rootBlock T (.inr t)) ∧
    receiverRoot B ((blocks B).dst e)=(((T).code t).1,(Z).rootBlock T (.inr t)) := by
  let e:=stemParent B (s,j)
  let t:=(T).home (ends (old).graph s j)
  have blockRead:=congrArg (fun z : ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×Bool=>z.2.2.2.1)
    ((Z).stemArchive T vertexCode key s j)
  have leftBlock : (Z).blockId T ((coarse).graph.src e)=(Z).rootBlock T (.inr t):=Fin.ext blockRead
  have rightBlock : (Z).blockId T ((coarse).graph.dst e)=(Z).rootBlock T (.inr t):=
    ((Z).block_edges T e).symm.trans leftBlock
  have shape:=(Z).stemFields T s j
  have left:=congrArg RawFields.src shape
  have right:=congrArg RawFields.dst shape
  have address:=DescentChosenRouter.public_read (placement) (T).code (T).source s j
  rw [←(T).attach] at address
  have owner (p : (placement).Public) :
      position (Z).graph (publicNode (placement) (Z).graph (T).commonDepth (T).code s p)=
       (DescentChosenRouter.publicAddress (placement) (T).code p).1 := by
    rcases p with ⟨g,j⟩|t <;> rfl
  obtain ⟨first,last⟩:=endpoint_root B e
  refine ⟨first.trans (Prod.ext ?_ leftBlock),last.trans (Prod.ext ?_ rightBlock)⟩
  · exact congrArg (position (Z).graph) left
  · exact (congrArg (position (Z).graph) right).trans ((owner _).trans (congrArg Prod.fst address))

/-- At either end of one original trunk, the original terminal is determined
by the physical site. Its two endpoints are the two tagged copies of that terminal. -/
theorem trunk_nodes (t : (Z).Fallback) :
    let e:=trunkParent B t
    let names:=installedNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
    names ((coarse).graph.src e)=.inl (false,t) ∧ names ((coarse).graph.dst e)=.inl (true,t) := by
  let e:=trunkParent B t
  have data:=sourceFields_read (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables e
  change physicalFields _ _ _ _ _ _ _ e=sourceFields _ _ _ _ _ ((wires) ((wires).symm (.inr (.inl t)))) at data
  rw [Equiv.apply_symm_apply] at data
  exact ⟨congrArg RawFields.src data,congrArg RawFields.dst data⟩

theorem same_site {v₁ v₂ : (coarse).graph.Site}
    (eqHome : Stage.home B.next.placement (hop v₁)=Stage.home B.next.placement (hop v₂)) : v₁=v₂ :=
  (hop).injective (B.next.valid.coordinates eqHome)

theorem trunk_eq {u : Host} {t v : (Z).Fallback}
    (one : (blocks B).src (trunkParent B t)=u ∨ (blocks B).dst (trunkParent B t)=u)
    (two : (blocks B).src (trunkParent B v)=u ∨ (blocks B).dst (trunkParent B v)=u) : t=v := by
  let names:=installedNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
  have st:=trunk_nodes B t
  have sv:=trunk_nodes B v
  rcases one with a|a <;> rcases two with b|b
  · have eqn:=congrArg names (same_site B (a.trans b.symm))
    rw [st.1,sv.1] at eqn;exact congrArg Prod.snd (Sum.inl.inj eqn)
  · have eqn:=congrArg names (same_site B (a.trans b.symm))
    rw [st.1,sv.2] at eqn;exact congrArg Prod.snd (Sum.inl.inj eqn)
  · have eqn:=congrArg names (same_site B (a.trans b.symm))
    rw [st.2,sv.1] at eqn;exact congrArg Prod.snd (Sum.inl.inj eqn)
  · have eqn:=congrArg names (same_site B (a.trans b.symm))
    rw [st.2,sv.2] at eqn;exact congrArg Prod.snd (Sum.inl.inj eqn)

def trunk_chart (u : Host) : Part (blocks B) u (trunkParent B) ↪Fin 1 :=
  ⟨fun _=>0,fun a b _=>Subtype.ext (trunk_eq B a.property.2 b.property.2)⟩

def hidden_chart (u : Host) :
    Part (blocks B) u (privateWire B) ↪Fin (2*(rootSlots ((Z).k-(T).commonDepth) (2^(Z).n)*capacity)) :=
  let take : Part (blocks B) u (privateWire B) ↪
    {x : PrivateOccurrence B // (blocks B).src (privateWire B x)=u ∨ (blocks B).dst (privateWire B x)=u} :=
    ⟨fun x=>⟨x.val,x.property.2⟩,fun _ _ eqn=>Subtype.ext (Subtype.mk.inj eqn)⟩
  take.trans ((private_local_chart B u).trans (localPrivateId _ _ _))

/-- No duplicates across the old, trunk, contact and private sectors. -/
def rawLocalRoster (u : Host) {a b : ℕ}
    (stems : Part (blocks B) u (stemParent B)↪Fin a)
    (contacts : Part (blocks B) u (contactParent B)↪Fin b) :
    Local (blocks B) u↪Fin (a+(1+(b+2*(rootSlots ((Z).k-(T).commonDepth) (2^(Z).n)*capacity)))) :=
  addresses (blocks B) u (motherNames B) stems (trunk_chart B u) contacts (hidden_chart B u)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
