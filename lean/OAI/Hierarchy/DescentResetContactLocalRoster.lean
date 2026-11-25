import OAI.Hierarchy.DescentPrivateLocalRoster

namespace OAI
/-! # Both signed public-contact rows at a physical post-reset receiver -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentResetTrunks DescentResetAttachments DescentDenseHostOrder DescentStageEdgeReceipt
open DescentSharedCableNames DescentRouterSlots DescentHostDirectory
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "height" => GroupStage.depthBound D n f g
local notation "Y" => (2^(Z).n : ℕ)
local notation "same" => funext (fun e=>((Z).allWidths e).symm)

/-- Original physical edge of a public contact, including an unused paid reservation. -/
def contactWire (c : (R).Contact) : (coarse).graph.Edge :=
  (installedWireNames _ (T).home (R).input (T).hub same (Z).bank (Z).tables).symm (.inr (.inr (.inl c)))

/-- Both physical endpoints retain the original coarse block and old vertex of the
particular rotor or exceptional tree where the true socket was installed. -/
theorem contact_endpoint_root (c : (R).Contact) (s : Bool) :
    let e:=contactWire B c
    receiverRoot B (if s then (blocks B).dst e else (blocks B).src e)=
      ((Z).rootVertex T ((R).owner s c),(Z).rootBlock T ((R).owner s c)) := by
  let e:=contactWire B c
  have raw:=sourceFields_read _ (T).home (R).input (T).hub same (Z).bank (Z).tables e
  have key : installedWireNames _ (T).home (R).input (T).hub same (Z).bank (Z).tables e=
      .inr (.inr (.inl c)):=Equiv.apply_symm_apply _ _
  rw [key] at raw
  let root (v : (coarse).graph.Site) := (position (Z).graph ((Z).placed T v).val,(Z).blockId T v)
  cases s
  · let node:=((Z).bank.src (.inl c)).2
    have endpoint : (coarse).graph.src e=(Z).privateSiteAt T false ((R).owner false c) node :=
      (Equiv.eq_symm_apply _).2 (congrArg RawFields.src raw)
    exact ((congrArg (receiverRoot B) (named_home B ((coarse).graph.src e))).trans
      (receiverRoot_site B _)).trans ((congrArg root endpoint).trans (root_at_private_site B false ((R).owner false c) node))
  · let node:=((Z).bank.dst (.inl c)).2
    have endpoint : (coarse).graph.dst e=(Z).privateSiteAt T true ((R).owner true c) node :=
      (Equiv.eq_symm_apply _).2 (congrArg RawFields.dst raw)
    exact ((congrArg (receiverRoot B) (named_home B ((coarse).graph.dst e))).trans
      (receiverRoot_site B _)).trans ((congrArg root endpoint).trans (root_at_private_site B true ((R).owner true c) node))

/-- The physically selected output column or its exceptional tree's actual leaf. -/
def contactSocket (s : Bool) : (R).Contact→Fin Y ⊕ Fin (2^height)
  | .inl c=>.inl (((R).outputName (T).commonDepth s c).2)
  | .inr c=>.inr (DescentResetCableSlots.leaf (R) height (T).bookHeight s
      (fallEnd (R) s c) (fallLeg (R) s c))

theorem contact_unique (s : Bool) {a b : (R).Contact}
    (owner : (R).owner s a=(R).owner s b)
    (socket : contactSocket B s a=contactSocket B s b) : a=b := by
  cases a with
  | inl a=>
    cases b with
    | inr b=>cases socket
    | inl b=>
      apply congrArg Sum.inl
      apply slot_unique (R).b (R).keys (R).hub (R).ends (R).span (R).room s
      have sameRoot:=Sum.inl.inj owner
      have num:=Sum.inl.inj socket
      let a₀:=slot (R).b (R).keys (R).hub (R).ends (R).span (R).room s a
      let b₀:=slot (R).b (R).keys (R).hub (R).ends (R).span (R).room s b
      change a₀.1=b₀.1 at sameRoot
      change (R).columns s a₀.1 a₀.2=(R).columns s b₀.1 b₀.2 at num
      rw [←sameRoot] at num
      exact Prod.ext sameRoot (((R).columns s a₀.1).injective num)
  | inr a=>
    cases b with
    | inl b=>cases socket
    | inr b=>
      have ends : fallEnd (R) s a=fallEnd (R) s b:=Sum.inr.inj owner
      have num:=Sum.inr.inj socket
      let ta:=fallEnd (R) s a
      let tb:=fallEnd (R) s b
      have bridge (u v : (Z).Fallback) (eqn : u=v)
          (x : LinkId (R).owner s (.inr u)) (y : LinkId (R).owner s (.inr v))
          (eqLeaf : DescentResetCableSlots.leaf (R) height (T).bookHeight s u x=
              DescentResetCableSlots.leaf (R) height (T).bookHeight s v y) : x.val=y.val := by
        subst v
        exact congrArg Subtype.val ((DescentResetCableSlots.leaf (R) height (T).bookHeight s u).injective eqLeaf)
      exact bridge ta tb ends (fallLeg (R) s a) (fallLeg (R) s b) num

abbrev ContactAt (u : Host) := {c : (R).Contact //
  (blocks B).src (contactWire B c)=u ∨ (blocks B).dst (contactWire B c)=u}

def contactSide {u : Host} (x : ContactAt B u) : Bool :=
  decide ((blocks B).src (contactWire B x.val)≠u)

theorem contact_at_root {u : Host} (x : ContactAt B u) :
    receiverRoot B u=
      ((Z).rootVertex T ((R).owner (contactSide B x) x.val),(Z).rootBlock T ((R).owner (contactSide B x) x.val)) := by
  let c:=x.val
  by_cases hs : (blocks B).src (contactWire B c)=u
  · have which : contactSide B x=false:=by change decide ((blocks B).src (contactWire B c)≠u)=false;simp [hs]
    rw [which]
    simpa only [Bool.false_eq_true,ite_false,hs] using contact_endpoint_root B c false
  · have ht : (blocks B).dst (contactWire B c)=u:=x.property.resolve_left hs
    have which : contactSide B x=true:=by exact decide_eq_true hs
    rw [which]
    simpa only [Bool.true_eq,ite_true,ht] using contact_endpoint_root B c true

/-- The fiber is bounded even if many old edges purchased the same contact. The choice
of side makes a self-loop a single candidate; signed expansion handles both incidences. -/
def contact_local_chart (u : Host) :
    ContactAt B u ↪ Bool × ResetInput.RootTicket Z T × (Fin Y ⊕ Fin (2^height)) where
  toFun x:=let s:=contactSide B x
           (s,(Z).rootTicket T ((R).owner s x.val),contactSocket B s x.val)
  inj' := by
    intro x y eqn
    have sides : contactSide B x=contactSide B y:=congrArg Prod.fst eqn
    have tickets:=congrArg (fun z=>z.2.1) eqn
    have sockets:=congrArg (fun z=>z.2.2) eqn
    dsimp only at tickets sockets
    have sameRoot:=(contact_at_root B x).symm.trans (contact_at_root B y)
    rw [←sides] at sameRoot tickets sockets
    apply Subtype.ext
    apply contact_unique B (contactSide B x) _ sockets
    apply ((Z).rootLocation T vertexCode).injective
    exact Prod.ext (congrArg vertexCode (congrArg Prod.fst sameRoot)) (Prod.ext (congrArg Prod.snd sameRoot) tickets)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
