import OAI.Hierarchy.DescentSelectedRotorFace

namespace OAI
/-! The genuine positive directed receiver and the issued short private rotor address. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentResetTrunks DescentStageEdgeReceipt
open DescentSharedCableNames DescentNextSignedWindow DescentSIMDLookup DescentRotorOperandQueryROM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "Q" => DescentCommonPalette.rotor (Z).graph
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "C₀" => blocks B
variable {funded field target lanes span m p : ℕ}
local notation "cfg" => rotorQueryShape B m span field target lanes

/-- Fetching an actual aligned rotor word fixes its signed source or target
even for a loop. The finite layer/batch ticket and the physical incidence are
derived from the same original register. -/
theorem observed_private_rotor_face (proof : B.Recorded funded) (s : Bool) (root : (Z).placement.Good)
    (site : (Q).Site) (node arg within : ℕ) (l : Shape.PrivateLane (Z).graph)
    (x : Fin 3→Cell field) (capRead : (x 0).val=input.placement.cap)
    (chosen : (x 1).val=((Z).goodLabel T root).val.1+1 ∧ (x 2).val%2=0)
    (fetch : ((cfg).flattened (Z).graph C ((Z).circuit s root).layers p node site)[arg]?=some (l,within))
    (registered : ((Z).circuit s root).layers*m≤ span) (room : 2*totalLocal B<2^target) :
    let u:=Stage.home A (hop ((Z).rotorSiteAt T s root site))
    let e:=privateWire B (goodOccurrence B s root l.edge)
    ∃(bound:l.address<span) (face:Roster.Face A ord C₀ u),
      face.val=(e,l.face) ∧ (l.start/p+within)/m<(C₀).count e ∧
      (if l.face then (coarse).graph.dst e else (coarse).graph.src e)=(Z).rotorSiteAt T s root site ∧
      ((cfg).value (Z).graph (s,l.face,(Z).goodLabel T root,l.edge,⟨l.address,bound⟩) x).val=
        (Roster.addr A ord C₀ u (localRoster B u) face).val+1:=by
  intro u e
  obtain ⟨hit,layer,batch,code⟩:=(cfg).flattened_face (Z).graph C _ p node site arg l within fetch
  have offset : l.address=layer.val*m+batch.val := code
  have packed : layer.val*m+batch.val<((Z).circuit s root).layers*m := by
    simpa only [finProdFinEquiv_apply_val,Nat.mul_comm m layer.val,Nat.add_comm] using
      (finProdFinEquiv (layer, (show Fin m from batch))).isLt
  have withinSpan := packed.trans_le registered
  have bound : l.address<span := lt_of_eq_of_lt offset withinSpan
  have home : (if l.face then (coarse).graph.dst e else (coarse).graph.src e)=(Z).rotorSiteAt T s root site:=
    ((Z).rotor_endpoint T s root l.edge l.face).trans (congrArg ((Z).rotorSiteAt T s root) hit)
  have owns : (l.start/p+within)/m<(C₀).count e:=reached_rotor_owns B s root (cfg) l C p _
    node arg within site fetch rfl rfl rfl rfl (Nat.zero_lt_of_lt batch.isLt)
  have host : (if l.face then (C₀).dst e else (C₀).src e)=u:=by
    calc
      _ = Stage.home A (hop (if l.face then (coarse).graph.dst e else (coarse).graph.src e)) := by
        cases l.face <;> rfl
      _ = u := congrArg (fun v : (coarse).graph.Site => Stage.home A (hop v)) home
  let face : Roster.Face A ord C₀ u:=⟨(e,l.face),Nat.zero_lt_of_lt owns,host⟩
  refine ⟨bound,face,rfl,owns,home,?_⟩
  have issued:=rotor_query_at (target:=target) (lanes:=lanes) B proof u s root l.edge m x capRead chosen
    face rfl layer batch withinSpan room
  dsimp only at issued
  have address : (⟨l.address,bound⟩ : Fin span)=⟨layer.val*m+batch.val,withinSpan⟩ := Fin.ext offset
  let valueAt := fun j : Fin span =>
    ((cfg).value (Z).graph (s,l.face,(Z).goodLabel T root,l.edge,j) x).val
  have law := (cfg).registered (Z).graph
    (s,l.face,(Z).goodLabel T root,l.edge,⟨layer.val*m+batch.val,withinSpan⟩) x
  exact (congrArg valueAt address).trans ((congrArg Fin.val law.symm).trans issued)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
