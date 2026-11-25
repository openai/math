import OAI.Hierarchy.DescentLocalArchiveOrder
import OAI.Hierarchy.DescentIssuedDonorChart

namespace OAI
/-! # The physical owner of each carried coefficient node or newly born role -/
namespace Hierarchy.DescentKernelHistory.NodeOrder
open DescentSixParty DescentInitialHost DescentCompiler
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
theorem followNames_site (n : Normalize W) (B : BitDescription W) (x : All (B.follow n)) :
    n.destination ((followNames n B) x).1=x.1 := by
  induction n with
  | done=>rfl
  | split W q m fit rest ih=>exact ih (B.pieces m q fit) x
  | named W s e rest ih=>
    let prev:=followNames rest (B.renamed s e) x
    change rest.destination (s (s.symm prev.1))=x.1
    exact (congrArg rest.destination (s.apply_symm_apply prev.1)).trans (ih _ x)
  | merge W V key flag k g rest ih=>
    let prev:=followNames rest (B.coalesced key flag k g) x
    exact (congrArg rest.destination prev.2.1.property).trans (ih _ x)

theorem castNames_site {U : MarkedWorld F d P bits} (h : W=U) (B : BitDescription W)
    (x : All (cast (congrArg BitDescription h) B)) :
    cast (congrArg (fun A : MarkedWorld F d P bits=>A.graph.Site) h) (castNames h B x).1=x.1 := by
  subst U;rfl
end
end Hierarchy.DescentKernelHistory.NodeOrder

namespace Hierarchy.DescentLocalArchiveOrder
open DescentSixParty DescentSixParty.Chronology DescentKernelHistory DescentCompiler DescentStageEdgeReceipt
open Computability.BorderVNP.Crossing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
variable {u q ε : ℝ} {S : AtomSchedule} {k i z D z' D' wire hist : ℕ}
    {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W)
set_option quotPrecheck false
local notation "r" => BitDescription.scannedRows he T
local notation "next" => (ticket.advance arch).bit
local notation "nodeNames" => NodeOrder.selectedNames arch.bit G (r).pick (fun _=>T.z) (fun _=>T.unitPos)
  (r).fit (fun _=>le_refl T.z) (r).pack ((r).profile c)
local notation "ord" => NodeOrder.followNames n (BitDescription.scanned he T arch.bit c)
local notation "back" => NodeOrder.castNames ((r).state c).symm _

def rawNodeSite : NodeOrder.All arch.bit ⊕ ((r).pairs×Fin 6) → (rawGraph he T c).Site
  | .inl x=>.inl x.1
  | .inr y=>.inr y

def owner (s : NodeOrder.All arch.bit ⊕ ((r).pairs×Fin 6)) : n.result.graph.Site :=
  n.destination (rawInput he T c ((r).state c) (rawNodeSite (he:=he) (T:=T) (c:=c) arch s))

set_option maxHeartbeats 800000 in
theorem roots_owner (x : NodeOrder.All next) : owner (n:=n) arch (roots ticket arch x)=x.1 := by
  let start:=ord x
  let selected:=back start
  let names:=nodeNames
  have site (x : NodeOrder.All arch.bit ⊕ ((r).pairs×Fin 6)) :
      (names.symm x).1=GadgetNetwork.newSite W.graph (r).pick (bestLayout (branchWidth G (fun _=>T.z) ((r).profile c))) (r).pack
        (rawNodeSite (he:=he) (T:=T) (c:=c) arch x) := by
    rcases x with a|⟨i,j⟩
    · exact NodeOrder.selected_site_old ..
    · exact NodeOrder.selected_site_born ..
  have before:=site (names selected)
  rw [names.symm_apply_apply] at before
  have moved:=NodeOrder.castNames_site ((r).state c).symm _ start
  unfold owner rawInput
  change n.destination (cast _ (GadgetNetwork.newSite _ _ _ _ (rawNodeSite arch (names selected))))=_
  rw [←before]
  exact (congrArg n.destination moved).trans (NodeOrder.followNames_site n _ x)

private theorem cast_snd_of_eq {I : Type} {B : I → Type} {a : Σ i, B i} {i : I} {x : B i}
    (h : a = ⟨i, x⟩) (hi : a.1 = i) : cast (congrArg B hi) a.2 = x := by
  cases h
  rfl

/-- The genuine scalar nodes at one output site are exactly the old and born rows
whose two consecutive quotient destinations lead to that site. -/
def fiber (v : n.result.graph.Site) :
    ((next).recipe v).Node ≃ {x : NodeOrder.All arch.bit ⊕ ((r).pairs×Fin 6) //owner (n:=n) arch x=v} where
  toFun x:=⟨roots ticket arch ⟨v,x⟩,roots_owner ticket arch ⟨v,x⟩⟩
  invFun x:=by
    let y:=(roots ticket arch).symm x.val
    have hy : y.1=v := by
      rw [←roots_owner ticket arch y,(roots ticket arch).apply_symm_apply];exact x.property
    exact cast (congrArg (fun s=>((next).recipe s).Node) hy) y.2
  left_inv x:=by
    have h := (roots ticket arch).symm_apply_apply ⟨v,x⟩
    exact cast_snd_of_eq h (congrArg Sigma.fst h)
  right_inv x:=by
    apply Subtype.ext
    let y:=(roots ticket arch).symm x.val
    have hy : y.1=v := by
      rw [←roots_owner ticket arch y,(roots ticket arch).apply_symm_apply];exact x.property
    change roots ticket arch ⟨v,cast _ y.2⟩=x.val
    have eq : (⟨v,cast (congrArg (fun s=>((next).recipe s).Node) hy) y.2⟩ : NodeOrder.All next)=y := by
      rcases y with ⟨i,u⟩;cases hy;rfl
    rw [eq];exact (roots ticket arch).apply_symm_apply x.val

end
end Hierarchy.DescentLocalArchiveOrder

end OAI
