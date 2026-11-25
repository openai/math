import OAI.Hierarchy.DescentActorDestination
import OAI.Hierarchy.DescentOrdinaryHubRows

namespace OAI
/-! # The physical target rack, group and block of every ordinary actor -/
namespace Hierarchy.DescentStageEdgeReceipt
open DescentKernelHistory DescentSixParty DescentHostDirectory
noncomputable section
variable {F H P : Type} [Field F] [Fintype H] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
    {W : MarkedWorld F d P bits} {G : PoweredGadget F} {u ε : ℝ} {he : 0≤ε} {T : StageInput W G u ε}
theorem IssuedDonorChart.merged_agree (b b' : IssuedDonorChart he T H) (c : (T.result he).Choice) (k g : ℕ)
    (x : (scanWorld he T c).graph.Site) :
    mergeHub b.hub k g (b.key he T c x)=mergeHub b'.hub k g (b'.key he T c x) := by
  have col : b.col=b'.col := eq_of_heq (b.native.trans b'.native.symm)
  have key : b.key he T c=b'.key he T c := by
    unfold IssuedDonorChart.key
    rw [col]
  obtain ⟨y,hy⟩:=b.key_host he T c x
  have flag : b.hub (b.key he T c x).1=b'.hub (b.key he T c x).1 := by
    rw [hy]
    exact (b.old y).2.trans (by rw [col];exact (b'.old y).2.symm)
  rw [←key]
  simp only [mergeHub,flag]
end
end Hierarchy.DescentStageEdgeReceipt

namespace Hierarchy.DescentSixParty.GroupStage
open Computability.BorderVNP.Crossing DescentKernelHistory DescentStageEdgeReceipt DescentHostDirectory DescentHostDegree DescentColonies GadgetNetwork DescentNetworkPartition
noncomputable section
variable {F P J J₁ V V₁ : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype J₁] [DecidableEq J₁]
  [Fintype V] [DecidableEq V] [Fintype V₁] [DecidableEq V₁]
  {d k l : ℕ} {bits : P→ℕ} {G : PoweredGadget F} {W Y : MarkedWorld F d P bits} {price ε u : ℝ}
  (A : GroupStage W G price ε J V k) (he : 0≤ε) (T : StageInput W G u ε) (c : (T.result he).Choice)
local notation "r" => BitDescription.scannedRows he T
local notation "venue" => GadgetNetwork.newSite W.graph (BitDescription.ScanRows.pick r) (bestLayout (branchWidth G (fun _=>T.z) ((BitDescription.ScanRows.profile r) c))) (BitDescription.ScanRows.pack r)

def VenueRows (digits : J≃J₁×Block l) {U : MarkedWorld F d P bits} (n : Normalize U)
    (next : GroupStage n.result G price ε J₁ V₁ l) (chart : V₁↪Key V) : Prop :=
  ∀ (state : U=scanWorld he T c) (b : IssuedDonorChart he T (J×V)) (x : (rawGraph he T c).Site),
    let w:=n.destination (rawInput he T c state x)
    let addr:=splitKey (mergeHub b.hub k (gainExponent 20 A.degree) (b.key he T c (venue x)))
    ((next.pos w).1,next.block w)=digits addr.1 ∧ chart (next.pos w).2=addr.2

theorem next_afterNames {U : MarkedWorld F d P bits} (n : Normalize U) (next : GroupStage n.result G price ε J₁ V₁ l)
    (s : Equiv.Perm n.result.graph.Site) (e : Equiv.Perm n.result.graph.Edge) (v : U.graph.Site) :
    let result:=GroupStage.afterNames n next s e
    (result.pos ((n.appendNames s e).destination v),result.block ((n.appendNames s e).destination v))=
      (next.pos (n.destination v),next.block (n.destination v)) := by
  induction n with
  | done W=>
    let x : (Normalize.done W).result.graph.Site := v
    exact congrArg (fun y => (next.pos y, next.block y)) (s.symm_apply_apply x)
  | split W q m fit rest ih=>exact ih next s e v
  | named W a b rest ih=>exact ih next s e (a v)
  | merge W V key flag k g rest ih=>exact ih next s e (MarkedWorld.address W key flag k g v)

theorem VenueRows.named (digits : J≃J₁×Block l) {U : MarkedWorld F d P bits} {n : Normalize U}
    (next : GroupStage n.result G price ε J₁ V₁ l) (chart : V₁↪Key V)
    (s : Equiv.Perm n.result.graph.Site) (e : Equiv.Perm n.result.graph.Edge)
    (rows : VenueRows A he T c digits n next chart) :
    VenueRows A he T c digits (n.appendNames s e) (GroupStage.afterNames n next s e) chart := by
  intro state b x
  have h:=next_afterNames n next s e (rawInput he T c state x)
  exact ⟨(congrArg (fun z=> (z.1.1,z.2)) h).trans (rows state b x).1,
    (congrArg (fun z=>chart z.1.2) h).trans (rows state b x).2⟩

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
