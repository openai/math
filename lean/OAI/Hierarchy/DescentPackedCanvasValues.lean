import OAI.Hierarchy.DescentPackedCanvasLift
import OAI.Hierarchy.DescentPackedCanvasRows
import OAI.Hierarchy.DescentPackedFlowHeader
import OAI.Hierarchy.DescentMeasuredPortProof
import OAI.Hierarchy.DescentPaddedFlowWalsh

namespace OAI
/-! # Value of each occupied or empty readout row at the public pitches -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentGL DescentColonies DescentSIMDLookup DescentPackedExchange DescentMeasuredWeights DescentMeasuredHeader
open DescentPackedWalsh DescentWalshPhysical DescentPackedRectangle.Canvas
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k H HP D u l : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W G q ε J V k) (name : V≃Fin H) (digits : Block (u+l)≃J×Block k)
  (hosts : H≤HP) (ports : A.degree≤D) (f K : ℕ)
local notation "m" => u+l
local notation "dep" => GroupStage.MixerHeader.depth A (A.mixerHeader digits name) f
local notation "lev" => inputLevels (k:=m) dep
local notation "bound" => A.wire*(A.z*G.b)*A.cap
private theorem canvasDegreeBound (v : V) : (A.mutual v).card≤A.degree :=
  (Finset.card_filter_le ..).trans (A.degreeBound v)
local notation "cc" => canvasDegreeBound A
local notation "oldloc" => portRow (k:=m) name A.mutual cc dep
local notation "geo" => loc A name digits f hosts ports
local notation "nxt" => neighborSlot (degree:=A.degree) name A.mutual
local notation "ext" => extendedPort (D:=D) hosts nxt
local notation "pub" => Equiv.trans (rowOrd HP m D) (finCongr (Eq.symm (Nat.mul_add HP (m+1) D)))
local notation "sp" => (fun (v : Fin HP) (z : Bits m)=>Padded.load A name digits v (address m z))
local notation "fp" => (fun p : Port HP D=>fun z : Bits m=>Padded.flow A name digits (Prod.snd p) (Prod.fst p) (address m z))
local notation "measure" => (fun (v : V) (z : Bits m)=>A.resetLoad digits v (address m z))
local notation "traffic" => (fun c : Contacts A.mutual=>fun z : Bits m=>A.resetFlow digits (Sigma.fst c) (Subtype.val (Sigma.snd c)) (address m z))
variable (baseDepth : Fin HP→ℕ) (same : ∀v : Fin H,baseDepth (v.castLE hosts)=
    GroupStage.MixerHeader.depth A (A.mixerHeader digits name) f (name.symm v))
    (bounded : ∀v : V,GroupStage.MixerHeader.depth A (A.mixerHeader digits name) f v≤u+l)

theorem Loaded.own_depth {b w : ℕ} (db gb out : ℕ) (mem : Memory w)
    (loaded : Loaded (b:=b) A name digits f K geo db gb out mem) (v : V) :
    mem (db+(name v).val*(m+1))=((dep v):Word w) := by
  let z : Fin (lev v) := ⟨0,Nat.succ_pos _⟩
  let site : Item lev (Contacts A.mutual):=.inl ⟨v,z⟩
  have key : (geo site).val=(name v).val*(m+1) :=
    public_site name lev (fun a => Nat.succ_le_succ (Nat.sub_le m (dep a)))
      (DescentMeasuredWeights.atPort name A.mutual cc) hosts ports v z
  have word := loaded.levels (geo site)
  rw [key, DescentMeasuredWeights.padded_at] at word
  exact word

include same bounded in
theorem true_depth (t:Rows HP m D) :
    (if liveHost (H:=H) t then realDepth baseDepth ext t else 0)=
      padded geo (level lev (inputDepth dep) (pairDepth A.mutual dep)) 0 (pub t) := by
  have actual := seen hosts ports 0 (realDepth (dep∘name.symm) nxt) (realDepth baseDepth ext)
    (depth_at hosts ports (dep∘name.symm) baseDepth same nxt)
    (fun v j h=>by simp [realDepth,extendedPort,Nat.not_lt.mpr h]) t
  have old (i:Fin (H*(m+1)+H*A.degree)) :=
    depth_padded name A.mutual cc dep bounded ((rowOrd H (u+l) A.degree).symm i)
  have agree : realDepth (dep∘name.symm) nxt ∘(rowOrd H (u+l) A.degree).symm=
      padded oldloc (level lev (inputDepth dep) (pairDepth A.mutual dep)) 0 :=
    funext (fun i=>by simpa only [Function.comp_apply,Equiv.apply_symm_apply] using old i)
  refine actual.trans ?_
  rw [agree]
  exact padded_widen oldloc (widen («m»:=u+l) hosts ports) _ 0 (pub t)

include same bounded in
theorem true_gain (t:Rows HP m D) :
    (if liveHost (H:=H) t then realGain baseDepth ext f bound K t else 0)=
      padded geo (gain lev f bound K) 0 (pub t) := by
  have actual := seen hosts ports 0 (realGain (dep∘name.symm) nxt f bound K) (realGain baseDepth ext f bound K)
    (gain_at hosts ports (dep∘name.symm) baseDepth same nxt f bound K)
    (fun v j h=>by simp [realGain,extendedPort,Nat.not_lt.mpr h]) t
  have agree : realGain (dep∘name.symm) nxt f bound K ∘(rowOrd H (u+l) A.degree).symm=padded oldloc (gain lev f bound K) 0 :=
    by
      funext i
      have original := gain_padded name A.mutual cc dep bounded f bound K ((rowOrd H (u+l) A.degree).symm i)
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using original
  refine actual.trans ?_
  rw [agree]
  exact padded_widen oldloc (widen («m»:=u+l) hosts ports) _ 0 (pub t)

include same bounded in
theorem true_load (t:Rows HP m D) : realLoad baseDepth ext sp fp t=
    padded geo (DescentMeasuredWeights.load lev measure traffic) (fun _=>0) (pub t) := by
  let sr (v : Fin H) (z : Bits m):=A.resetLoad digits (name.symm v) (address m z)
  let fl (p : Port H A.degree) (z : Bits m):=raw A name digits p.2 p.1 (address m z)
  have rs (v:Fin H) : sp (v.castLE hosts)=sr v:=by
    funext z
    exact congrArg (fun hit : Option (Fin H) =>
      hit.elim 0 (fun u => A.resetLoad digits (name.symm u) (address m z)))
      (DescentPackedFlowPair.Padded.project_cast hosts v)
  have rf (v:Fin H) (j:Fin A.degree) : fp (v.castLE hosts,j.castLE ports)=fl (v,j):=by
    funext z
    simp only [Padded.flow,DescentPackedFlowPair.Padded.project_cast,Option.elim_some,fl]
  have empty (v:Fin HP) (high:H≤v.val) : sp v=fun _=>0:=by
    funext z;simp [Padded.load,DescentPackedFlowPair.Padded.project,show ¬v.val<H by omega]
  have extended := extend_eq hosts ports (fun _ : Bits m=>0)
    (realLoad (dep∘name.symm) nxt sr fl) (realLoad baseDepth ext sp fp)
    (load_at hosts ports (dep∘name.symm) baseDepth same nxt sr fl sp fp rs rf)
    (load_zero hosts ports baseDepth nxt sp fp empty) t
  have agree : realLoad (dep∘name.symm) nxt sr fl ∘ (rowOrd H (u+l) A.degree).symm =
      padded oldloc (DescentMeasuredWeights.load lev measure traffic) (fun _=>0) := by
    funext i
    have original := load_padded name A.mutual cc dep bounded sr fl measure traffic
      (fun v=>by simp [sr])
      (fun c=>funext (fun z=>raw_contact A name digits cc c (address m z)))
      ((rowOrd H (u+l) A.degree).symm i)
    simpa only [Function.comp_apply,Equiv.apply_symm_apply] using original
  refine extended.trans ?_
  rw [agree]
  exact padded_widen oldloc (widen («m»:=u+l) hosts ports)
    (DescentMeasuredWeights.load lev measure traffic) (fun _=>0) (pub t)

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
