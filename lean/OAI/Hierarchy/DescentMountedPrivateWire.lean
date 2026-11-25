import OAI.Hierarchy.DescentMountedGoodKeys
import OAI.Hierarchy.DescentCableBlockNumber

namespace OAI
namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentRouterSlots DescentBatchedBank DescentBundleHistory DescentBatchedNodeOrder
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
open DescentLaneGates

private theorem privatePort_word {d c p : ℕ} {E : Type} {bits : E → ℕ} (N : Network d E bits)
    (M : ∀a, Network c (DescentNetworkSubstitution.Slot N a) (DescentNetworkSubstitution.slotWidth N a))
    (a : N.Site) (j : (M a).Site) (ref : BlockRef p (boundaryWidth (M a) j))
    (edge : (M a).Edge) (word : ℕ) (read : ref.cableNumber (M a) j = some (edge,word)) :
    let Q := DescentNetworkSubstitution.network N M
    ∃ (wire : Incident Q ⟨a,j⟩) (valid : (word+1)*p ≤ boundaryWidth Q ⟨a,j⟩ (.inl wire)),
      wire.val = .inr ⟨a,edge⟩ ∧ (portMap N M a j).wordBlock ref = ⟨.inl wire,word,valid⟩ := by
  dsimp only
  rcases ref with ⟨port,b,room⟩
  cases port with
  | inr socket => cases read
  | inl old =>
    change some (old.val,b) = some (edge,word) at read
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj read)
    let wire : Incident (DescentNetworkSubstitution.network N M) ⟨a,j⟩ :=
      ⟨.inr ⟨a,old.val⟩,old.property.imp (congrArg (Sigma.mk a)) (congrArg (Sigma.mk a))⟩
    exact ⟨wire,room,rfl,rfl⟩

variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
    {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
    (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
    (key : I↪Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p)
local notation "sel" => selected P G hw pay hardware
local notation "bank" => DescentMixedRouter.network G hw u P.contact P.input P.site P.owner P.align sel D
local notation "prg" => sizedProgram G hw u m p hp fit P.contact P.input P.site P.owner P.align key D sel
variable (s : Bool) (g : P.Good)
local notation "r" => (⟨s,.inl g⟩ : Bool×P.Site)
local notation "sizedHardware" => (fit ▸ hardware : Hardware (K:=K) (C₀:=C₀) (u:=m*p) P G hw pay)
local notation "sizedChoice" => selected P G hw pay sizedHardware s (.inl g)
local notation "trueDevice" => DescentMixedRouter.device G hw (m*p) P.contact P.input P.site P.owner P.align
  (D:=D) sizedChoice
local notation "installedSite" => DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay hardware s g) C₀ bits u
local notation "installedEdge" => DescentCommonPalette.rotorEdgeEquiv G D
  (selectedRotorLayers P G hw pay hardware s g) C₀ bits u
local notation "sizedSite" => DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay sizedHardware s g) C₀ bits (m*p)
local notation "sizedEdge" => DescentCommonPalette.rotorEdgeEquiv G D
  (selectedRotorLayers P G hw pay sizedHardware s g) C₀ bits (m*p)
local notation "prog" v => (DescentBatchedBank.deviceProgram G hw m p hp P.contact P.input P.site P.owner
  P.align key D sizedChoice (sizedSite v))
local notation "widthAt" v => (boundaryWidth trueDevice (sizedSite v))
local notation "venue" v => (⟨r,installedSite v⟩ : (bank).Site)
variable (v : (DescentCommonPalette.rotor G).Site)
local notation "μ" => (fun i => (widthAt v) i / p)
local notation "rack" => DescentRouterBank.network D P.contact P.input P.site P.owner (fun _ : I=>m*p)

theorem mountedGoodPrivate (ref : BlockRef p (widthAt v))
    (edge : (DescentCommonPalette.rotor G).Edge) (word : ℕ)
    (identified : ref.cableNumber trueDevice (sizedSite v) = some (sizedEdge edge,word)) :
    let output := (mountedGoodPorts P G hw pay hardware D m p fit s g v).wordBlock ref
    ∃ (wire : Incident bank (venue v)) (valid : (word+1)*p ≤ boundaryWidth bank (venue v) (.inl wire)),
      wire.val = .inr ⟨r,installedEdge edge⟩ ∧ output = ⟨.inl wire,word,valid⟩ := by
  revert hardware ref identified
  subst u
  intro mounted ref identified
  let levels := selectedRotorLayers P G hw pay mounted s g
  let devices := fun a : (rack).Site =>
    DescentMixedRouter.device G hw (m*p) P.contact P.input P.site P.owner P.align (D:=D)
      (selected P G hw pay mounted a.1 a.2)
  exact privatePort_word rack devices r (DescentCommonPalette.rotorSiteEquiv G D levels C₀ bits (m*p) v)
    ref (DescentCommonPalette.rotorEdgeEquiv G D levels C₀ bits (m*p) edge) word identified

/-- The actual mounted key on a private rotor lane still names that very
rotor cable at the original p-word. -/
theorem mountedGoodPrivateKey
    (source : ∀i,(widthAt v) i=μ i*p)
    (target : ∀i,boundaryWidth bank (venue v) i=boundaryWidth bank (venue v) i/p*p)
    (localNode : (prog v).Node) (j : ℕ) (ref : BlockRef p (widthAt v))
    (edge : (DescentCommonPalette.rotor G).Edge) (word : ℕ)
    (read : ((ofProgram μ source hp (prog v)).keys localNode)[j]?=some (.inl ref))
    (identified : ref.cableNumber trueDevice (sizedSite v) = some (sizedEdge edge,word)) :
    let node:=(mountedGoodNode P G hw pay hardware key D m p hp fit s g v).symm localNode
    ∃ (wire : Incident bank (venue v)) (valid : (word+1)*p ≤ boundaryWidth bank (venue v) (.inl wire)),
      wire.val = .inr ⟨r,installedEdge edge⟩ ∧
      ((ofProgram (fun i=>boundaryWidth bank (venue v) i/p) target hp (prg (venue v))).keys node)[j]?=
        some (.inl ⟨.inl wire,word,valid⟩) :=by
  intro node
  obtain ⟨wire,valid,actual,port⟩:=mountedGoodPrivate P G hw pay hardware D m p fit s g v ref edge word identified
  refine ⟨wire,valid,actual,?_⟩
  exact (mountedGoodIssued P G hw pay hardware key D m p hp fit s g v target source localNode j ref read).trans
    (congrArg (fun b=>some (Sum.inl b)) port)

end
end Hierarchy.DescentChosenRouter

end OAI
