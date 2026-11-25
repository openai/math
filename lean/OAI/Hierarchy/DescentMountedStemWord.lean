import OAI.Hierarchy.DescentMountedContactKey
import OAI.Hierarchy.DescentInstalledRotorStem

namespace OAI
namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentRouterSlots DescentBatchedBank DescentBundleHistory DescentRetainedRangeDigits DescentBatchedNodeOrder
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1600000
open private transportCircuit from OAI.Hierarchy.DescentInstalledNames
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
local notation "sizedSite" => DescentCommonPalette.rotorSiteEquiv G D
  (selectedRotorLayers P G hw pay sizedHardware s g) C₀ bits (m*p)
local notation:max "venue" v:arg => (⟨r,installedSite v⟩ : (bank).Site)
variable (v : (DescentCommonPalette.rotor G).Site)

open DescentLaneGates

local notation "itemEnum" => @Subtype.fintype I (fun a => P.owner s (P.contact a) = Sum.inl g)
  (fun _ => Classical.propDecidable _) inferInstance
local notation "base" => (transportCircuit (b:=itemEnum) (G:=G) (hw:=hw) (pay:=pay) (sizedHardware s g))

open DescentPhysicalSplit DescentLaneGates

/-- Installing the first rotor leg keeps the original external input socket. -/
theorem mountedGood_stem (e : Cells P s g) (ref : BlockRef p (boundaryWidth trueDevice (sizedSite v)))
    (atSite : (trueDevice).attach (rootSlot D P.contact P.input P.site P.owner (fun _ : I=>m*p) s (.inl g)
      (root P.contact P.input P.site P.owner s (.inl g) P.align e))=sizedSite v)
    (inner : ref.port=.inr ⟨_,atSite⟩) :
    ∃port,((mountedGoodPorts P G hw pay hardware D m p fit s g v).wordBlock ref).port=.inr port ∧
      port.val=(s,P.input s e.val) ∧
      ((mountedGoodPorts P G hw pay hardware D m p fit s g v).wordBlock ref).block=ref.block :=by
  revert hardware ref atSite inner
  subst u
  intro mounted ref atSite inner
  let rack₀ := DescentRouterBank.network D P.contact P.input P.site P.owner (fun _ : I => m*p)
  let devices₀ := fun a : rack₀.Site => DescentMixedRouter.device G hw (m*p) P.contact P.input P.site P.owner P.align
    (D:=D) (selected P G hw pay mounted a.1 a.2)
  let here := (DescentCommonPalette.rotorSiteEquiv G D (selectedRotorLayers P G hw pay mounted s g) C₀ bits (m*p)) v
  change ∃port,(portMap rack₀ devices₀ (s,.inl g) here).slot ref.port=.inr port ∧ _
  rw [inner]
  exact ⟨_,rfl,rfl,rfl⟩

local notation "H₀" => Physical.host G.arcs D (selectedRotorLayers P G hw pay sizedHardware s g) C₀ bits (m*p)
local notation "backLane" => DescentBatchedRotor.tapLane D m p hp P.contact P.input P.site P.owner P.align s
  (.inl g) G (head P s g) (tail P s g) base
variable (vertex : Fin (2^n))
variable (i : Fin (DescentPhysicalSplit.count (Physical.host G.arcs D
  (selectedRotorLayers P G hw pay (fit ▸ hardware : Hardware (K:=K) (C₀:=C₀) (u:=m*p) P G hw pay) s g)
  C₀ bits (m*p)) vertex))
local notation "tapSite" => (sizedSite).symm ⟨vertex,.inr i⟩
local notation "rawTap" => (⟨vertex,.inr i⟩ : (trueDevice).Site)
local notation "tapWidth" => boundaryWidth trueDevice rawTap
local notation "tapUnits" => (fun e=>tapWidth e/p)
local notation "gate" t:arg => (mountedGoodNode P G hw pay hardware key D m p hp fit s g tapSite).symm (.inr t)

local notation "legBits_" => @DescentResetGates.legBits (Cells P s g) K itemEnum _ D (m*p) n h bits C₀ G hw pay _ _ base
local notation "color" => DescentLaneGates.Block (selectedRotorLayers P G hw pay sizedHardware s g) m
  (@DescentResetGates.tapBits (Cells P s g) K itemEnum _ D (m*p) n h bits C₀ G hw pay _ _ base vertex i)

open DescentRotorOperandQueryROM.Shape DescentResetPublicOperandBook DescentPhysicalSplit
local notation "src" => source P s g
local notation "dst" => target P s g
local notation "pick" => (Function.Embedding.subtype (fun t=>P.owner s (P.contact t)=.inl g)).trans key
local notation "array" => DescentRotor.Ordered.orderedAddress pick src dst hw
local notation "idx" slot:arg t:arg => (t).2.2.cast (congrArg legBits_ slot)
local notation "req" q:arg t:arg slot:arg digit:arg => (⟨false,q,(t).1.val,(t).2.1.val,(idx slot t).val,digit⟩ : Mouth n)
local notation "rootRows" q:arg => DescentRotorOperandRanks.At src dst (fun a=>a.1=q)
local notation "rank" q:arg t:arg slot:arg digit:arg e:arg => Config.earlierCount src dst pick (req q t slot digit) e

private def inputLayer {E L : Type} [Field L] {keySize n h C₀ bits size : ℕ}
    {board : NonlinearExpanders.Graph n h} {hw : 0<bits} {pay : ℝ}
    {a : Fintype E} {sourceAt targetAt : E → Fin (2^n)}
    (chip : @BaseCircuit E a n h L _ board C₀ bits size hw sourceAt targetAt pay)
    (key : E ↪ Fin keySize) (e : E) : ℕ :=
  letI := a
  (chip.choose (DescentRotor.Ordered.orderedAddress key sourceAt targetAt hw e).1).val

private theorem transport_inputLayer {E L : Type} [Field L] {keySize n h C₀ bits size : ℕ}
    {board : NonlinearExpanders.Graph n h} {hw : 0<bits} {pay : ℝ}
    {a b : Fintype E} {sourceAt targetAt : E → Fin (2^n)}
    (chip : @BaseCircuit E a n h L _ board C₀ bits size hw sourceAt targetAt pay)
    (key : E ↪ Fin keySize) (e : E) :
    inputLayer chip key e = inputLayer (transportCircuit (G:=board) (hw:=hw) (pay:=pay) (b:=b) chip) key e := by
  cases Subsingleton.elim a b
  rfl

theorem sized_layer_count : (hardware s g).layers=selectedRotorLayers P G hw pay sizedHardware s g :=by
  subst u
  exact (selectedRotorLayers_eq P G hw pay hardware s g).symm

/-- Resizing the unit by its true product preserves the chosen layer number. -/
theorem sized_focus_layer (e : Cells P s g) :
    inputLayer (hardware s g) pick e = inputLayer (base) pick e :=by
  subst u
  exact transport_inputLayer (hardware s g) _ _

local instance (priority := high) mountedStemCellsEnum : Fintype (Cells P s g) := itemEnum

/-- The actual selected source leg of a mounted GOOD tap supplies its external
port and its chronological block. Both quantities are determined by the gate. -/
theorem installed_stem_word (q : Fin (2^n)) (slot : name H₀ vertex i=.inl (q,false)) (t : color)
    (targetFit : ∀z,boundaryWidth bank (venue tapSite) z=boundaryWidth bank (venue tapSite) z/p*p)
    (sourceFit : ∀z,tapWidth z=tapUnits z*p) (digit : ℕ)
    (e : Cells P s g) (selected : src e=q ∧ (base).choose (array e).1=t.1 ∧ (array e).2=idx slot t)
    (covered : digit< min 2 (Fintype.card (rootRows q)*m-(rank q t slot digit e*m+t.2.1.val))) :
    let back:=backLane vertex i true ⟨i,t⟩
    ∃ref : BlockRef p (boundaryWidth bank (venue tapSite)),∃port,
      ref.port=.inr port ∧ port.val=(s,P.input s e.val) ∧
      ref.block=rank q t slot digit e*m+t.2.1.val+digit ∧
      ((ofProgram (fun z=>boundaryWidth bank (venue tapSite) z/p) targetFit hp (prg (venue tapSite))).keys (gate t))[back.count tapUnits+digit]?=some (.inl ref) :=by
  intro back
  obtain ⟨l,atSite,issued,atPin⟩:=DescentResetLaneIssue.public_stem_lane D m p hp P.contact P.input P.site P.owner
    P.align s (.inl g) G (head P s g) (tail P s g) (base) key q t.1 t.2.1 (idx slot t) e selected
  obtain ⟨start,extent⟩:=DescentResetLaneIssue.public_focus_word D m p hp P.contact P.input P.site P.owner P.align
    s (.inl g) G (head P s g) (tail P s g) (base) key false q t.1 t.2.1 (idx slot t) digit e selected l issued
  have live : digit<l.count (fun z=>boundaryWidth trueDevice (tap H₀ (.inl (q,false))) z/p):=extent.symm ▸ covered
  obtain ⟨ref,whereAt,word,read⟩:=installed_focus_tap P G hw pay hardware key D m p hp fit s g vertex i q false slot
    t targetFit sourceFit l issued digit live
  let placed:=(congrArg (tap H₀) slot).symm.trans (tap_named H₀ vertex i)
  have rect (a b : (trueDevice).Site) (atTap : a=b) (lane : Lane p (boundaryWidth trueDevice a))
      (rootAt : (trueDevice).attach (rootSlot D P.contact P.input P.site P.owner (fun _ : I=>m*p) s (.inl g)
        (root P.contact P.input P.site P.owner s (.inl g) P.align e))=a)
      (portAt : lane.port=.inr ⟨_,rootAt⟩) :
      (atTap ▸ lane : Lane p (boundaryWidth trueDevice b)).port=.inr ⟨_,rootAt.trans atTap⟩ :=by
    cases atTap
    exact portAt
  obtain ⟨port,atOuter,mark,unchanged⟩:=mountedGood_stem P G hw pay hardware D m p fit s g tapSite e
    ref (atSite.trans placed) (whereAt.trans (rect _ _ placed l atSite atPin))
  exact ⟨_,port,atOuter,mark,unchanged.trans (word.trans (congrArg (·+digit) start)),read⟩

end
end Hierarchy.DescentChosenRouter

end OAI
