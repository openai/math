import OAI.Hierarchy.DescentOrdinaryChildFields
import OAI.Hierarchy.DescentSignedRosterWindows

namespace OAI
/-! # Numeric ordinary successor windows on the actual source-grouped stage -/
namespace Hierarchy.DescentOrdinaryWindowFields
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings DescentOrdinarySiblingSerial DescentParallelBase
open private DescentOrdinarySiblingSerial.physicalBase DescentOrdinarySiblingSerial.physicalKey
  from OAI.Hierarchy.DescentOrdinarySiblingSerial
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
set_option Elab.async false
set_option maxHeartbeats 1200000
private theorem transport_first {H E : Type} [DecidableEq H] [Fintype E] {n cap : ℕ}
    {B : Ends H n} (C : Blocks B E) (terms : ∀ h, (B.incident h).card ≤ cap)
    (u : E) (hu : 0 < C.count u) (home : H) (src : C.src u = home) :
    (B.position terms home (Incidence.candidate C home ⟨u,hu,Or.inl src⟩ ⟨0,hu⟩)).val =
      (B.position terms (C.src u) (Incidence.candidate C (C.src u) ⟨u,hu,Or.inl rfl⟩ ⟨0,hu⟩)).val := by
  subst home
  rfl

private theorem if_decided (p : Prop) [Decidable p] (x y : ℕ) :
    (if p then x else y) = (if decide p then x else y) := by
  by_cases hp : p <;> simp [hp]

variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
local notation "sel" => W.selected G pick z hz fit pack p
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
local notation "coarse" => coalesced sel key flag k g
local notation "world" => DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected
variable (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
local notation "sparse" => DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site
local notation "next" => PhysicalRename.rankedWorld world site sparse
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {stage : ℕ} {price ε : ℝ}
variable (A : GroupStage
    (PhysicalRename.rankedWorld
      (DescentOrdinarySiblingSerial.physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
      (DescentOrdinarySiblingSerial.physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site))
    G price ε J V stage)
local notation "ord" => originalId (next).graph.Edge
local notation "stream'" => Stage.stream A ord
local notation "B" => Stage.source A ord

open DescentOrdinaryParentBlocks DescentNextSignedWindow DescentOrdinaryChildFields
variable {i : ℕ} (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i) (names : Stage.Host J V stage↪ℕ) (qp:0<q)
local notation "C₀" => blocks W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp
local notation "wt" => weight W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
local notation "grain" => emit W G edge pair pick z hz fit pack p key flag k g q old picked affected site A
local notation "terms" => Stage.measured A ord S ready
local notation "live" => DescentPackedOperand.Public.endpoint A ord S ready names

local notation "Host" => Stage.Host J V stage
local notation "Face" => Roster.Face A ord C₀
local notation "unit" => GrainPorts.Unit A ord C₀

/-- The count-only common peer scan, the directed all-neighbor scan and
its source-side quantity have separate physical interpretations. -/
def record (h:Host) (u:Face h) (neighbor:Fin A.degree) : Record A.degree A.cap :=
  let e:=u.val.1
  let first_:Fin (wt e):=⟨0,u.property.1⟩
  let entry:=Roster.resident A ord C₀ h u
  let root:=(C₀).src e
  let src:Local C₀ root:=⟨e,u.property.1,Or.inl rfl⟩
  { side:=u.val.2, neighbor:=neighbor, marked:=decide (e∈(coarse).core),
    count:=wt e,position:=((B).position terms h (Incidence.candidate C₀ h entry first_)).val,
    shared:=(B).serial ((C₀).src e) ((C₀).dst e) ((C₀).order ⟨e,first_⟩),
    atSource:=((B).position terms root (Incidence.candidate C₀ root src first_)).val }

local notation "rawRecord" => record W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready qp

def face (h:Host) (t:unit h) : Face h:=⟨(t.val.1.1,t.val.2),Nat.zero_lt_of_lt t.val.1.2.isLt,t.property⟩

local notation "face'" => face W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp

/-- A literal successor peer number suffices to interpret every other field.
That number is the digit produced by `DescentPackedChildNeighbor.SIMD.issued_digit`. -/
theorem render_actual (h:Host) (t:unit h) (neighbor:Fin A.degree)
    (peer:(Stage.live A ord S ready names h (GrainPorts.port A ord C₀ h t)).neighbor=neighbor):
    render (rawRecord h (face' h t) neighbor) t.val.1.2.val=some (Stage.live A ord S ready names h (GrainPorts.port A ord C₀ h t)):=by
  let u:=t.val.1.1
  let j:=t.val.1.2
  let side:=t.val.2
  have actual:Stage.live A ord S ready names h (GrainPorts.port A ord C₀ h t)=live side (grain ⟨u,j⟩):=by
    apply (GrainPorts.at_end A ord C₀ h S ready names t).trans
    exact congrArg (live side) ((stream').symm_apply_apply (grain ⟨u,j⟩))
  rw [actual] at peer ⊢
  have md:=metadata W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready names u j side
  apply «matches» (rawRecord h (face' h t) neighbor) j _ peer
  · exact serial W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready names qp u j side
  · have origin:=sourceWire W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready names qp u j side
    have homeEq:=src_at W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qp u j
    exact origin.trans (congrArg₂ Nat.add
      (transport_first C₀ terms u (Nat.zero_lt_of_lt j.isLt) _ homeEq.symm)
      (if_decided (u ∈ (coarse).core) j.val 0))
  · exact md.1.trans (if_decided (u ∈ (coarse).core) 0 j.val)
  · exact md.2.1
  · exact md.2.2

/-- All native window selectors now follow from the real roster, the six
short numeric parent columns and one measured neighbor for every lane. -/
theorem scope {c:ℕ} (h:Host) (addr:Local C₀ h↪Fin c) (neighbor:Face h→Fin A.degree)
    (near:∀t:unit h,(Stage.live A ord S ready names h (GrainPorts.port A ord C₀ h t)).neighbor=neighbor (face' h t))
    (j:Fin (2*A.cap)):
    let info:=fun f=>rawRecord h f (neighbor f)
    let rows:=Roster.rows A ord C₀ h addr info
    let panel:=Stage.signedPanel A ord S ready names h j
    (panel=none→∀a,(rows a).bind (fun r=>read r j)=none) ∧
    (∀t,panel=some t→∃a,(rows a).bind (fun r=>read r j)=some t ∧ ∀b,b≠a→(rows b).bind (fun r=>read r j)=none):=by
  intro info rows panel
  have weight (f:Face h):(info f).count=(C₀).count f.val.1:=rfl
  let eqv:=Roster.physical A ord C₀ h addr info weight
  apply DescentNextSignedWindow.complete A ord S ready names C₀ h rows eqv _ _ j
  · intro t
    have dataEq := Roster.physical_data A ord C₀ h addr info weight t
    have offsetEq := congrArg Prod.snd (Roster.physical_at A ord C₀ h addr info weight t)
    exact (GrainPorts.address A ord C₀ h S ready t).trans (congrArg₂ Nat.add
      (congrArg (fun r : Record A.degree A.cap => number A.cap r.side r.position) dataEq.symm) offsetEq.symm)
  · intro t
    have dataEq := Roster.physical_data A ord C₀ h addr info weight t
    have offsetEq := congrArg Prod.snd (Roster.physical_at A ord C₀ h addr info weight t)
    exact (congrArg₂ render dataEq offsetEq).trans
      (render_actual W G edge pair pick z hz fit pack p key flag k g q old picked affected site A S ready names qp h t _ (near t))

end
end Hierarchy.DescentOrdinaryWindowFields

end OAI
