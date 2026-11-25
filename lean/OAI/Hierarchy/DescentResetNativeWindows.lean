import OAI.Hierarchy.DescentResetSignedPositions
import OAI.Hierarchy.DescentResetHeaderPlacement
import OAI.Hierarchy.DescentClosedRosterCoverage
import OAI.Hierarchy.DescentNextSignedRAM

namespace OAI
/-! # Eight numeric fields on the executed reset's original mixed cable roster -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentStageEdgeReceipt
open DescentParallelBase DescentResetSignedScan DescentNextSignedWindow DescentCableDonorNames
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "cnt" => fun e : (coarse).graph.Edge =>(coarse).graph.width e/(Z).unit
local notation "world" => (Z).orderedOrdinary T birth
local notation "tape" => (Z).nativeResetEdges T vertexCode birth
local notation "index" => (tape).order.trans Fin.valEmbedding
local notation "dense" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "groups" => S.groupCount (i+1)
local notation "rawSite" => B.raw.siteFrom (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=groups)) dense) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "sparse" => DescentResetLocalOrder.allCode B.raw index S B.valid rawSite
local notation "renameEdge" => DescentPhysicalOrder.rename sparse
local notation "next" => B.reblock.result
local notation "A" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "stream'" => Stage.stream A ord
local notation "board" => Stage.source A ord
local notation "wt" => weight B
local notation "grains" => emit B
local notation "piece'" => piece B
local notation "base'" => first B


open scoped BigOperators
open DescentNextSignedWindow
local notation "C₀" => blocks B
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "live" => fun e : (coarse).graph.Edge=>e∈(coarse).core
local notation "fit" => Stage.measured A ord S B.next.valid
variable (names : Stage.Host (Fin (S.groupCount (i+1))) B.next.V k ↪ ℕ)

open DescentNextSignedWindow.Native
open private DescentResetWindowFields.portOrder from OAI.Hierarchy.DescentResetWindowFields
local notation "face" h => Roster.Face A ord C₀ h
local notation "nativeSlot" => fun h => Roster.addr A ord C₀ h (localRoster B h)
local notation "info" => fun h f => DescentResetWindowFields.record A ord S B.next.valid C₀ live h f
  (DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ h f)
local notation "pos" => sumAt B names (localRoster B)
local notation "raw" => (Z).actualRecord T vertexCode

def candidateRows (h₀ : Host) : Fin (2*totalLocal B)→Option (Record (A).degree (A).cap) :=
  Roster.rows A ord C₀ h₀ (localRoster B h₀) (fun f=>info h₀ f)

theorem candidate_scope (h₀ : Host) (j : Fin (2*(A).cap)) :
    let rs:=candidateRows B names h₀
    let panel:=Stage.signedPanel A ord S B.next.valid names h₀ j
    (panel=none→∀a,(rs a).bind (fun t=>read t j)=none) ∧
    (∀t,panel=some t→∃a,(rs a).bind (fun t=>read t j)=some t ∧
      ∀b,b≠a→(rs b).bind (fun t=>read t j)=none) :=
  DescentResetWindowFields.scope A ord S B.next.valid names C₀ live (emission B) h₀ (localRoster B h₀)
    (DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ h₀)
    (DescentResetWindowFields.near A ord S B.next.valid names C₀ h₀) j

theorem source_neighbor (h₀ : Host) (f₀ : face h₀) :
    (DescentResetWindowFields.neighbor A ord S B.next.valid names C₀ h₀ f₀).val=
      (shortParent B names h₀ (Roster.resident A ord C₀ h₀ f₀)).peer := by
  let j:=DescentResetWindowFields.firstUnit A ord C₀ h₀ f₀
  let u:=Stage.ofPort A ord h₀ (GrainPorts.port A ord C₀ h₀ j)
  have id_ : u.val=(C₀).order j.val.1:=DescentResetWindowFields.portOrder A ord C₀ h₀ j
  have peer : (board).peer h₀ u.val=other C₀ h₀ (Roster.resident A ord C₀ h₀ f₀) := by
    rw [id_]
    simp only [Ends.peer,(C₀).atSource,(C₀).atTarget,other]
    rfl
  let group:=Halo.fromRank (Stage.near A) names (Stage.near_room A)
  change (group.slot h₀ ⟨(board).peer h₀ u.val,_⟩).val=(group.slot h₀ ⟨_,_⟩).val
  exact congrArg (fun v:↥(Stage.near A h₀)=>(group.slot h₀ v).val) (Subtype.ext peer)

/-- Positive physical rows use their real core bit and mass, two measured
positions at this end, and one measured position at the true source. -/
theorem candidate_fields (h₀ : Host) (f₀ : face h₀) :
    let e:=f₀.val.1
    let x:=Roster.resident A ord C₀ h₀ f₀
    let src : Local C₀ ((C₀).src e):=⟨e,f₀.property.1,.inl rfl⟩
    Native.fields (candidateRows B names h₀ (nativeSlot h₀ f₀)) =
      ![(raw e) 0,f₀.val.2.toNat,(shortParent B names h₀ x).peer,(raw e) 6,
        pos false h₀ x,pos true h₀ x,pos false ((C₀).src e) src,(raw e) 5/(Z).unit] := by
  intro e x src
  have record_:=signed_header B e f₀.val.2
  have ⟨first,shared,origin,weight⟩:=three_fields B names (localRoster B) h₀ f₀
  have active : raw e 0=1:=record_.1
  have marked : raw e 6=(decide (e∈(coarse).core)).toNat:=record_.2.2.2.2.2.2
  have units : raw e 5/(Z).unit=(C₀).count e := by
    have width:=record_.2.2.2.2.2.1
    have positive : 0<(Z).unit:=by
      rw [B.unit,←B.next.grain]
      exact Nat.mul_pos B.next.placement.unitPos G.base_pos
    rw [width,Nat.mul_div_cancel _ positive]
  change Native.fields (Roster.rows A ord C₀ h₀ (localRoster B h₀) (fun f=>info h₀ f) (nativeSlot h₀ f₀))=_
  rw [Roster.mounted,active,marked,units]
  have markEq : (info h₀ f₀).marked = decide (e∈(coarse).core) := decide_eq_decide.mpr Iff.rfl
  rw [←source_neighbor B names h₀ f₀,first,shared,origin,←markEq]
  rfl

theorem candidate_hole (h₀ : Host) (slot : Fin (2*totalLocal B))
    (miss : ∀f : face h₀,nativeSlot h₀ f≠slot) : Native.fields (candidateRows B names h₀ slot)=fun _=>0 := by
  have absent : ¬∃f : face h₀,nativeSlot h₀ f=slot:=by rintro ⟨f,h⟩;exact miss f h
  simp [candidateRows,Roster.rows,absent,Native.fields]

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
