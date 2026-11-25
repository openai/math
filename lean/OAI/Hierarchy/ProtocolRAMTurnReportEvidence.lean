import OAI.Hierarchy.ProtocolRAMPaidOriginalEndpoints
import OAI.Hierarchy.ProtocolRAMPaidUsedWalk
import OAI.Hierarchy.ProtocolRAMPaidTurnCoordinates
import OAI.Hierarchy.TaggedWireLiveRoleSides

namespace OAI
/-! # The actual settled report supplies all endpoint and live-incidence checks -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.Report
open AdaptiveProbe Tagged WireTelescope HistoryRoles RoleProgram ProtocolRAM.Calendar CoreRoute
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ProtocolRAMPaidTurnPlacement
open scoped Classical
variable {h W k attempts w R M den : ℕ} {π : Equiv.Perm (Row h)} {U : Widths (siteLast h (2^W) k+1)}
    (Z : Report π (2^W) k w R M den U) (depth : ℕ)
    (mark : ReportSockets.Marks h W k attempts) (uni : ReportSockets.Exclusive mark)
local notation "S" => Z.sampler
local notation "B" => Z.mount
local notation "inj" => (siteNumber h (2^W) k).injective
local notation "pad" => publicChord h (2^W) k
local notation "I" => ProtocolRAMTurnGeometry.Source Z.edges h (2^W) k
local notation "port" => Public S h W k attempts
local notation "before" => SettledMatrix.Layout.available Z.fixed Z.stock Z.reserved Z.used
local notation "amount" => fun i : Fin Z.edges=>(Z.rows i).width

theorem fixed_live_width (i : Fin Z.edges) (on : 0<Z.fixed i) : 0<(Z.rows i).width :=
  Z.named_live_uses_positive (.inl i) on ⟨0, by change 0 < 1; decide⟩

variable (id : {i : Fin Z.edges // 0<(Z.rows i).width} ↪ Catalogue Z.sampler π.symm depth mark)
    (position : ∀ i : {i : Fin Z.edges // 0<(Z.rows i).width},
      filledChord Z.mount.actual (publicChord h (2^W) k) i.val =
        HistoryRoles.sorted Z.sampler π.symm depth mark (.inl (id i)))

def fixedOriginal : {i : Fin Z.edges // 0<Z.fixed i} ↪ Catalogue S π.symm depth mark :=
  (show {i : Fin Z.edges // 0<Z.fixed i} ↪ {i : Fin Z.edges // 0<(Z.rows i).width} from
    ⟨fun i => ⟨i.val, Z.fixed_live_width i.val i.property⟩,
      fun _ _ eq => Subtype.ext
        (congrArg (fun edge : {i : Fin Z.edges // 0 < (Z.rows i).width} => edge.val) eq)⟩).trans id

include position in
theorem fixedOriginal_position (i : {i : Fin Z.edges // 0<Z.fixed i}) :
    filledChord (B).actual pad i.val=sorted S π.symm depth mark (.inl (Z.fixedOriginal depth mark id i)) :=
  position ⟨i.val,Z.fixed_live_width i.val i.property⟩

def beforePay (e : Fin Z.edges) (side : Bool) : port :=
  activePaid S amount (fun i on s=>HistoryRoles.paid S π.symm depth mark uni (id ⟨i,on⟩,s)) e side

theorem beforePay_live (e : {i : Fin Z.edges // 0<Z.fixed i}) (side : Bool) :
    Z.beforePay depth mark uni id e.val side=.inl
      (HistoryRoles.paid S π.symm depth mark uni (Z.fixedOriginal depth mark id e,side)) :=
  activePaid_pos S amount _ e.val (Z.fixed_live_width e.val e.property) side

include position in
theorem start_from_report (src : I) (on : 0<before src) :
    (name (site S (publicRoleFor S π.symm (Z.beforePay depth mark uni id) src false))).val=
      ProtocolRAMTurnEdges.visit B inj pad src 0 := by
  apply original_start S π.symm depth mark uni B pad Z.fixed (Z.fixedOriginal depth mark id)
    (Z.beforePay depth mark uni id) (Z.fixedOriginal_position depth mark id position) (Z.beforePay_live depth mark uni id) src
  rcases src with e|i|c
  · exact on
  · trivial
  · trivial

theorem fixed_from_report (e : {i : Fin Z.edges // 0<Z.fixed i}) :
    ∃flip : Bool,∀side,publicRoleFor S π.symm (Z.beforePay depth mark uni id) (.inl e.val) side=
      .inl (HistoryRoles.paid S π.symm depth mark uni (Z.fixedOriginal depth mark id e,if flip then !side else side)) :=
  paid_original_order S π.symm depth mark uni Z.fixed (Z.fixedOriginal depth mark id)
    (Z.beforePay depth mark uni id) e (Z.beforePay_live depth mark uni id e)

include position in
theorem ends_from_report (order : Orders h (2^W) k) (src : I) (live : 0<before src) (j : ℕ)
    (fits : j<ProtocolRAMTurnGeometry.length src) :
    let x:=ProtocolRAMTurnOccurrence.edgeAt B inj pad order (ProtocolRAMTurnGeometry.origin order src+j)
    let ends:=ProtocolRAMTurnOccurrence.endsAt B inj pad x
    ∃e:Fin Z.edges,∃on:0<(Z.rows e).width,e.val=x ∧
      ProtocolRAMTurnOperands.printed S true (fun b=>Sum.inl (HistoryRoles.paid S π.symm depth mark uni (id ⟨e,on⟩,b))) false true=ends.1 ∧
      ProtocolRAMTurnOperands.printed S true (fun b=>Sum.inl (HistoryRoles.paid S π.symm depth mark uni (id ⟨e,on⟩,b))) true true=ends.2 := by
  intro x ends
  obtain ⟨e,he,on⟩:=used_in_walk B inj pad order amount src (Z.named_live_uses_positive src live) j fits
  change e.val = x at he
  let p (b : Bool) : port := .inl (HistoryRoles.paid S π.symm depth mark uni (id ⟨e,on⟩,b))
  have result:=paid_printed_ends S π.symm depth mark uni B pad e (id ⟨e,on⟩) p (position ⟨e,on⟩) (fun _=>rfl)
  have exactEnds : ends=ProtocolRAMTurnEdges.ends B inj pad e := by
    dsimp only [ends]
    rw [←he]
    simp only [ProtocolRAMTurnOccurrence.endsAt,dite_eq_left e.isLt]
  refine ⟨e,on,he,?_⟩
  rw [exactEnds]
  exact result

end Hierarchy.ProbeStage.CoreBoard.Report
end

end OAI
