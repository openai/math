import OAI.Hierarchy.ProtocolRAMTurnReportEvidence
import OAI.Hierarchy.TaggedWireTerminalOriginal
import OAI.Hierarchy.TaggedWireTerminalPorts

namespace OAI
/-! # The two exact labelled socket numbers written for each positive terminal role -/
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
namespace Hierarchy.ProtocolRAMPaidTurnPlacement
open ProbeStage CoreBoard AdaptiveProbe HistoryRoles RoleProgram WireTelescope ProtocolRAM.Calendar
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open scoped Classical
variable {h W k attempts edges : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : ReportSockets.Marks h W k attempts) (uni : ReportSockets.Exclusive mark)
local notation "I" => Commodity (Fin (2^h)) (Stages h (2^W)) k
local notation "C" => Columns h (2^W)×Fin k
local notation "raw" => HistoryRoles.Source S π depth mark
local notation "physical" => HistoryRoles.physical S π depth mark uni
local notation "sides" => HistoryRoles.swap S π depth mark
local notation "code" => RoleProgram.labelled S

theorem printed_physical (x : raw) (age b : Bool) :
    ProtocolRAMTurnOperands.printed S age (fun s=>physical (x,s)) b false=
      code age (physical (x,sides x b)) := by
  simp only [ProtocolRAMTurnOperands.printed,HistoryRoles.physical_site,Incident.choose,HistoryRoles.swap]
 ; rfl

theorem physical_named (x : raw) (b : Bool) :
    name (site S (physical (x,sides x b)))=(portGraph _).vertex (sorted S π depth mark x) b := by
  rw [physical_site]
  by_cases lt:name (physicalEnds S π depth mark x).1<name (physicalEnds S π depth mark x).2
  all_goals cases b <;> simp [swap,sorted,orderedChord,Incident.choose,portGraph,PortGraph.vertex,lt]

theorem printed_normalized (p : Bool→Public S h W k attempts) (b : Bool)
    (sep : name (site S (p false))≠name (site S (p true))) :
    ProtocolRAMTurnOperands.printed S false
      (fun side=>p (if name (site S (p false))<name (site S (p true)) then side else !side)) b false=
      ProtocolRAMTurnOperands.printed S false p b false := by
  by_cases ab:name (site S (p false))<name (site S (p true))
  · simp only [ite_eq_left ab]
  · simp only [ite_eq_right ab]
    exact printed_swap S p b sep

variable (fixed : Fin edges→ℕ) (stock : Commodity (Fin (2^h)) (Stages h (2^W)) k→ℕ)
    (res used : (Columns h (2^W)×Fin k)→ℕ)
    (ident : {e // 0<fixed e} ↪ Catalogue S π depth mark) (pay : Fin edges→Bool→Public S h W k attempts)
    (paid : ∀e : {e // 0<fixed e},∀b,pay e.val b=.inl (HistoryRoles.paid S π depth mark uni (ident e,b)))
local notation "width" => SettledMatrix.Layout.bits fixed stock res used
local notation "rawWidth" => SettledMatrix.Layout.available fixed stock res used
local notation "num" => SettledMatrix.Layout.numbered (r:=edges) («I»:=I) (A:=C)
local notation "before" => fun i (_ : 0<width i)=>publicRoleFor S π pay (num i)
local notation "role" => Terminal.ports S π depth mark uni fixed stock res used ident
local notation "src" => NamedAperture.liftRow fixed (Sum.elim stock (fun i=>res i-used i)) ident

private theorem nonfixed_role (u : I⊕C) :
    publicRoleFor S π pay (.inr u) = fun s=>physical (.inr u,s) := by
  cases u <;> rfl

attribute [local irreducible] ProtocolRAMTurnOperands.printed RoleProgram.labelled

set_option maxHeartbeats 1800000 in
include ident paid in
private theorem input_printed (z : {x : Fin edges⊕(I⊕C) // 0<rawWidth x}) (b : Bool) :
    ProtocolRAMTurnOperands.printed S false (publicRoleFor S π pay z.val) b false=
      code false (physical (src z,sides (src z) b)) := by
  rcases z with ⟨(e|u),on⟩
  · let x : raw:=.inl (ident ⟨e,on⟩)
    let p := fun s=>physical (x,s)
    have rep : pay e=p := funext (paid ⟨e,on⟩)
    have sep : name (site S (p false))≠name (site S (p true)) := by
      apply name.injective.ne
      intro eq
      have left : site S (p false)=(physicalEnds S π depth mark x).1:=physical_site S π depth mark uni x false
      have right : site S (p true)=(physicalEnds S π depth mark x).2:=physical_site S π depth mark uni x true
      exact physical_distinct S π depth mark x (left.symm.trans (eq.trans right))
    let normalize (f : Bool→Public S h W k attempts) := fun s=>
      f (if name (site S (f false))<name (site S (f true)) then s else !s)
    exact (congrArg (fun f=>ProtocolRAMTurnOperands.printed S false (normalize f) b false) rep).trans
      ((printed_normalized S p b sep).trans (printed_physical S π depth mark uni x false b))
  · exact (congrArg (fun f=>ProtocolRAMTurnOperands.printed S false f b false)
        (nonfixed_role S π depth mark uni pay u)).trans
      (printed_physical S π depth mark uni (.inr u) false b)

include paid in
theorem original_code (i : Fin (Fintype.card (Fin edges⊕(I⊕C)))) (b : Bool) :
    ProtocolRAMTurnStepOrder.liveCode S false width before i b=
      if on : 0<width i then code false (role ⟨(i,b),on⟩) else 0 := by
  by_cases on:0<width i
  · simp only [ProtocolRAMTurnStepOrder.liveCode,dite_eq_left on]
    exact input_printed S π depth mark uni fixed stock res used ident pay paid ⟨num i,on⟩ b
  · simp only [ProtocolRAMTurnStepOrder.liveCode,dite_eq_right on]

variable {M : ℕ} (board : CatalogueRows.Board) (order : Fin board.coreRows≃Edges S h (2^W) k)
    (acquired : ReportSockets.Bought S π depth mark→Fin board.boughtRows) (rows : Fin board.rows→ProtocolRAMEmit.Row)
    (receipt : CatalogueRows.Alignment board S π depth mark M rows (fun i=>(rows i).width)
      (board.original S π depth mark order acquired))
local notation "amount" => fun i : Fin board.rows=>(rows i).width
local notation "after" => fun e (on : 0<amount e) b=>Sum.inl (HistoryRoles.paid S π depth mark uni (receipt.ident ⟨e,on⟩,b))
local notation "output" => CatalogueRows.Alignment.originalPort S π depth mark uni board order acquired rows receipt

theorem paid_code (e : Fin board.rows) (b : Bool) :
    ProtocolRAMTurnStepOrder.liveCode S true amount after e b=
      if on : 0<amount e then code true (output ⟨e,on⟩ b) else 0 := by
  by_cases on:0<amount e
  · simp only [ProtocolRAMTurnStepOrder.liveCode,dite_eq_left on]
    exact printed_physical S π depth mark uni (.inl (receipt.ident ⟨e,on⟩)) true b
  · simp [ProtocolRAMTurnStepOrder.liveCode,on]

theorem paid_vertex (phys : Fin board.rows→Chord (siteLast h (2^W) k+1))
    (pos : ∀u : CatalogueRows.Alignment.Active board rows,phys u.val=sorted S π depth mark (.inl (receipt.ident u)))
    (u : CatalogueRows.Alignment.Active board rows) (b : Bool) :
    name (site S (output u b))=(rowGraph phys).vertex u.val b := by
  change name (site S (physical ((.inl (receipt.ident u)),sides (.inl (receipt.ident u)) b)))=
    (portGraph _).vertex (phys u.val) b
  rw [pos u]
  exact physical_named S π depth mark uni _ b

end Hierarchy.ProtocolRAMPaidTurnPlacement


namespace Hierarchy.ProbeStage.CoreBoard.Report
open Tagged AdaptiveProbe WireTelescope HistoryRoles RoleProgram ProtocolRAM.Calendar CoreRoute
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical
variable {h W k attempts w R M den : ℕ} {π : Equiv.Perm (Row h)} {U : Widths (siteLast h (2^W) k+1)}
    (Z : Report π (2^W) k w R M den U) (depth : ℕ) (mark : ReportSockets.Marks h W k attempts) (uni : ReportSockets.Exclusive mark)
local notation "S" => Z.sampler
local notation "counts" => SettledMatrix.Layout.bits Z.fixed Z.stock Z.reserved Z.used
local notation "num" => SettledMatrix.Layout.numbered (r:=Z.edges) (I:=Goods h W k) (A:=Catalysts h W k)
variable (ident : {i : Fin Z.edges // 0<(Z.rows i).width} ↪ Catalogue Z.sampler π.symm depth mark)
local notation "before" => fun i (_ : 0<counts i)=>publicRoleFor S π.symm (Z.beforePay depth mark uni ident) (num i)
local notation "port" => Terminal.ports S π.symm depth mark uni Z.fixed Z.stock Z.reserved Z.used (Z.fixedOriginal depth mark ident)

include ident in
theorem input_socket_code (i : Fin (Fintype.card (Fin Z.edges⊕(Goods h W k⊕Catalysts h W k)))) (b : Bool) :
    ProtocolRAMTurnStepOrder.liveCode S false counts before i b=
      if on:0<counts i then RoleProgram.labelled S false (port ⟨(i,b),on⟩) else 0 :=
  ProtocolRAMPaidTurnPlacement.original_code S π.symm depth mark uni Z.fixed Z.stock Z.reserved Z.used
    (Z.fixedOriginal depth mark ident) (Z.beforePay depth mark uni ident) (Z.beforePay_live depth mark uni ident) i b

end Hierarchy.ProbeStage.CoreBoard.Report

end
end OAI
