import OAI.Hierarchy.ProtocolRAMPaidTurnPhysicalSite
import OAI.Hierarchy.ProtocolRAMPaidTurnPlacement
import OAI.Hierarchy.ProtocolRAMTurnAuthenticatedChart
import OAI.Hierarchy.TaggedWireOriginalRead

namespace OAI
/-! # The native terminal record's last two words are exactly its purchased physical seat -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAMPaidTurnPlacement
open ProbeStage CoreBoard WordSeats ReportSockets AdaptiveProbe WireTelescope SettledMatrix
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM.Calendar ProtocolRAMTurnOrder ProtocolRAMTurnGeometry ProtocolRAMTurnChart ProtocolRAMTurnShelf
open scoped Classical

variable {h W k attempts edges n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : Marks h W k attempts) (uni : Exclusive mark)
    (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges) (pad : Chord (siteLast h (2^W) k+1))
    (fixed : Fin edges→ℕ) (ident : {i // 0<fixed i} ↪ Catalogue S π depth mark)
local notation "L" => B.matrixLayout (siteNumber h (2^W) k).injective pad
local notation "R" => fixedRoom (k:=k) (attempts:=attempts) S
local notation "Source" => ProtocolRAMTurnGeometry.Source edges h (2^W) k
local notation "oldRole" => fun (i : {i //0<fixed i}) (b : Bool) => Sum.inl (HistoryRoles.paid S π depth mark uni (ident i,b))
local notation "code" => fun (i : {i // 0<fixed i}) (b : Bool) => HistoryRoles.code S (.inl
  (HistoryRoles.paid S π depth mark uni (fixedVisit S π depth mark fixed ident (i,b))))

theorem printed_fixed (e : {i //0<fixed i}) (p : Bool→HistoryRoles.Public S h W k attempts)
    (connected : ∀b,p b=oldRole e b) (b : Bool) : ProtocolRAMTurnOperands.printed S false p b false=2*code e b := by
  let a:=actualEnds S π depth mark (ident e)
  have nameAt (t : Bool) : HistoryRoles.name (HistoryRoles.site S (p t))=HistoryRoles.name (Incident.choose a t) := by
    rw [connected]
    exact congrArg HistoryRoles.name (HistoryRoles.paid_site S π depth mark uni (ident e) t)
  change 2*HistoryRoles.code S (p (if HistoryRoles.name (HistoryRoles.site S (p false)) <
      HistoryRoles.name (HistoryRoles.site S (p true)) then b else !b)) =
    2*HistoryRoles.code S (.inl (HistoryRoles.paid S π depth mark uni
      (ident e,if HistoryRoles.name a.1 < HistoryRoles.name a.2 then b else !b)))
  rw [nameAt false,nameAt true,connected]
  rfl

variable (aligned : ∀e : {i //0<fixed i},filledChord B.actual pad e.val=HistoryRoles.sorted S π depth mark (.inl (ident e)))
local notation "siteAt" => ProtocolRAMTurnEdges.visit B (siteNumber h (2^W) k).injective pad

variable (words : Words)
local notation "item" => fun (s : Source)=>(ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k s).val
variable (fixedWords : ∀e : {i //0<fixed i},∀b : Bool,
    (if b then words.targetRole else words.sourceRole)
      (ProtocolRAMTurnGeometry.sourceOrder edges h (2^W) k (.inl e.val)).val =
        2*HistoryRoles.code S (.inl (HistoryRoles.paid S π depth mark uni
          (fixedVisit S π depth mark fixed ident (e,b)))))

/-- Authentication of each positive fixed original. The memory may contain
arbitrary words in rows whose old paid width is zero. -/
theorem captured_fixed {native : ℕ} (book : HistoryRoles.RoleProgram.Board) (site half : ProtocolRAM.Bank)
    {old : Fin book.old→ℕ} {new : Fin book.edges→ℕ}
    {original : ∀r,0<old r→Bool→HistoryRoles.Public S h W k attempts}
    {ending : ∀r,0<new r→Bool→HistoryRoles.Public S h W k attempts}
    {m : Memory native}
    (live : book.LiveReads S old new original ending m) (fits : 2*R≤2^native)
    (idx : {i //0<fixed i}→Fin book.old) (address : ∀i,(idx i).val=item (.inl i.val))
    (used : ∀i,0<old (idx i)) (auth : ∀i b,original (idx i) (used i) b=oldRole i b)
    (i : {e //0<fixed e}) (b : Bool) :
    let v:=ProtocolRAMTurnChart.captured (ProtocolRAMTurnSnapshot.chartData book site half) m
    (if b then v.targetRole else v.sourceRole) (item (.inl i.val))=2*code i b := by
  let v:=ProtocolRAMTurnChart.captured (ProtocolRAMTurnSnapshot.chartData book site half) m
  change (if b then v.targetRole else v.sourceRole) _=_
  rw [←address i]
  exact (ProtocolRAMTurnSnapshot.original_code S book live site half (idx i) (used i) b fits).trans
    (printed_fixed S π depth mark uni fixed ident i _ (auth i) b)

theorem printed_swap (p : Bool→HistoryRoles.Public S h W k attempts) (side : Bool)
    (sep : HistoryRoles.name (HistoryRoles.site S (p false))≠HistoryRoles.name (HistoryRoles.site S (p true))) :
    ProtocolRAMTurnOperands.printed S false (fun b=>p (!b)) side false=
      ProtocolRAMTurnOperands.printed S false p side false := by
  by_cases order:HistoryRoles.name (HistoryRoles.site S (p false))<HistoryRoles.name (HistoryRoles.site S (p true))
  · cases side <;> simp [ProtocolRAMTurnOperands.printed,order,not_lt_of_ge order.le]
  · have back:=lt_of_le_of_ne (le_of_not_gt order) sep.symm
    cases side <;> simp [ProtocolRAMTurnOperands.printed,order,back]

theorem paid_original_order (pay : Fin edges→Bool→HistoryRoles.Public S h W k attempts)
    (e : {i //0<fixed i}) (assigned : ∀b,pay e.val b=oldRole e b) :
    ∃flip : Bool,∀b,HistoryRoles.RoleProgram.publicRoleFor S π pay (.inl e.val) b=oldRole e (if flip then !b else b) := by
  by_cases lo:HistoryRoles.name (HistoryRoles.site S (pay e.val false))<HistoryRoles.name (HistoryRoles.site S (pay e.val true))
  · exact ⟨false,fun b=>by simpa only [HistoryRoles.RoleProgram.publicRoleFor,ite_eq_left lo,Bool.false_eq_true,ite_false] using assigned b⟩
  · exact ⟨true,fun b=>by simpa only [HistoryRoles.RoleProgram.publicRoleFor,ite_eq_right lo,ite_true] using assigned (!b)⟩

/-- The stored original may already have been normalized by publicRoleFor.
Either uniform endpoint order prints the identical physical role. -/
theorem captured_fixed_ordered {native : ℕ} (book : HistoryRoles.RoleProgram.Board) (site half : ProtocolRAM.Bank)
    {old : Fin book.old→ℕ} {new : Fin book.edges→ℕ}
    {original : ∀r,0<old r→Bool→HistoryRoles.Public S h W k attempts}
    {ending : ∀r,0<new r→Bool→HistoryRoles.Public S h W k attempts}
    {m : Memory native} (live : book.LiveReads S old new original ending m) (fits : 2*R≤2^native)
    (idx : {i //0<fixed i}→Fin book.old) (address : ∀i,(idx i).val=item (.inl i.val))
    (used : ∀i,0<old (idx i)) (auth : ∀i,∃flip : Bool,∀b,original (idx i) (used i) b=oldRole i (if flip then !b else b))
    (i : {e //0<fixed e}) (b : Bool) :
    let v:=ProtocolRAMTurnChart.captured (ProtocolRAMTurnSnapshot.chartData book site half) m
    (if b then v.targetRole else v.sourceRole) (item (.inl i.val))=2*code i b := by
  let v:=ProtocolRAMTurnChart.captured (ProtocolRAMTurnSnapshot.chartData book site half) m
  change (if b then v.targetRole else v.sourceRole) _=_
  rw [←address i]
  refine (ProtocolRAMTurnSnapshot.original_code S book live site half (idx i) (used i) b fits).trans ?_
  obtain ⟨fl,orient⟩:=auth i
  let raw:Bool→HistoryRoles.Public S h W k attempts:=oldRole i
  have law:=printed_fixed S π depth mark uni fixed ident i raw (fun _=>rfl) b
  cases fl
  · have ep : original (idx i) (used i)=raw:=funext (fun c=>orient c)
    rw [ep];exact law
  · have ep : original (idx i) (used i)=fun t=>raw (!t):=funext (fun c=>orient c)
    have atSide (t : Bool) : HistoryRoles.site S (raw t)=Incident.choose (actualEnds S π depth mark (ident i)) t :=
      HistoryRoles.paid_site S π depth mark uni (ident i) t
    have ne : HistoryRoles.name (HistoryRoles.site S (raw false))≠HistoryRoles.name (HistoryRoles.site S (raw true)) := by
      rw [atSide,atSide]
      exact fun eq=>actual_distinct S π depth mark (ident i) ((siteNumber h (2^W) k).injective eq)
    rw [ep,printed_swap S raw b ne]
    exact law

include fixedWords in
theorem forward_seat (z : RawBoundary (h:=h) (W:=W) (k:=k) (edges:=edges)) (keep : ProtocolRAMLiveTurnOrder.retain fixed z.1) :
    (localSeat S π depth mark uni B pad fixed ident (rawLive S π B pad fixed z keep)).val=
      if ProtocolRAMTurnGeometry.fixed z.1 then
        (if z.2.val=0 then words.sourceRole (item z.1) else words.targetRole (item z.1))/2
      else ProtocolRAMTurnGeometry.label R z.1 z.2.val := by
  rcases z with ⟨(e|i|c),j⟩
  · let v : {i // 0<fixed i}:=⟨e,keep⟩
    have atSide (side : Bool) : (localSeat S π depth mark uni B pad fixed ident (.inl (v,side))).val =
        (if side then words.targetRole else words.sourceRole) (item (.inl e))/2 := by
      rw [fixed_code,fixedWords v side]
      omega
    change Fin 2 at j
    fin_cases j
    · exact atSide false
    · exact atSide true
  · rcases i with p|⟨⟨p,t⟩,a⟩
    · exact payload_code S π depth mark uni B pad fixed ident p _
    · rw [show (localSeat S π depth mark uni B pad fixed ident (rawLive S π B pad fixed _ keep)).val=_
        from alt_code S π depth mark uni B pad fixed ident p t a _,raw_phase]
      rfl
  · rw [show (localSeat S π depth mark uni B pad fixed ident (rawLive S π B pad fixed _ keep)).val=_
      from reserve_code S π depth mark uni B pad fixed ident c _,raw_phase]
    rfl

variable (order : Fin n≃ProtocolRAMTurnGeometry.Source edges h (2^W) k)
local notation "len" => ProtocolRAMTurnGeometry.length ∘ order
local notation "visit" => ProtocolRAMVisitAdjacency.vertex len (fun a=>siteAt (order a))
variable (col : Fin (turns (ProtocolRAMTurnGeometry.length ∘ order))→Fin 7→ℕ)
    (kept : ∀u : Live col,ProtocolRAMLiveTurnOrder.retain fixed (rawItem order u.val).1)

include aligned fixedWords in
theorem loc (o : CoreRoute.Orders h (2^W) k) (u : Live col) :
    let r:=record (header o R order) words visit u.val
    let seat:=chartPut S π depth mark uni B pad fixed ident order col kept u
    seat.1.val=r.site ∧ seat.2.val=r.seat := by
  exact ⟨forward_site S π depth mark B pad fixed ident aligned (rawItem order u.val) (kept u),
    forward_seat S π depth mark uni B pad fixed ident words fixedWords (rawItem order u.val) (kept u)⟩

/-- Positivity of the terminal column pays every retained identity at its
true width. Non-fixed rows use their own distinct public allocations. -/
theorem record_keep (o : CoreRoute.Orders h (2^W) k) (v : ProtocolRAMTurnItinerary.Values)
    (widthAt : ∀e : Fin edges,words.width (item (.inl e))=fixed e) :
    ∀u : Live (fun r=>(record (header o R order) words visit r).field v),
      ProtocolRAMLiveTurnOrder.retain fixed (rawItem order u.val).1 := by
  intro u
  let src:=(rawItem order u.val).1
  have paid : words.width (item src)≠0 := by
    intro zero
    apply u.property
    change (if _ then 0 else words.width (item src))=0
    simp [zero]
  change ProtocolRAMLiveTurnOrder.retain fixed src
  cases atSrc:src with
  | inl e=>rw [atSrc,widthAt] at paid;exact Nat.pos_of_ne_zero paid
  | inr z=>trivial

end Hierarchy.ProtocolRAMPaidTurnPlacement

end
end OAI
