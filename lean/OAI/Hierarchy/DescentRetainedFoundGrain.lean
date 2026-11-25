import OAI.Hierarchy.DescentOperandStemSource
import OAI.Hierarchy.DescentResetRetainedCableValue

namespace OAI
/-! # Identifying the signed grain chosen by a retained operand, including old loops -/
namespace Hierarchy.DescentOperandPriorIncidence
open DescentSixParty DescentColonies DescentSharedCableNames DescentTerminalPointerDigits
open DescentTerminalSignedGrainWord DescentStageEdgeReceipt DescentOperandSignedSearch
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentGroupPeerOrder
open DescentKernelHistory DescentOperandStateBanks DescentIssuedFallbackPanel
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {T : PoweredGadget F} {q ε : ℝ}
  (A : GroupStage W T q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
  (ready : A.StateBounds S i) (names : Stage.Host J V k↪ℕ) (v : W.graph.Site)
local notation "h" => Stage.home A v
local notation "ports" => A.CellPorts (h).1.1 (h).1.2 (h).2
local notation "panel" => Stage.signedPanel A native S ready names h
local notation "addr" => Stage.signed A native S ready (h).1 (h).2
local notation "tokenAt" => token A native S ready names v
local notation "coord" => fun u:W.graph.Site=>(A.pos u,A.block u)

def originFace (e : Incident W.graph v) : Bool:=decide (W.graph.src e.val≠v)

def originPort (e : Incident W.graph v) (j : Fin (A.grainCount e.val)) : ports :=
  if left : W.graph.src e.val=v then
    .inl ⟨⟨e.val,congrArg A.pos left,congrArg A.block left⟩,j⟩
  else
    let right:=e.property.resolve_left left
    .inr ⟨⟨e.val,congrArg A.pos right,congrArg A.block right⟩,j⟩

theorem origin_port (e : Incident W.graph v) (j : Fin (A.grainCount e.val)) :
    Stage.recover A h (originPort A v e j)=(⟨e.val,j⟩ : Stage.Grain A) ∧
      Stage.signedBit A h (originPort A v e j)=(if originFace v e then 1 else 0):=by
  by_cases hs:W.graph.src e.val=v <;> simp [originPort,originFace,hs,Stage.recover,Stage.signedBit]

/-- On an authentic prior signed panel, the queried token and the sign identify
the original physical grain. Both ends of an old loop still have distinct signs. -/
theorem real_hit (coords : Function.Injective coord) (e : Incident W.graph v) (j : Fin (A.grainCount e.val))
    (wanted : Fin (A.degree*A.cap*A.cap)) (key : point A.degree A.cap (Packed.token (some wanted))=some (tokenAt ⟨e,j⟩))
    (f : Fin 2) (s : Fin (2*A.cap)) :
    hit A.degree A.cap f s (Packed.token (some wanted)) (DescentSignedCableCodec.encode (panel s)) ↔
      ∃p : ports,addr p=s ∧ Stage.signedBit A h p=f ∧ Stage.recover A h p=(⟨e.val,j⟩ : Stage.Grain A):=by
  change (_ ∧ sign A.cap s=f ∧ project A.degree A.cap _=Packed.token (some wanted)) ↔ _
  rw [DescentOperandPriorTicket.signal,point_project,key]
  constructor
  · rintro ⟨_,side,data⟩
    by_cases live : ∃p:ports,addr p=s
    · obtain ⟨p,rfl⟩:=live
      rw [Stage.signed_read,Option.map_some,Option.some.injEq] at data
      refine ⟨p,rfl,(sign_real A native S ready v p).symm.trans side,?_⟩
      cases p with
      | inl l =>
        rcases l with ⟨⟨e',atPos,atBlock⟩,idx⟩
        let src : Incident W.graph v:=⟨e',Or.inl (coords (Prod.ext atPos atBlock))⟩
        have uniq:=(tokenAt).injective ((grain_read A native S ready names v _ src idx rfl).symm.trans data)
        exact congrArg (fun t:SiteGrains A v=>(⟨t.1.val,t.2⟩:Stage.Grain A)) uniq
      | inr l =>
        rcases l with ⟨⟨e',atPos,atBlock⟩,idx⟩
        let dst : Incident W.graph v:=⟨e',Or.inr (coords (Prod.ext atPos atBlock))⟩
        have uniq:=(tokenAt).injective ((grain_read A native S ready names v _ dst idx rfl).symm.trans data)
        exact congrArg (fun t:SiteGrains A v=>(⟨t.1.val,t.2⟩:Stage.Grain A)) uniq
    · rw [Stage.signed_empty A native S ready names h s (not_exists.mp live)] at data
      contradiction
  · rintro ⟨p,rfl,side,recovered⟩
    refine ⟨Nat.succ_ne_zero _,(sign_real A native S ready v p).trans side,?_⟩
    rw [Stage.signed_read,Option.map_some,Option.some.injEq]
    exact grain_read A native S ready names v p e j recovered

/-- The chosen query slot is the same signed old port used by the reset
stem and by the remote incoming-ticket panel. -/
theorem origin_address (e : Incident W.graph v) (j : Fin (A.grainCount e.val)) :
    address A native S ready (port A (originFace v e) (⟨e.val,j⟩ : Stage.Grain A))=(h,addr (originPort A v e j)):=by
  rcases e with ⟨edge,incident⟩
  by_cases atSrc:W.graph.src edge=v
  · have face : originFace v ⟨edge,incident⟩ = false := by simp [originFace,atSrc]
    rw [face]
    subst v
    simp only [DescentIssuedFallbackPanel.address,DescentIssuedFallbackPanel.port,originPort,dite_true]
    rfl
  · have face : originFace v ⟨edge,incident⟩ = true := by simp [originFace,atSrc]
    rw [face]
    have atDst:=incident.resolve_left atSrc
    subst v
    simp only [DescentIssuedFallbackPanel.address,DescentIssuedFallbackPanel.port,originPort,dite_eq_right atSrc]
    rfl

theorem origin_local_address {m c : ℕ} (digits : Block m≃J×Block k) (basis : DescentGL.Layout m)
    (e : Incident W.graph v) (j : Fin (A.grainCount e.val)) :
    localAddress (c:=c) A native S ready digits basis (originFace v e) (⟨e.val,j⟩ : Stage.Grain A)=
      (subcell (c:=c) digits basis h,addr (originPort A v e j)):=by
  unfold localAddress
  rw [origin_address A native S ready v e j]

private theorem outgoing_impossible (coords : Function.Injective coord) (e : Incident W.graph v)
    (j : Fin (A.grainCount e.val)) (p : ports) (hs : originFace v e=true)
    (side : Stage.signedBit A h p=0) (same : Stage.recover A h p=(⟨e.val,j⟩ : Stage.Grain A)) : False:=by
  have remote : W.graph.src e.val≠v:=by simpa [originFace] using hs
  cases p with
  | inl l =>
    rcases l with ⟨⟨f,ep,eb⟩,idx⟩
    have edge : f=e.val:=congrArg Sigma.fst same
    exact remote ((congrArg W.graph.src edge).symm.trans (coords (Prod.ext ep eb)))
  | inr l => exact (by decide : (1:Fin 2)≠0) side

/-- The register is evaluated with the source-first ordering of a retained node.
The resulting physical slot is the actual earlier signed incidence of that grain. -/
theorem found_origin (C : DescentResetRetainedCableLaw.Shape)
    (degree : C.degree=A.degree) (capacity : C.cap=A.cap) (x : C.Input) (z : C.Donor)
    (coords : Function.Injective coord) (e : Incident W.graph v) (j : Fin (A.grainCount e.val))
    (peer first chunk : ℕ) (read : ∀f,(C.header x f).val=(Pointer.cable peer first chunk).header f)
    (donor : (C.donorCell x).val=z.val+1) (rows : ∀s,HEq (C.row x z s)
      (DescentSignedCableCodec.encode (panel (s.cast (congrArg (2*·) capacity)))))
    (peerFit : peer<A.degree) (firstFit : first<A.cap) (within : chunk/C.units=j.val)
    (label : peer*A.cap+first=(DescentTerminalPortChart.label A native S ready names v e (Nat.zero_lt_of_lt j.isLt)).val) :
    C.found x=some (z,originFace v e,(addr (originPort A v e j)).cast (congrArg (2*·) capacity.symm)):=by
  obtain ⟨D₀,c₀,Z,u,b,zBits,lanes⟩:=C
  change D₀=A.degree at degree
  change c₀=A.cap at capacity
  subst D₀;subst c₀
  let C : DescentResetRetainedCableLaw.Shape:=⟨A.degree,A.cap,Z,u,b,zBits,lanes⟩
  have rr (s):C.row x z s=DescentSignedCableCodec.encode (panel s):=eq_of_heq (rows s)
  have below:chunk/u<A.cap:=by rw [within];exact j.isLt.trans_le (Stage.grain_room A native S ready e.val)
  let wanted:=finProdFinEquiv (finProdFinEquiv ((⟨peer,peerFit⟩:Fin A.degree),(⟨first,firstFit⟩:Fin A.cap)),
    (⟨chunk/u,below⟩:Fin A.cap))
  have q₀:DescentOperandPriorTicket.key A.degree A.cap u (C.header x)=Packed.token (some wanted):=
    DescentOperandPriorTicket.cable _ _ _ _ _ _ _ read peerFit firstFit below
  have match_:point A.degree A.cap (Packed.token (some wanted))=some (tokenAt ⟨e,j⟩):=by
    simp only [wanted,point,Packed.token_back,Option.map_some,Equiv.symm_apply_apply,Option.some.injEq,
      token,finProdFinEquiv_apply_val]
    apply Prod.ext _ within
    change _ = (DescentTerminalPortChart.label A native S ready names v e (Nat.zero_lt_of_lt j.isLt)).val
    simpa only [Nat.add_comm,Nat.mul_comm] using label
  have port:=origin_port A v e j
  apply C.found_from_slots x z (originFace v e) (addr (originPort A v e j)) (read 0) donor
  · intro s
    rw [rr,q₀,real_hit A native S ready names v coords e j wanted match_]
    constructor
    · rintro ⟨p,rfl,face,same⟩
      exact congrArg addr (port_unique A v p _ (same.trans port.1.symm) (face.trans port.2.symm))
    · rintro rfl
      exact ⟨_,rfl,port.2,port.1⟩
  · intro isTarget s
    rw [rr,q₀,real_hit A native S ready names v coords e j wanted match_]
    rintro ⟨p,_,face,same⟩
    exact outgoing_impossible A v coords e j p isTarget face same

end
end Hierarchy.DescentOperandPriorIncidence

end OAI
