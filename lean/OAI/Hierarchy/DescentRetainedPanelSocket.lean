import OAI.Hierarchy.DescentRetainedOriginFacts
import OAI.Hierarchy.DescentTerminalGrainPrefix

namespace OAI
/-! # Source-preferred original incidence in the signed bytes of a retained panel -/
namespace Hierarchy.DescentOperandPriorIncidence
open DescentSixParty DescentSharedCableNames DescentTerminalPointerDigits
open DescentTerminalSignedGrainWord DescentKernelHistory
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}
    (A : GroupStage W G q ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (names : Stage.Host J V k↪ℕ)
    (v : W.graph.Site) (coords : Function.Injective (fun s=>(A.pos s,A.block s)))
local notation "here" => Stage.home A v
local notation "code" => Stage.signed A native S ready here.1 here.2
local notation "ports" => A.CellPorts here.1.1 here.1.2 here.2
local notation "bank" => Stage.signedPanel A native S ready names here
local notation "row" => fun s : Fin (2*A.cap)=>(bank s).map grain
local notation "tokenAt" => DescentTerminalPointerDigits.token A native S ready names v
local notation "recover" => Stage.recover A here

include coords in
private theorem retained_port_at (s : Fin (2*A.cap)) (e : Incident W.graph v) (j : Fin (A.grainCount e.val))
    (hit : (row) s=some (tokenAt ⟨e,j⟩)) : ∃u : ports,code u=s ∧ recover u=⟨e.val,j⟩ :=by
  by_cases found : ∃u : ports,code u=s
  · obtain ⟨u,rfl⟩:=found
    dsimp only at hit
    rw [Stage.signed_read,Option.map_some,Option.some.injEq] at hit
    refine ⟨u,rfl,?_⟩
    cases u with
    | inl l =>
      rcases l with ⟨⟨e',ep,eb⟩,n⟩
      let wire : Incident W.graph v:=⟨e',Or.inl (coords (Prod.ext ep eb))⟩
      have eqn:=(tokenAt).injective ((grain_read A native S ready names v _ wire n rfl).symm.trans hit)
      exact congrArg (fun x : SiteGrains A v=>(⟨x.1.val,x.2⟩:Stage.Grain A)) eqn
    | inr l =>
      rcases l with ⟨⟨e',ep,eb⟩,n⟩
      let wire : Incident W.graph v:=⟨e',Or.inr (coords (Prod.ext ep eb))⟩
      have eqn:=(tokenAt).injective ((grain_read A native S ready names v _ wire n rfl).symm.trans hit)
      exact congrArg (fun x : SiteGrains A v=>(⟨x.1.val,x.2⟩:Stage.Grain A)) eqn
  · dsimp only at hit
    rw [Stage.signed_empty _ _ _ _ _ _ _ (not_exists.mp found)] at hit
    contradiction

include coords in
theorem retained_first_origin (e : Incident W.graph v) (pos : 0<A.grainCount e.val) :
    let u:=DescentTerminalPortChart.first A v e pos
    origin (D:=A.degree) (cap:=A.cap) (fun s=>DescentSignedCableCodec.encode (bank s)) (tokenAt ⟨e,⟨0,pos⟩⟩)=
      some (Stage.live A native S ready names here u) :=by
  intro u
  let t:=tokenAt ⟨e,⟨0,pos⟩⟩
  have member : recover u=⟨e.val,⟨0,pos⟩⟩:=by
    dsimp only [u,DescentTerminalPortChart.first];split <;> rfl
  have exactWing : seek (row) (Stage.signedBit A here u) t=some (code u):=by
    apply seek_exact
    intro s
    constructor
    · rintro ⟨side,hit⟩
      obtain ⟨b,rfl,got⟩:=retained_port_at A native S ready names v coords _ e ⟨0,pos⟩ hit
      rw [sign_real] at side
      exact congrArg (code) (port_unique A v b u (got.trans member.symm) side)
    · rintro rfl
      refine ⟨sign_real A native S ready v u,?_⟩
      rw [Stage.signed_read,Option.map_some]
      exact congrArg some (grain_read A native S ready names v u e ⟨0,pos⟩ member)
  have selected : originIndex (row) t=some (code u):=by
    by_cases atSrc : W.graph.src e.val=v
    · have zero : Stage.signedBit A here u=0:=by
        simp [u,DescentTerminalPortChart.first,atSrc,Stage.signedBit]
      rw [zero] at exactWing
      simp only [originIndex,exactWing]
    · have one : Stage.signedBit A here u=1:=by
        simp [u,DescentTerminalPortChart.first,atSrc,Stage.signedBit]
      rw [one] at exactWing
      cases zero : seek (row) 0 t with
      | none=>simpa only [originIndex,zero] using exactWing
      | some s=>
        have picked := List.find?_some
          (p:=fun j : Fin (2*A.cap) => decide (sign A.cap j=0 ∧ (row) j=some t))
          (l:=List.finRange (2*A.cap)) (a:=s) zero
        have hit : sign A.cap s=0 ∧ (row) s=some t := of_decide_eq_true picked
        obtain ⟨b,slot,got⟩:=retained_port_at A native S ready names v coords s e ⟨0,pos⟩ hit.2
        have face : Stage.signedBit A here b=0:=(sign_real A native S ready v b).symm.trans
          ((congrArg (sign A.cap) slot).trans hit.1)
        rcases b with ⟨⟨original,ep,eb⟩,n⟩|target
        · have atSite : W.graph.src original=v:=coords (Prod.ext ep eb)
          have same : original=e.val:=congrArg Sigma.fst got
          exact False.elim (atSrc (same ▸ atSite))
        · exact False.elim (by simp [Stage.signedBit] at face)
  unfold origin
  simp only [point_project,DescentSignedCableCodec.decode_encode]
  change (originIndex (row) t).bind (fun s=>bank s)=_
  rw [selected,Option.bind_some,Stage.signed_read]

end
end Hierarchy.DescentOperandPriorIncidence

end OAI
