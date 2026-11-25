import OAI.Hierarchy.DescentResetOppositeGrain
import OAI.Hierarchy.DescentResetReciprocalPeer

namespace OAI
/-! # Returning a signed target's payload to the true original source -/
namespace Hierarchy.DescentResetOppositePayload
open DescentSharedCableNames Stage DescentIssuedFallbackPanel DescentSIMDLookup DescentSixParty
open scoped Classical
noncomputable section

/-- At the remote host, the signed target must point back to this receiver.
This separates parallel incoming fibers from different original sources. -/
def accepts {D cap : ℕ} (guard : Fin D→Fin D→Bool) (wanted : Live D cap) (remote : Fin D) (chip : Option (Live D cap)) : Prop :=
  remote=wanted.neighbor ∧ ∃x,chip=some x ∧ x.target=true ∧ guard remote x.neighbor=true ∧ x.sourceWire=wanted.sourceWire ∧ x.within=wanted.within

def reverse {D cap b : ℕ} (guard : Fin D→Fin D→Bool) (query : Option (Live D cap))
    (send : Slot D cap→Option (Live D cap)) (data : Slot D cap→Cell b) : Cell b :=
  match query with
  | none=>0
  | some q=>if q.target then 0 else if has : ∃s : Slot D cap,accepts guard q s.1 (send s) then data has.choose else 0

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k i b : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
  (names : Host J V k↪ℕ)
local notation "H" => Host J V k
local notation "E" => Grain A
local notation "panel" => signedPanel A native S ready names
local notation "pL" => port A false
local notation "pR" => port A true
local notation "cable" => live A native S ready names
local notation "addr" => address A native S ready
local notation "peer" => physicalPeer A names

private theorem cross (side : Bool) (e : E) :
    let u:=port A side e
    peer u.1 (cable u.1 u.2).neighbor=some ((port A (!side) e).1):=by
  have read:=signedPeer_actual A native S ready names side e
  dsimp only at read
  unfold signedPeer at read
  rw [signed_read] at read
  cases side <;> exact read

theorem target_slot (e : E) (j : Fin (2*A.cap)) (t : Live A.degree A.cap)
    (stored : panel (pR e).1 j=some t) (orientation : t.target=true)
    (back : peer (pR e).1 t.neighbor=some (pL e).1)
    (wire : t.sourceWire=(cable (pL e).1 (pL e).2).sourceWire)
    (offset : t.within=(cable (pL e).1 (pL e).2).within) : j=(addr (pR e)).2:=by
  let h:=(pR e).1
  have hit : ∃u : A.CellPorts h.1.1 h.1.2 h.2,signed A native S ready h.1 h.2 u=j:=by
    by_contra denied
    rw [signed_empty A native S ready names _ _ (not_exists.mp denied)] at stored
    contradiction
  obtain ⟨u,atU⟩:=hit
  rw [←atU,signed_read] at stored
  have eqn : cable h u=t:=Option.some.inj stored
  let f:=recover A h u
  have mode : (cable h u).target=true:=(congrArg Live.target eqn).trans orientation
  have pu : pR f=⟨h,u⟩:=by
    have h':=DescentIssuedFallbackPanel.from_any A native S ready names h u
    dsimp only at h'
    rw [mode] at h'
    exact h'
  have ret:=cross A native S ready names true f
  change peer (pR f).1 (cable (pR f).1 (pR f).2).neighbor=some (pL f).1 at ret
  rw [pu] at ret
  change peer h (cable h u).neighbor = some (pL f).1 at ret
  rw [eqn] at ret
  have orig : W.graph.src f.1=W.graph.src e.1:=ready.coordinates (Option.some.inj (ret.symm.trans back))
  have code : outgoing A native S ready ⟨f.1,Nat.zero_lt_of_lt f.2.isLt⟩=
      outgoing A native S ready ⟨e.1,Nat.zero_lt_of_lt e.2.isLt⟩:=(congrArg Live.sourceWire eqn).trans wire
  have name:=outgoing_identify A native S ready ⟨f.1,Nat.zero_lt_of_lt f.2.isLt⟩ ⟨e.1,Nat.zero_lt_of_lt e.2.isLt⟩ orig code
  have same : f=e:=by
    apply Sigma.ext (congrArg Subtype.val name)
    apply (Fin.heq_ext_iff (congrArg A.grainCount (congrArg Subtype.val name))).mpr
    exact congrArg Fin.val ((congrArg Live.within eqn).trans offset)
  have location:=congrArg addr pu
  rw [same] at location
  exact atU.symm.trans (congrArg Prod.snd location).symm

def guardAt (h : H) (v t : Fin A.degree) : Bool:=decide ((peer h v).bind (fun x=>peer x t)=some h)

theorem returned (e : E) (payload : H→Fin (2*A.cap)→Cell b) :
    let h:=(pL e).1
    let reads:=fun (s : Slot A.degree A.cap)=>(peer h s.1).bind (fun v=>panel v s.2)
    let words:=fun (s : Slot A.degree A.cap)=>(peer h s.1).elim 0 (fun v=>payload v s.2)
    reverse (guardAt A names h) (panel h (addr (pL e)).2) reads words=payload (pR e).1 (addr (pR e)).2:=by
  intro h reads words
  let q:=cable h (pL e).2
  let other:=(pR e).1
  let t:=cable other (pR e).2
  let slot:=(addr (pR e)).2
  let s : Slot A.degree A.cap:=(q.neighbor,slot)
  have outward : peer h q.neighbor=some other:=cross A native S ready names false e
  have inward : peer other t.neighbor=some h:=cross A native S ready names true e
  have got : reads s=some t:=by
    change (peer h q.neighbor).bind _=_
    rw [outward];exact signed_read A native S ready names _ _
  have gate : guardAt A names h q.neighbor t.neighbor=true:=by simp [guardAt,outward,inward]
  have has : ∃u : Slot A.degree A.cap,accepts (guardAt A names h) q u.1 (reads u):=⟨s,rfl,t,got,rfl,gate,rfl,rfl⟩
  have only (u : Slot A.degree A.cap) (ok : accepts (guardAt A names h) q u.1 (reads u)) : u=s:=by
    obtain ⟨index_,b,origin,side,check,first,within⟩:=ok
    apply Prod.ext index_
    change (peer h u.1).bind _ = some b at origin
    rw [index_,outward] at origin
    have way : peer other b.neighbor=some h:=by simpa only [guardAt,index_,outward,Option.bind_some,decide_eq_true_eq] using check
    exact target_slot A native S ready names e u.2 b origin side way first within
  rw [show panel h (addr (pL e)).2=some q from signed_read A native S ready names _ _]
  simp only [reverse, show q.target = false from rfl, Bool.false_eq_true, ite_false,
    dite_eq_left has, only _ has.choose_spec]
  change (peer h q.neighbor).elim _ _=_
  rw [outward]
  rfl

end
end Hierarchy.DescentResetOppositePayload

end OAI
