import OAI.Hierarchy.DescentResetOppositePayload
import OAI.Hierarchy.DescentFallbackSignedPeer

namespace OAI
/-! # The source payload selected by a signed incoming old cable grain -/
namespace Hierarchy.DescentResetOppositePayload
open DescentSharedCableNames Stage DescentIssuedFallbackPanel DescentSIMDLookup DescentSixParty
open scoped Classical
noncomputable section
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

/-- At a given real issuing host and block, a cable's first source port and
grain offset identify the exact source occurrence even for parallel cables. -/
theorem sender_slot (e : E) (j : Fin (2*A.cap)) (t : Live A.degree A.cap)
    (stored : panel (pL e).1 j=some t) (sender : t.target=false)
    (wire : t.sourceWire=(cable (pR e).1 (pR e).2).sourceWire)
    (offset : t.within=(cable (pR e).1 (pR e).2).within) : j=(addr (pL e)).2:=by
  let h:=(pL e).1
  have hit : ∃u : A.CellPorts h.1.1 h.1.2 h.2,signed A native S ready h.1 h.2 u=j:=by
    by_contra denied
    rw [signed_empty A native S ready names _ _ (not_exists.mp denied)] at stored
    contradiction
  obtain ⟨u,atU⟩:=hit
  rw [←atU,signed_read] at stored
  have eqn : cable h u=t:=Option.some.inj stored
  let f:=recover A h u
  have mode : (cable h u).target=false:=(congrArg Live.target eqn).trans sender
  have pu : pL f=⟨h,u⟩:=by
    have h':=DescentIssuedFallbackPanel.from_any A native S ready names h u
    dsimp only at h'
    rw [mode] at h'
    exact h'
  have atHome : home A (W.graph.src f.1)=home A (W.graph.src e.1):=congrArg Sigma.fst pu
  have orig : W.graph.src f.1=W.graph.src e.1:=ready.coordinates atHome
  have code : outgoing A native S ready ⟨f.1,Nat.zero_lt_of_lt f.2.isLt⟩=
      outgoing A native S ready ⟨e.1,Nat.zero_lt_of_lt e.2.isLt⟩:=(congrArg Live.sourceWire eqn).trans wire
  have name := outgoing_identify A native S ready ⟨f.1,Nat.zero_lt_of_lt f.2.isLt⟩ ⟨e.1,Nat.zero_lt_of_lt e.2.isLt⟩ orig code
  have same : f=e:=by
    apply Sigma.ext (congrArg Subtype.val name)
    apply (Fin.heq_ext_iff (congrArg A.grainCount (congrArg Subtype.val name))).mpr
    exact congrArg Fin.val ((congrArg Live.within eqn).trans offset)
  have loc:=congrArg addr pu
  rw [same] at loc
  exact atU.symm.trans (congrArg Prod.snd loc).symm

/-- On the stored recipient, selecting the source payload over the physical
old neighbor list yields precisely the payload from that very old grain. -/
theorem paired (e : E) (payload : H→Fin (2*A.cap)→Cell b) :
    let h:=(pR e).1
    let reads:=fun (s : Slot A.degree A.cap)=>(peer h s.1).bind (fun v=>panel v s.2)
    let words:=fun (s : Slot A.degree A.cap)=>(peer h s.1).elim 0 (fun v=>payload v s.2)
    select (panel h (addr (pR e)).2) reads words=payload (pL e).1 (addr (pL e)).2:=by
  intro h reads words
  let q:=cable h (pR e).2
  let source:=(pL e).1
  let slot:=(addr (pL e)).2
  let s : Slot A.degree A.cap:=(q.neighbor,slot)
  have stored : panel h (addr (pR e)).2 = some q :=
    signed_read A native S ready names h (pR e).2
  have route : peer h q.neighbor=some source:=by
    have atR:=signedPeer_actual A native S ready names true e
    change (panel h (addr (pR e)).2).bind _=some source at atR
    rw [stored] at atR
    exact atR
  have got : reads s=some (cable source (pL e).2):=by
    change (peer h q.neighbor).bind _=_
    rw [route]
    exact signed_read A native S ready names _ _
  have found : «matches» q s.1 (reads s):=⟨rfl,_,got,rfl,rfl,rfl⟩
  have unique (u : Slot A.degree A.cap) (ok : «matches» q u.1 (reads u)) : u=s:=by
    obtain ⟨index_,t,origin,flag,first,within⟩:=ok
    apply Prod.ext index_
    change (peer h u.1).bind _ = some t at origin
    rw [index_,route] at origin
    exact sender_slot A native S ready names e u.2 t origin flag first within
  rw [stored,
    selected q reads words rfl s found unique]
  change (peer h q.neighbor).elim _ _=_
  rw [route]
  rfl

end
end Hierarchy.DescentResetOppositePayload

end OAI
