import OAI.Hierarchy.DescentHostRosterOrder
import OAI.Hierarchy.DescentPackedMatchStageCounts
import OAI.Hierarchy.DescentPackedMatchedGather

namespace OAI
/-! # A single hardware peer roster for all group lanes -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w D : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (groups : J↪Fin G) (hosts : V↪Fin H)
local notation "physical" => spread groups hosts (terrain (short:=short) A native S ready names win next)

omit [DecidableEq V] in
private theorem host_hit (near : V→Fin D→Option V) (v : V) (j : Fin D) :
    hostRotor hosts near (hosts v) j=(near v j).map hosts := by
  have hit : ∃y,hosts y=hosts v := ⟨v,rfl⟩
  rw [hostRotor,dite_eq_left hit,hosts.injective hit.choose_spec]

private theorem panel_eq {r D p d : ℕ} {x y : Panel r D p d} (h₁ : x.winner=y.winner) (h₂ : x.neighbor=y.neighbor)
    (h₃ : x.peerWinner=y.peerWinner) : x=y := by
  cases x
  cases y
  cases h₁
  cases h₂
  cases h₃
  rfl

omit [DecidableEq V] [DecidableEq J] in
private theorem spread_from_peers {r p d D : ℕ} (panels : J × V → Panel r D p d)
    (nextOf : J × V → Fin D → Option (J × V)) (near : V → Fin D → Option V)
    (grouped : ∀ g v j, nextOf (g,v) j = (near v j).map (fun t => (g,t)))
    (peer : ∀ z j x, (panels z).peerWinner j x =
      (nextOf z j).elim 0 (fun t => (panels t).winner x)) :
    let landscape := spread groups hosts panels
    Gather.fromPeers (fun h g => (landscape h g).winner) (fun h g => (landscape h g).neighbor)
      (hostRotor hosts near) = landscape := by
  let data := spread groups hosts panels
  have hit (z : J × V) : data (hosts z.2) (groups z.1) = panels z := spread_hit groups hosts panels z
  have miss (h : Fin H) (g : Fin G) (absent : ¬ ∃ z : J × V, groups z.1 = g ∧ hosts z.2 = h) :
      data h g = blank r D p d := by
    unfold data spread
    rw [dite_eq_right absent]
  funext h g
  refine panel_eq ?_ ?_ ?_
  · rfl
  · rfl
  funext j x
  change (hostRotor hosts near h j).elim 0 (fun t => (data t g).winner x) = (data h g).peerWinner j x
  by_cases found : ∃ v, hosts v = h
  · obtain ⟨v,rfl⟩ := found
    rw [host_hit hosts near]
    by_cases present : ∃ u, groups u = g
    · obtain ⟨u,rfl⟩ := present
      rw [hit (u,v), peer (u,v) j x, grouped u v j]
      cases res : near v j with
      | none => rfl
      | some t =>
        change (data (hosts t) (groups u)).winner x = (panels (u,t)).winner x
        exact congrArg (fun u' : Panel r D p d => u'.winner x) (hit (u,t))
    · have vacant (t : Fin H) : data t g = blank r D p d := miss t g (by
        rintro ⟨z,cg,_⟩
        exact present ⟨z.1,cg⟩)
      rw [vacant (hosts v)]
      cases res : near v j with
      | none => rfl
      | some t =>
        change (data (hosts t) g).winner x = 0
        exact congrArg (fun u' : Panel r D p d => u'.winner x) (vacant (hosts t))
  · have vacant := miss h g (by rintro ⟨z,_,hv⟩; exact found ⟨z.2,hv⟩)
    simp only [hostRotor, dite_eq_right found, Option.elim_none, vacant, blank]

theorem terrain_eq (near : V→Fin A.degree→Option V)
    (grouped : ∀g v j,next (g,v) j=(near v j).map (fun z=>(g,z))) :
    Gather.fromPeers (fun h g=>(physical h g).winner) (fun h g=>(physical h g).neighbor) (hostRotor hosts near)=physical := by
  exact spread_from_peers groups hosts (terrain (short:=short) A native S ready names win next)
    next near grouped (fun _ _ _ => rfl)

theorem gathered_fields (near : V→Fin A.degree→Option V)
    (grouped : ∀g v j,next (g,v) j=(near v j).map (fun z=>(g,z)))
    (winner : Fin (2^k)→Bank) (marked : Fin (2^k)→Fin (2*A.cap)→Bank) (P : DescentPackedColony.Ports A.degree)
    (base : ℕ) (m : Memory w) (mounted : DescentPackedColony.Mounted P (hostRotor hosts near) m G M)
    (access : ∀x,DescentPackedColony.Accessible P (winner x) H G M w base)
    (mf : ∀x i,(marked x i).Fits w base) (room : ∀x i,H*chunks G M≤(marked x i).size)
    (own : ∀x,DescentPackedColony.Reads (winner x) (fun h g=>(physical h g).winner x) M m)
    (old : ∀x i,DescentPackedColony.Reads (marked x i) (fun h g=>(physical h g).neighbor x i) M m) (j : Fin (fields (2^k) A.degree (2*A.cap))) :
    DescentPackedZip.Source (Gather.expr winner marked P H j) (fun h g=>Gather.terrain physical h g j) M m := by
  have raw:=Gather.real_fields winner marked P (fun h g=>(physical h g).winner) (fun h g=>(physical h g).neighbor)
    (hostRotor hosts near) base m mounted access mf room own old j
  rw [terrain_eq A native S ready names win next groups hosts near grouped] at raw
  exact raw

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
