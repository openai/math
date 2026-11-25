import OAI.Hierarchy.DescentPhysicalRosterPrefix
import OAI.Hierarchy.DescentPaddedRasterValue
import OAI.Hierarchy.DescentScalarVenueFields

namespace OAI
/-! # Exact target-name digits at every real and padded old host -/
namespace Hierarchy.DescentScalarVenueMask
open DescentSIMDLookup DescentSortedRoster DescentSharedCableNames
open DescentPackedActorMask
noncomputable section
variable {H H' paths r cap G raw : ℕ} (wide : H≤H')
variable (small : Fin H→Fin paths→Option (Fin H)) (large : Fin H'→Fin paths→Option (Fin H'))
    (agree : ∀v s,large (Fin.castLEEmb wide v) s=(small v s).map (Fin.castLEEmb wide))

include agree in
theorem hit_pad (v : Fin H) (s p : Fin paths) :
    DescentScalarVenueDirectory.hit large s (Fin.castLEEmb wide v) p=DescentScalarVenueDirectory.hit small s v p :=by
  unfold DescentScalarVenueDirectory.hit
  rw [DescentSortedRoster.indexed_pad wide small large v (agree v) s]
  cases DescentSortedRoster.indexed small v s with
  | none=>rfl
  | some u=>
    change decide (large (Fin.castLEEmb wide u) p=some (Fin.castLEEmb wide v))=decide (small u p=some v)
    rw [agree u p]
    cases small u p <;> simp []

variable (t : Fin r→Fin (1+cap*6)→Fin H→Fin G→Ticket paths raw)
    (t' : Fin r→Fin (1+cap*6)→Fin H'→Fin G→Ticket paths raw)
    (hubs : Fin H→Fin G→ Cell 1) (hubs' : Fin H'→Fin G→ Cell 1)
    (k gain slots low : ℕ)

include agree in
theorem fields_real (real : ∀x j h g,t' x j (Fin.castLEEmb wide h) g=t x j h g)
    (hub : ∀h g,hubs' (Fin.castLEEmb wide h) g=hubs h g) (h : Fin H) (g : Fin G) (j : Fin (actors (paths*r) cap)) :
    fields large t' hubs' k gain slots low (Fin.castLEEmb wide h) g j=fields small t hubs k gain slots low h g j :=by
  let z:Fin (paths*r)×Fin (1+cap*6):=finProdFinEquiv.symm j
  let s:Fin paths×Fin r:=finProdFinEquiv.symm z.1
  let id:=(indexed small h s.1).bind (fun u=>t s.2 z.2 u g)
  have eqn : (indexed large (Fin.castLEEmb wide h) s.1).bind (fun u=>t' s.2 z.2 u g)=id :=by
    rw [DescentSortedRoster.indexed_pad wide small large h (agree h) s.1]
    dsimp only [id]
    cases indexed small h s.1 with
    | none=>rfl
    | some u=>exact real s.2 z.2 u g
  change returned k gain slots raw low large s.1 (Fin.castLEEmb wide h) (hubs' (Fin.castLEEmb wide h) g)
      ((indexed large (Fin.castLEEmb wide h) s.1).bind (fun u=>t' s.2 z.2 u g))=
    returned k gain slots raw low small s.1 h (hubs h g) id
  rw [eqn,hub]
  unfold returned reached
  cases dp:id with
  | none=>rfl
  | some u=>simp only [Option.map_some,Option.getD_some,hit_pad wide small large agree]

theorem fields_ghost (h : Fin H') (g : Fin G) (j : Fin (actors (paths*r) cap))
    (blank : ∀s u,large h s=some u→H≤u.val)
    (empty : ∀x t (u : Fin H'),H≤u.val→t' x t u g=none) :
    fields large t' hubs' k gain slots low h g j=0 :=by
  let z:Fin (paths*r)×Fin (1+cap*6):=finProdFinEquiv.symm j
  let s:Fin paths×Fin r:=finProdFinEquiv.symm z.1
  have gone : (indexed large h s.1).bind (fun u=>t' s.2 z.2 u g)=none :=by
    cases e:indexed large h s.1 with
    | none=>rfl
    | some u=>
      have present:=((DescentSortedRoster.indexed_iff large h s.1 u).mp e).1
      obtain ⟨i,at_⟩:=(Finset.mem_filter.mp present).2
      exact empty s.2 z.2 u (blank i u at_)
  change returned k gain slots raw low large s.1 h (hubs' h g)
      ((indexed large h s.1).bind (fun u=>t' s.2 z.2 u g))=0
  rw [gone]
  simp [returned,reached,keepRaw,trimmed,Packed.readToken,Packed.token]


open DescentHaloWalkRAM DescentPacking.PackedMatch.Local.Stage DescentOrdinaryRasterReturn
theorem padded_targets {V : Type} [Fintype V] {d : ℕ} (host : V↪Fin H) (near : V→Fin d→Option V)
    (orig : Fin r→Fin (1+cap*6)→Fin H→Fin G→Ticket (breadth d) raw)
    (padded : Fin r→Fin (1+cap*6)→Fin H'→Fin G→Ticket (breadth d) raw)
    (actual : ∀x j h g,padded x j (Fin.castLEEmb wide h) g=orig x j h g)
    (vacant : ∀x j (h : Fin H') g,H≤h.val→padded x j h g=none)
    (sameHub : ∀h g,hubs' (Fin.castLEEmb wide h) g=hubs h g)
    (u : Fin H') (g : Fin G) (j : Fin (actors (breadth d*r) cap)) :
    fields (Gather.reaching (hostRotor (host.trans (Fin.castLEEmb wide)) near)) padded hubs' k gain slots low u g j=
      extend (fun h g=>fields (Gather.reaching (hostRotor host near)) orig hubs k gain slots low h g j) u g :=by
  by_cases live : u.val<H
  · let h : Fin H := ⟨u.val,live⟩
    have same : (Fin.castLEEmb wide) h=u := Fin.ext rfl
    have agree:=reaching_pad wide _ _ (physical_rotor wide host near)
    have yes:=fields_real wide _ _ agree orig padded hubs hubs' k gain slots low actual sameHub h g j
    rw [same] at yes
    simpa only [extend,dite_eq_left live] using yes
  · have no:=fields_ghost (H:=H) (large:=Gather.reaching (hostRotor (host.trans (Fin.castLEEmb wide)) near))
      (t':=padded) (hubs':=hubs') k gain slots low u g j
      (padded_donor_blank wide host near u (Nat.le_of_not_gt live)) (fun x s v hv=>vacant x s v g hv)
    simpa only [extend,dite_eq_right live] using no


end
end Hierarchy.DescentScalarVenueMask

end OAI
