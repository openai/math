import OAI.Hierarchy.DescentReachedCountVenue
import OAI.Hierarchy.DescentReachedCountPadding
import OAI.Hierarchy.DescentGroupPeerOrder
import OAI.Hierarchy.DescentPhysicalRosterPrefix

namespace OAI
/-! The charged donor count at every canonical old vertex and every padding row. -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts
open DescentGroupPeerOrder DescentSharedCableNames DescentPacking.PackedMatch.Local
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentScalarVenueMask DescentHaloWalkRAM
open DescentOrdinaryRasterReturn ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
/-- Extending the host rectangle keeps the prior counts on real hosts and
returns zero on the remaining rows. -/
theorem padded_prior {V : Type} [Fintype V] {H₀ H₁ d blocks groups bits : ℕ}
    (wide : H₀≤H₁) (host : V↪Fin H₀) (near : V→Fin d→Option V)
    (prior : Fin blocks→Fin H₀→Fin groups→Cell bits) (h : Fin H₁) (g : Fin groups)
    (j : Fin (breadth d * blocks)) :
    priorValue (Gather.reaching (hostRotor (host.trans (Fin.castLEEmb wide)) near))
      (fun x=>extend (prior x)) h g j =
      extend (fun v u=>priorValue (Gather.reaching (hostRotor host near)) prior v u j) h g := by
  let small := Gather.reaching (hostRotor host near)
  let large := Gather.reaching (hostRotor (host.trans (Fin.castLEEmb wide)) near)
  let pair := finProdFinEquiv.symm j
  have real (v : Fin H₀) : priorValue large (fun x=>extend (prior x)) (Fin.castLEEmb wide v) g j =
      priorValue small prior v g j := by
    change (DescentSortedRoster.indexed large (Fin.castLEEmb wide v) pair.1).elim 0
      (fun u=>extend (prior pair.2) u g) = (DescentSortedRoster.indexed small v pair.1).elim 0 _
    rw [DescentSortedRoster.indexed_pad wide small large v (reaching_pad wide _ _ (physical_rotor wide host near) v) pair.1]
    cases DescentSortedRoster.indexed small v pair.1 with
    | none=>rfl
    | some u=>exact dite_eq_left u.isLt
  by_cases live : h.val<H₀
  · let v : Fin H₀ := ⟨h.val,live⟩
    have atHost : Fin.castLEEmb wide v=h := Fin.ext rfl
    simpa only [atHost,extend,dite_eq_left live] using real v
  · change (DescentSortedRoster.indexed large h pair.1).elim 0 (fun u=>extend (prior pair.2) u g) = _
    rw [show extend (fun v u=>priorValue small prior v u j) h g=0 from dite_eq_right live]
    cases hit : DescentSortedRoster.indexed large h pair.1 with
    | none=>rfl
    | some u=>
      obtain ⟨s,at_⟩ := (Finset.mem_filter.mp ((DescentSortedRoster.indexed_iff large h pair.1 u).mp hit).1).2
      exact dite_eq_right (Nat.not_lt.mpr (padded_donor_blank wide host near h (Nat.le_of_not_gt live) s u at_))

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {Gd : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z degree wire hist H M b w raw cap : ℕ}
    (r : Reached W Gd q ε S k age z degree wire hist) (wide : Fintype.card r.V≤H)
    (i : Dated.Operands) (base venueFloor actorFloor : ℕ)
local notation "G₀" => S.groupCount age
local notation "A" => r.placement
local notation "D" => (A).degree
local notation "paths" => breadth D
local notation "actual" => r.vertex.trans (Fin.castLEEmb wide)
local notation "near" => hostRoster (A) (r.vertex.trans Fin.valEmbedding)
local notation "order" => Gather.reaching (hostRotor r.vertex near)
local notation "physical" => Gather.reaching (hostRotor actual near)
local notation "census" => fun x h g=>Census.count (A) (Equiv.refl _) r.vertex b h g x
local notation "K" => 1+cap*6
local notation "L" => layout base H G₀ M k paths b
variable (ports : Ports (breadth r.placement.degree)) (route key : Fin (2^k)→Fin (1+cap*6)→Bank) (hub ends : Bank)
    (tokens : Fin (2^k)→Fin (1+cap*6)→Fin H→Fin (S.groupCount age)→Ticket (breadth r.placement.degree) raw)
    (hubs : Fin H→Fin (S.groupCount age)→Cell 1)

theorem run_original (old actor atCount : Memory w) (oldRoster : Fin H→Fin degree→Option (Fin H))
    (stage : stageVenue r wide i M b venueFloor oldRoster old)
    (arrived : Receiver.Raw ports route key hub ends actorFloor physical tokens hubs M actor)
    (earlier : venueFloor≤base) (didRoute : actorFloor≤base)
    (oldWords : ∀a<venueFloor,atCount a=old a) (actorWords : ∀a<actorFloor,atCount a=actor a)
    (room : (L).roof<2^w) :
    let dst:=(L).output ports i.atoms atCount
    ((L).program w ports i.atoms).Exec atCount dst ((L).ticks ports i.atoms) ∧
    CheapCode ((L).program w ports i.atoms) ∧
    Source (L).expr (fun (h : Fin H) g=>encode b (paths*2^k) (fun j=>
      extend (fun v u=>priorValue order census v u j) h g)) M dst ∧
    ∀a,a<base ∨ (L).roof≤a → dst a=atCount a := by
  intro dst
  have got:=run_venue r wide i ports route key hub ends physical tokens hubs base venueFloor actorFloor
    old actor atCount oldRoster stage arrived earlier didRoute oldWords actorWords room
  refine ⟨got.1,got.2.1,?_,got.2.2.2⟩
  have vals : (fun x h g=>Census.count (A) (Equiv.refl _) actual b h g x) =
      fun x=>extend (H:=H) (census x) := by
    funext x h g
    exact census_padded r wide h g x
  have agree : (fun h g=>encode b (paths*2^k) (priorValue physical
      (fun x h g=>Census.count (A) (Equiv.refl _) actual b h g x) h g)) =
      fun h g=>encode b (paths*2^k) (fun j=>extend (fun v u=>priorValue order census v u j) h g) := by
    rw [vals]
    funext h g
    apply congrArg (encode b (paths*2^k))
    funext j
    exact padded_prior wide r.vertex near census h g j
  rw [←agree]
  exact got.2.2.1

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts

end OAI
