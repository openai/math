import OAI.Hierarchy.DescentReachedCountRepitch

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
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {Gd : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z degree wire hist H M oldM b w raw cap : ℕ}
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
local notation "L" => Repitch.count H G₀ oldM M k paths b base
variable (ports : Ports (breadth r.placement.degree)) (route key : Fin (2^k)→Fin (1+cap*6)→Bank) (hub ends : Bank)
    (tokens : Fin (2^k)→Fin (1+cap*6)→Fin H→Fin (S.groupCount age)→Ticket (breadth r.placement.degree) raw)
    (hubs : Fin H→Fin (S.groupCount age)→Cell 1)

theorem run_original_on_ports (old atCount : Memory w) (oldRoster : Fin H→Fin degree→Option (Fin H))
    (stage : stageVenue r wide i oldM b venueFloor oldRoster old)
    (positive : 0 < oldM) (earlier : venueFloor ≤ base) (oldWords : ∀a < venueFloor,atCount a=old a)
    (visible : Accessible ports hub H G₀ M w base)
    (ready : Mounted ports (DescentSortedRoster.indexed physical) atCount G₀ M)
    (room : (L).roof<2^w) :
    let p:=Repitch.phase H G₀ oldM M k paths b base w ports i.atoms
    p.Runs atCount ∧
    Source (L).expr (fun (h : Fin H) g=>encode b (paths*2^k) (fun j=>
      extend (fun v u=>priorValue order census v u j) h g)) M (p.image atCount) ∧
    ∀a,a < base ∨ (L).roof ≤ a → p.image atCount a=atCount a := by
  intro p
  obtain ⟨_,_,_,_,_,_,_,early,data_⟩:=stage
  have got:=Repitch.run H G₀ oldM M k paths b base ports hub i.atoms atCount physical
    (fun x h g=>Census.count (A) (Equiv.refl _) actual b h g x)
    (fun j _=>ProtocolRAMGeneratedWrite.fits_mono _ earlier (early j))
    (fun x u=>(eval_below (i.atoms x.val) _ old atCount (early _) oldWords).trans (data_ x u)) positive
    visible ready room
  refine ⟨got.1,?_,got.2.2⟩
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
  exact got.2.1

theorem run_original_repacked (old actor atCount : Memory w) (oldRoster : Fin H→Fin degree→Option (Fin H))
    (stage : stageVenue r wide i oldM b venueFloor oldRoster old)
    (arrived : Receiver.Raw ports route key hub ends actorFloor physical tokens hubs M actor)
    (positive : 0 < oldM) (earlier : venueFloor ≤ base) (didRoute : actorFloor ≤ base)
    (oldWords : ∀a < venueFloor,atCount a=old a) (actorWords : ∀a < actorFloor,atCount a=actor a)
    (room : (L).roof<2^w) :
    let p:=Repitch.phase H G₀ oldM M k paths b base w ports i.atoms
    p.Runs atCount ∧
    Source (L).expr (fun (h : Fin H) g=>encode b (paths*2^k) (fun j=>
      extend (fun v u=>priorValue order census v u j) h g)) M (p.image atCount) ∧
    ∀a,a < base ∨ (L).roof ≤ a → p.image atCount a=atCount a := by
  exact run_original_on_ports r wide i base venueFloor ports hub old atCount oldRoster stage positive earlier oldWords
    (RoleControl.Layout.accessible_after arrived.shape didRoute)
    (RoleControl.Layout.previous_mounted arrived.shape _ actorWords arrived.routed) room

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts

end OAI
