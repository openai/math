import OAI.Hierarchy.DescentReachedCountPublish
import OAI.Hierarchy.DescentDatedStageVenue
import OAI.Hierarchy.DescentScalarVenueReceiver
import OAI.Hierarchy.DescentPaddedRasterValue

namespace OAI
/-! Dated census snapshots after the physical route, key and actor publishers. -/
namespace Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local DescentPacking.PackedMatch.Local.Stage
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentScalarVenueMask DescentSharedCableNames
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {Gd : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age z degree wire hist H M b w paths raw cap : ℕ}
    (r : Reached W Gd q ε S k age z degree wire hist)
    (wide : Fintype.card r.V≤H) (i : Dated.Operands)
variable (ports : Ports paths) (route key : Fin (2^k)→Fin (1+cap*6)→Bank)
    (hub ends : Bank) (walks : Fin H→Fin paths→Option (Fin H))
    (tokens : Fin (2^k)→Fin (1+cap*6)→Fin H→Fin (S.groupCount age)→Ticket paths raw)
    (hubs : Fin H→Fin (S.groupCount age)→Cell 1)

theorem run_venue (base venueFloor actorFloor : ℕ) (old actor atCount : Memory w)
    (oldRoster : Fin H→Fin degree→Option (Fin H))
    (stage : stageVenue r wide i M b venueFloor oldRoster old)
    (arrived : Receiver.Raw (cap:=cap) (raw:=raw) ports route key hub ends actorFloor walks tokens hubs M actor)
    (earlier : venueFloor≤base) (didRoute : actorFloor≤base)
    (oldWords : ∀a<venueFloor,atCount a=old a) (actorWords : ∀a<actorFloor,atCount a=actor a)
    (room : (layout base H (S.groupCount age) M k paths b).roof<2^w) :
    let L:=layout base H (S.groupCount age) M k paths b
    let dst:=L.output ports i.atoms atCount
    (L.program w ports i.atoms).Exec atCount dst (L.ticks ports i.atoms) ∧
    CheapCode (L.program w ports i.atoms) ∧
    Source L.expr (fun h g=>encode b (paths*2^k) (priorValue walks
      (fun x v j=>Census.count r.placement (Equiv.refl _) (r.vertex.trans (Fin.castLEEmb wide)) b v j x) h g)) M dst ∧
    ∀a,a<base ∨ L.roof≤a → dst a=atCount a := by
  intro L dst
  let prior (x : Fin (2^k)) (h : Fin H) (g : Fin (S.groupCount age)) :=
    Census.count r.placement (Equiv.refl _) (r.vertex.trans (Fin.castLEEmb wide)) b h g x
  have access : Accessible ports hub H (S.groupCount age) M w base :=
    RoleControl.Layout.accessible_after arrived.shape didRoute
  have mounted : Mounted ports (DescentSortedRoster.indexed walks) atCount (S.groupCount age) M :=
    RoleControl.Layout.previous_mounted arrived.shape (DescentSortedRoster.indexed walks) actorWords arrived.routed
  obtain ⟨_,_,_,_,_,_,_,early,data_⟩:=stage
  have reads (x : Fin (2^k)) : Source (i.atoms x.val) (prior x) M atCount := by
    intro p
    exact (eval_below (i.atoms x.val) _ old atCount (early x.val) oldWords).trans (data_ x p)
  exact L.run ports hub i.atoms atCount walks prior
    (fun j _=>ProtocolRAMGeneratedWrite.fits_mono _ earlier (early j)) reads access mounted room

theorem census_padded (h : Fin H) (g : Fin (S.groupCount age)) (x : Fin (2^k)) :
    Census.count r.placement (Equiv.refl _) (r.vertex.trans (Fin.castLEEmb wide)) b h g x=
      DescentOrdinaryRasterReturn.extend
        (fun a j=>Census.count r.placement (Equiv.refl _) r.vertex b a j x) h g :=
  DescentOrdinaryRasterReturn.padded_count r.placement (Equiv.refl _) r.vertex wide h g x

end
end Hierarchy.DescentOrdinaryAtomFieldRAM.RoleCounts

end OAI
