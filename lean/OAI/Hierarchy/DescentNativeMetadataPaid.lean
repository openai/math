import OAI.Hierarchy.DescentVenueMetadataPaidField
import OAI.Hierarchy.DescentStageVenuePaidPages

namespace OAI
/-! # Reading the funded metadata prefix at its actual predecessor pitch -/
namespace Hierarchy.DescentSixParty.StageVenueTail.Date
open DescentColonies DescentCompiler DescentSIMDLookup DescentPackedColony DescentPacking.PackedMatch.Local.Stage
open DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

theorem paid_prefix {H H' G M b w : ℕ} (crop : H'≤H) (bank : Bank) (values : Fin H→Fin G→Cell b)
    (m : Memory w) (observed : Reads bank values M m) :
    Reads bank (fun (h:Fin H') g=>values (h.castLE crop) g) M m:=by
  intro z
  let old : Row H G M:=(z.1.castLE crop,z.2)
  have address:(row H G M old).val=(row H' G M z).val:=by
    simp [row,finProdFinEquiv_apply_val,old]
  have source:=observed old
  rw [address] at source
  exact source

variable {F P : Type} [Field F] {u : ℕ} {bits : P→ℕ} {W : MarkedWorld F u P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D wire hist H w : ℕ}
  (r : Reached W G q ε S k i z D wire hist) (d : Date) (B : Sources)

theorem metadata_paid_source (wide : Fintype.card r.V≤d.hosts) (groups : S.groupCount i=d.groups)
    (blocks : k=d.k) (hCrop : H≤d.hosts) (x : Block k) (start : ℕ) (m : Memory w)
    (available : d.Space B start w) (paid : paidCounts B r wide d.paidBits d.paidLanes m) :
    Source (d.metadataPaid B x.val)
      (fun (h:Fin H) g=>Census.count r.placement (Equiv.refl _) (r.vertex.trans (Fin.castLEEmb wide))
        d.paidBits (h.castLE hCrop) g x) d.paidLanes m:=by
  let key:=x.cast (congrArg (2^·) blocks)
  have stored:=available.paid key
  rw [metadataPaid,ite_eq_left (show x.val<2^d.k from key.isLt)]
  apply source_column (B.paid x.val) start stored.1 m _
  · rw [←groups] at stored
    exact (Nat.mul_le_mul_right _ hCrop).trans stored.2
  · exact paid_prefix (G := S.groupCount i) (M := d.paidLanes) (b := d.paidBits) hCrop
      (B.paid x.val) (fun h g => Census.count r.placement (Equiv.refl _)
        (r.vertex.trans (Fin.castLEEmb wide)) d.paidBits h g x) m (paid x)

end
end Hierarchy.DescentSixParty.StageVenueTail.Date

end OAI
