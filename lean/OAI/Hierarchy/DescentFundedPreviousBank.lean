import OAI.Hierarchy.DescentFundedBankAddress
import OAI.Hierarchy.DescentStageVenueChange
import OAI.Hierarchy.DescentDatedSeedOperands

namespace OAI
/-! # The same funded bank after a seed, ordinary date, or reset -/
namespace Hierarchy.DescentFundedCensus
open DescentSixParty DescentCompiler DescentColonies DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

structure IssuedBanks (io : Dated.Operands) (H G M : ℕ) : Prop where
  row : ∀x,io.atoms x=.lookup (priorBank io x) .row
  capacity : ∀x,H*chunks G M≤(priorBank io x).size

theorem from_venue (d : StageVenueTail.Date) (B : StageVenueTail.Sources) (base : ℕ) :
    IssuedBanks (d.operands B base) d.hosts d.groups d.lanes :=
  ⟨fun _=>rfl,fun _=>Nat.le_pow_clog (by decide) _⟩

theorem from_seed {F : Type} [Field F] {k p : ℕ}
    (X : Catalyst.Approximation F k p) (l : DescentDatedSeedStartup.Layout) (d H G : ℕ) :
    IssuedBanks (DescentDatedSeedStartup.operands X l d H G) H G l.packedLanes :=
  ⟨fun _=>rfl,fun _=>(DescentSeedInitialTable.capacities H G l.packedLanes 3).2.2⟩

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k age z D wire hist H paid M w start : ℕ}
  (r : Reached W G q ε S k age z D wire hist) (wide : Fintype.card r.V≤H)
  (io : Dated.Operands) (peer : Fin H→Fin D→Option (Fin H)) {m later : Memory w}
local notation "groups" => S.groupCount age
local notation "host" => r.vertex.trans (Fin.castLEEmb wide)

/-- The honest stage-venue receipt gives the original RAM page, its real
extent and the whole packed word, even for a partly filled final chunk. -/
theorem original_pages (layout : IssuedBanks io H groups M) (seen : stageVenue r wide io M paid start peer m)
    (keep : ∀a,a<start→later a=m a) :
    ∀x : Block k,(priorBank io x.val).Fits w start ∧ H*chunks groups M≤(priorBank io x.val).size ∧
      Reads (priorBank io x.val) (fun h g=>Census.count r.placement (Equiv.refl _) host paid h g x) M later :=by
  obtain ⟨_,_,_,_,_,_,_,safe,original⟩:=seen
  intro x
  have f:=safe x.val
  have equality:=layout.row x.val
  rw [equality] at f
  refine ⟨f.1,layout.capacity _,?_⟩
  intro pos
  let j:=(row H groups M pos).val
  have valid:j<(priorBank io x.val).size:=(row H groups M pos).isLt.trans_le (layout.capacity _)
  have raw:=original x pos
  rw [equality] at raw
  change m ((priorBank io x.val).base+(j:Word w).val%(priorBank io x.val).size)=_ at raw
  rw [Fin.val_cast_of_lt (valid.trans f.1.2.1),Nat.mod_eq_of_lt valid] at raw
  exact (keep _ ((Nat.add_lt_add_left valid _).trans_le f.1.2.2)).trans raw

end
end Hierarchy.DescentFundedCensus

end OAI
