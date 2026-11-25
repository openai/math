import OAI.Hierarchy.DescentResetTrunkOriginalHeaders
import OAI.Hierarchy.DescentResetStemOriginalSlots
import OAI.Hierarchy.DescentResetFieldReceipt
import OAI.Hierarchy.DescentRankSheetShapes
import OAI.Hierarchy.DescentPhysicalResetDateOperands

namespace OAI
/-! # The recorded stem header in the ranked candidate sheet -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentParallelBase DescentCompiler DescentColonies DescentDatedAddressBook DescentSIMDLookup DescentPackedColony
open DescentResetFieldAssembler DescentResetCandidatePair DescentPackedZip ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "used" => Fintype.card B.next.V
local notation "oldRank" => B.frame.host.symm.toEmbedding.trans input.vertex

/-- Padding changes the finite type of the old host field. The number of occupied
physical names below each new name remains the same. -/
theorem rack_of_original {H₀ H₁ : ℕ} (pad : Fintype.card input.V≤H₀) (bound : used≤H₁) :
    rackOf B (((Z).denseHostRank T ((oldRank).trans (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)) =
      originalTrunkRack B := by
  let ranked:=((Z).denseHostRank T ((oldRank).trans (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)
  have position (u : B.next.V) : (ranked u).val=(denseOrder B u).val := by
    change ((Z).denseHostRank T ((oldRank).trans (Fin.castLEEmb pad)) u).val=((Z).denseHostRank T oldRank u).val
    rw [(Z).denseHostRank_read T ((oldRank).trans (Fin.castLEEmb pad)) u,(Z).denseHostRank_read T oldRank u]; rfl
  funext r
  by_cases live : r.val<used
  · let u:=(denseOrder B).symm ⟨r.val,live⟩
    have same : ranked u=r:=Fin.ext ((position u).trans (congrArg Fin.val ((denseOrder B).apply_symm_apply ⟨r.val,live⟩)))
    calc
      rackOf B ranked r = rackOf B ranked (ranked u) := congrArg (rackOf B ranked) same.symm
      _ = some u := rack_present B ranked u
      _ = originalTrunkRack B r := by simp only [originalTrunkRack,dite_eq_left live,u]
  · have missing (u : B.next.V) (same : ranked u=r) : False := by
      have eqn : (denseOrder B u).val=r.val := (position u).symm.trans (congrArg Fin.val same)
      exact live (eqn ▸ (denseOrder B u).isLt)
    exact (rack_missing B ranked r missing).trans (by simp only [originalTrunkRack,dite_eq_right live])

private theorem shaped_stem {X X' s s' c c' p p' : ℕ} (hx:X=X') (hs:s=s') (hc:c=c') (hp:p=p')
    (src : Inputs X s c p) (x : Fin X') (j : Fin s') :
    shaped hx hs hc hp src x (.inl j)=src (x.cast hx.symm) (.inl (j.cast hs.symm)) := by
  subst X';subst s';subst c';subst p';rfl

variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "s₀" => (v₀).sheets
local notation "pos" => CandidateSheet.index (stemsCount B) (contactCount B) (privateCount B)
local notation "stemWordAt" x:arg j:arg => (v₀).front.stemOperand ((v₀).actorEnd base₀) x j

/-- The last register read of the calendar stem program supplies both address
room and the seven packed fields of the left sector in the numbered sheet. -/
theorem named_stem_sector {hosts : ℕ} (pad : Fintype.card input.V≤hosts) (bound : used≤(s₀).hosts)
    (hx : (v₀).receiver.blocks=2^k) (hs : I.sectors.stems=stemsCount B)
    (hc : I.sectors.contacts=contactCount B) (hp : I.sectors.privates=privateCount B)
    (state : Computability.VPVNP.BurstRAM.Memory bw)
    (seen : ∀(x : Fin (2^k)) (j : Fin (stemsCount B)),
      (stemWordAt x.val j.val).Fits bw ((v₀).trunkEnd base₀) ∧
      Source (stemWordAt x.val j.val) (fun (r : Fin (s₀).hosts) g₀=>
        DescentResetFieldAssembler.raw (s₀).metaBits (actualMeta B (originalTrunkRack B) x (stemShelf B j) r g₀)) (s₀).lanes state) :
    ∀(x : Fin (2^k)) (j : Fin (stemsCount B)),
      (shaped hx hs hc hp I.sectors.header x (.inl j)).Fits bw ((v₀).trunkEnd base₀) ∧
      Source (shaped hx hs hc hp I.sectors.header x (.inl j)) (fun r g₀=>
        DescentResetFieldAssembler.raw (s₀).metaBits (actualMeta B
          (rackOf B (((Z).denseHostRank T ((oldRank).trans (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)))
          x (pos (.inl j)) r g₀)) (s₀).lanes state := by
  intro x j
  have address : shaped hx hs hc hp I.sectors.header x (.inl j)=stemWordAt x.val j.val := by
    rw [shaped_stem]; rfl
  have index : pos (.inl j)=stemShelf B j:=Fin.ext (CandidateSheet.stem_val j)
  rw [address,index,rack_of_original B pad bound]
  exact seen x j

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
