import OAI.Hierarchy.DescentSeedCountImage

namespace OAI
/-! # The public host count survives the seed node chart and counter clear -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentInitialHost DescentCompiler DescentSixParty DescentColonies
open DescentSeedRoot DescentPackedSeed DescentPackedColony DescentSIMDLookup DescentSeedInitialTable
open Computability.VPVNP.BurstRAM PrivateRAM Catalyst ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule}
  {k cp p H w : ℕ} (X : Approximation F cp p)
  (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k)
  (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout) (header : ℕ)
local notation "G₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "db" => directoryBase X l H G₀ k
local notation "top" => endAddress X l H G₀ k
local notation "ct" => sharedHostCountBank db H G₀ l.packedLanes
local notation "chart" => nodeChart l k H G₀
local notation "finish" => (chart).seedEnd top
local notation "Q" => nodeArities X publicWide l
theorem roster_host_count (m : Memory w) (early : header < l.base) (room : finish<2^w) :
    afterCountImage X digits publicWide l header m (ct).base=(Fintype.card (Vertex X):Word w) :=by
  let t:=output X (Equiv.refl _) digits hs l m
  have leq : top ≤ finish:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have fits:=shared_host_fits db H G₀ l.packedLanes w (leq.trans_lt room)
  have lt : (ct).base < top:=by have b:=fits.2.2;change (ct).base+1 ≤ top at b;omega
  have starts:=fences X l H G₀ k
  have start : db≤(ct).base:=by
    dsimp [sharedHostCountBank,bank]
    omega
  have earlier : header < (ct).base :=early.trans_le (starts.1.trans (starts.2.1.trans start))
  have a:=(chart).seedIssued top Q (DescentPrivateHeader.initialized header t) room
  have value:=shared_host_count (G:=G₀) (M:=l.packedLanes) X hs db k l.wire l.history l.seedWidth l.fieldBits
    (operandMem X (Equiv.refl _) digits hs l m)
  have stock : t (ct).base = (Fintype.card (Vertex X):Word w) := by
    unfold t output
    simpa only [Bank.read,Fin.val_zero,Nat.zero_mod,Nat.add_zero] using value
  exact (a.2.1 (ct).base (.inl lt)).trans
    ((DescentPrivateHeader.initialized_frame header t _ (ne_of_gt earlier)).trans stock)

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
