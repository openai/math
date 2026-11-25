import OAI.Hierarchy.DescentSeedNativeWideNode
import OAI.Hierarchy.DescentSeedTokenProgram

namespace OAI
/-! # The public code and clock of the combined initial register loader -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentSeedInitialTable DescentColonies DescentSIMDLookup DescentPackedColony DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM Catalyst ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec)
  {k cp p H : ℕ} (X : Approximation F cp p)
  (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k)
  (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top
local notation "i₀" => operands X l k H g₀
local notation "lanes" => DescentDatedSeedStartup.Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "limit" => DescentDatedSeedStartup.Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "cpu" => DescentDatedSeedStartup.Primitive.program X G op S.copies l.seedWidth Z payload k H g₀ lanes finish hs
local notation "cost" => DescentDatedSeedStartup.Primitive.ticks X G op S.copies l.seedWidth Z payload k H g₀ lanes finish hs
local notation "combine" => DescentDatedSeedStartup.Primitive.image X G op S.copies l.seedWidth Z payload k H g₀ lanes finish hs

def completeAfter (w : ℕ) := (afterCount X digits publicWide l header w).seq ((cpu) w)
def completeTicks (w : ℕ) := afterCountTicks (S:=S) (k:=k) (H:=H) X l + (cost) w
def selectedProgram {w : ℕ} := (DescentWideSeedFlags.check X S.copies l.seedWidth payload w).seq
  (completeAfter G op X digits publicWide l header payload Z w)

def completeProgram {w : ℕ} (radix : S.radix=2^k) :=
  selectedProgram G op X (S.initialDigits radix) publicWide l header payload Z (w:=w)

theorem full_price (w : ℕ) :
    (4+(DescentPackedSeed.rows X S.copies l.seedWidth payload+1)*66+completeTicks (S:=S) (k:=k) G op X publicWide l payload Z w)+
      7*DescentStaticWordColumn.names (selectedProgram G op X digits publicWide l header payload Z (w:=w)) =
    (wideTicks (S:=S) (k:=k) (H:=H) X l payload+
      7*DescentStaticWordColumn.names (wideNode X digits publicWide l header payload w))+
    ((cost) w+7*DescentStaticWordColumn.names ((cpu) w)) :=by
  simp only [selectedProgram,completeAfter,completeTicks,afterCount,afterCountTicks,wideNode,wideTicks,
    DescentStaticWordColumn.names_seq]
  omega

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
