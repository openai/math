import OAI.Hierarchy.DescentSeedLoaderExecution
import OAI.Hierarchy.DescentSeedVenueAfterCount
import OAI.Hierarchy.DescentDatedSeedAfterCountCode
import OAI.Hierarchy.DescentDatedSeedWideProgram
import OAI.Hierarchy.DescentDatedSeedCleared
import OAI.Hierarchy.DescentDatedVenueFloor
import OAI.Hierarchy.DescentDatedVenueBelow
import OAI.Hierarchy.DescentWideExteriorRoot
import OAI.Hierarchy.DescentExteriorAppendedWords

namespace OAI
/-! The physical first date starts at the counted tape returned by the named history validator. -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentSeedInitialTable DescentExteriorShelf DescentExterior DescentColonies DescentSIMDLookup DescentPackedColony
open DescentTerminalEpochChart DescentPackedProfileInstall Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {S : AtomSchedule} {G : PoweredGadget F} {q ε : ℝ}
    {k cp p wire s z₀ H w e j r t : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k)
    (publicWide : Fintype.card (Vertex X)≤H) (l : Layout) (header : ℕ)
local notation "g₀" => S.groupCount 0
local notation "M" => l.packedLanes
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "Q" => nodeArities X publicWide l
local notation "finish" => (chart).seedEnd top
local notation "i" => operands X l k H g₀
local notation "core" => DescentDatedSeedStartup.program X (Equiv.refl _) digits hs l w

theorem afterCount_price (payload : ℕ) (active : 0<chunks g₀ l.operandLanes) :
    afterCountTicks (S:=S) (H:=H) (k:=k) X l +
      7*DescentStaticWordColumn.names (afterCount X digits publicWide l header w) ≤
      1300+1600*(top-l.base+1)+115*((chart).names*(chart).rows) := by
  have paid:=wide_price X digits publicWide l header payload w active
  simp only [wideTicks,wideNode,afterCountTicks,afterCount,DescentStaticWordColumn.names_seq,
    DescentWideSeedFlags.names] at *
  omega

variable {c : (initialGroup X S.copies s).Choice}
    (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z₀) (wire:=wire) c digits)
    (wide : Fintype.card o.raw.V≤H)

variable (payload : ℕ) (seed : Select X S.copies l.seedWidth→P)
    (lo C grain : ℕ) (ss : List (Source P)) (origin extra : ℕ)
    (x : Fin e→Plane j r→Fin t→Bool) (z : P⊕Hidden e j r t→Bool) (back : Memory w)
local notation "lowEnd" => end_ (lo+DescentPackedEpochShelves.extent grain ss) C grain
local notation "frontSize" => origin+17*span j r t e
local notation "raw" => Root.appended frontSize extra
  (Root.widePackedImage X S.copies l.seedWidth payload w seed lo C grain ss origin x z) back
local notation "counted" => DescentWideSeedFlags.countedAt X S.copies l.seedWidth payload seed (z∘Sum.inl) raw
local notation "verdict" => DescentWideSeedFlags.endInput X S.copies l.seedWidth payload
local notation "entries" => DescentPackedSeed.rows X S.copies l.seedWidth payload

include o wide in
theorem wide_source_count (width : 2*digitsNeeded l.seedWidth≤payload)
    (signed : DescentSignedCableCodec.width 3 256*M≤w) (fields : l.operandBits*l.operandLanes≤w)
    (seedFits : verdict+(entries+1)<2^w) (seedBefore : verdict+(entries+1)≤lo)
    (shelves : lowEnd≤origin) (privateAfter : frontSize+extra≤header)
    (early : header<l.base) (space : finish<2^w) :
    afterCountImage X digits publicWide l header counted 0=((S.copies*Fintype.card (Vertex X):ℕ):Word w) := by
  have started : 0<DescentTerminalPackedSeedFlags.start X S.copies l.seedWidth payload := by
    unfold DescentTerminalPackedSeedFlags.start
    exact Nat.add_pos_right _ (Nat.two_pow_pos _)
  have dictionary : 0<(DescentWideSeedFlags.dictionary X S.copies l.seedWidth payload).base := by
    change 0<DescentTerminalPackedSeedFlags.start X S.copies l.seedWidth payload+_
    omega
  have below : 0<verdict := dictionary.trans_le (Nat.le_add_right ..)
  have loFits : lo≤lowEnd := by dsimp only [end_,DescentPackedProfileInstall.dict]; omega
  have beforeLo : 0 < lo := by omega
  have beforeFront : 0 < frontSize :=
    (beforeLo.trans_le (loFits.trans shelves)).trans_le (Nat.le_add_right ..)
  have beforeHeader : 0 < header :=
    beforeFront.trans_le ((Nat.le_add_right ..).trans privateAfter)
  have checked:=Root.wideCounted_on X S.copies l.seedWidth payload w seed lo C grain ss origin x z raw
    (fun a h=>Root.append_low _ _ _ _ h) width seedFits seedBefore shelves
  have run_:=wide_after_count X digits publicWide l header o wide counted signed fields early space
  calc
    afterCountImage X digits publicWide l header counted 0 = counted 0 :=
      run_.2.2.2.2 0 beforeHeader.ne (.inl (beforeHeader.trans early))
    _ = raw 0 := checked.2.2.2.2 0 (.inl below)
    _ = Root.widePackedImage X S.copies l.seedWidth payload w seed lo C grain ss origin x z 0 :=
      Root.append_low _ _ _ _ beforeFront
    _ = Root.wideOriginal X S.copies l.seedWidth payload w seed lo C grain ss (z∘Sum.inl) 0 :=
      Root.widePacked_original X S.copies l.seedWidth payload w seed lo C grain ss origin x z
        shelves (beforeLo.trans_le loFits)
    _ = DescentWideSeedFlags.initial X S.copies l.seedWidth payload w seed (z∘Sum.inl) 0 :=
      DescentPackedEpochShelves.frame lo C grain ss (z∘Sum.inl) _ (a:=0) beforeLo
    _ = _ := (DescentWideSeedFlags.lower X S.copies l.seedWidth payload w seed (z∘Sum.inl) dictionary).trans
      (DescentPackedSeed.wide_site_count X payload w _)

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
