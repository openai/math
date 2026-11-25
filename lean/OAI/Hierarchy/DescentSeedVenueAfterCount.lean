import OAI.Hierarchy.DescentSeedNativeWideNode
import OAI.Hierarchy.DescentSeedCountImage
import OAI.Hierarchy.DescentDatedSeedCleared
import OAI.Hierarchy.DescentDatedVenueFloor
import OAI.Hierarchy.DescentDatedVenueBelow

namespace OAI
/-! # The initial reached venue after the seed census and the two node pages -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentSeedInitialTable DescentColonies DescentSIMDLookup DescentPackedColony
open Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
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

variable {c : (initialGroup X S.copies s).Choice}
    (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z₀) (wire:=wire) c digits)
    (wide : Fintype.card o.raw.V≤H)

theorem wide_after_count (m : Memory w)
    (signed : DescentSignedCableCodec.width 3 256*M ≤ w) (fields : l.operandBits*l.operandLanes ≤ w)
    (early : header < l.base) (space : finish < 2^w) :
    let final := afterCountImage X digits publicWide l header m
    (afterCount X digits publicWide l header w).Exec m final (afterCountTicks (S:=S) (H:=H) (k:=k) X l) ∧
    final header=0 ∧ stageVenue o.source (source_hosts X o wide) (i) M l.fieldBits finish (roster X hs) final ∧
    (∀ (f : Fin 2) (x : Block k), Reads ((chart).seedBank top f x) ((chart).seedField Q f) l.operandLanes final) ∧
    ∀ a, a≠header → a<l.base ∨ finish≤a → final a=m a := by
  intro final
  let middle := output X (Equiv.refl _) digits hs l m
  let done_ := DescentPrivateHeader.initialized header middle
  have ends:=fences X l H g₀ k
  have stop : top≤finish := (Nat.le_add_right top _).trans (Nat.le_add_right ..)
  have floor : l.base≤top := ends.1.trans (ends.2.1.trans ends.2.2)
  have build : (core).Exec m middle (DescentDatedSeedStartup.clock X l H g₀ k) :=
    execute X (Equiv.refl _) digits hs l m signed fields (stop.trans_lt space)
  have old:=retain X (Equiv.refl _) digits hs l m signed fields (stop.trans_lt space)
  have clear:=source_after_clear X o wide l m signed fields top le_rfl (stop.trans_lt space) header early
  have metadataRun:=(chart).seedIssued top Q done_ space
  refine ⟨?_, (metadataRun.2.1 header (.inl (early.trans_le floor))).trans clear.2.1,?_,
    (fun f x=>(chart).seedRead top Q done_ f x),?_⟩
  · intro np nk nr machine pc reg pub exit install advice cfg ini status same
    exact Procedure.Exec.then (Procedure.Exec.then build clear.1) metadataRun.1
      machine pc reg pub exit install advice cfg ini status same
  · apply stageVenue_mono o.source (source_hosts X o wide) (i) M l.fieldBits top (roster X hs) final stop
    apply stageVenue_below o.source (source_hosts X o wide) (i) M l.fieldBits top (roster X hs) done_ final clear.2.2.1
    · intro x a
      have bounds:=wire_room (H:=H) (G:=g₀) (d:=k) X l top le_rfl (stop.trans_lt space) x.val a.val
      exact (Nat.add_le_add_left bounds.2 _).trans bounds.1.2.2
    · exact fun a ha=>metadataRun.2.1 a (.inl ha)
  · intro a away outside
    exact (metadataRun.2.1 a (by omega)).trans ((DescentPrivateHeader.initialized_frame header middle a away).trans
      (old a (by omega)))

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
