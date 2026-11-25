import OAI.Hierarchy.DescentSeedLoaderExecution
import OAI.Hierarchy.DescentSeedVenueAfterCount

namespace OAI
/-! # The single seed initialization after validating the original selector shelf -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentSixParty.SeedNamed DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
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

variable {q ε : ℝ} {wire s z₀ w : ℕ} {c : (initialGroup X S.copies s).Choice}
  (o : Origin X (G:=G) (S:=S) (q:=q) (fee:=ε) (z:=z₀) (wire:=wire) c digits)
  (wide : Fintype.card o.raw.V ≤ H)
local notation "final" => completeImage G op X digits publicWide l header payload Z

theorem complete_after_count (m : Memory w) (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w)
    (fields : l.operandBits*l.operandLanes ≤ w) (early : header < l.base) (sourceSpace : publicWords X+span jobs ≤ finish)
    (live : 0 < lanes) (machine : payload ≤ w) (space : limit < 2^w) :
    (completeAfter G op X digits publicWide l header payload Z w).Exec m ((final) m)
      (completeTicks (S:=S) (k:=k) G op X publicWide l payload Z w) ∧
    (final) m header=0 ∧
    stageVenue o.source (source_hosts X o wide) (i₀) l.packedLanes l.fieldBits limit (roster X hs) ((final) m) ∧
    (∀(f : Fin 2) (x : Block k), Reads ((chart).seedBank top f x) ((chart).seedField Q f) l.operandLanes ((final) m)) ∧
    ∀u,u≠header → u < l.base ∨ limit ≤ u → (final) m u=m u :=by
  let prev:=afterCountImage X digits publicWide l header m
  obtain ⟨first,second⟩:=DescentDatedSeedStartup.Primitive.fences X S.copies l.seedWidth payload k H g₀ lanes finish
  have topBound : top ≤ finish := (Nat.le_add_right top _).trans (Nat.le_add_right ..)
  have upper : finish≤limit:=first.trans second
  have cut : finish < 2^w := upper.trans_lt space
  obtain ⟨_,_,venue,metadata,_⟩:=wide_after_count X digits publicWide l header o wide m signed fields early cut
  obtain ⟨_,_,unchanged⟩:=DescentDatedSeedStartup.Primitive.any X G op S.copies l.seedWidth Z payload k H g₀ lanes finish hs
    prev sourceSpace space machine live
  have low : ∀u,u < finish → (final) m u=prev u:=fun u h=>unchanged u (.inl h)
  obtain ⟨exec,zero,framed⟩:=complete_any G op X digits publicWide l header payload Z m signed fields early sourceSpace live machine space
  refine ⟨exec,zero,?_,?_,framed⟩
  · apply stageVenue_mono o.source (source_hosts X o wide) (i₀) l.packedLanes l.fieldBits finish (roster X hs) ((final) m) upper
    refine stageVenue_below o.source (source_hosts X o wide) (i₀) l.packedLanes l.fieldBits
      finish (roster X hs) prev ((final) m) venue ?_ low
    intro x j
    obtain ⟨fit,rows⟩:=wire_room (H:=H) (G:=g₀) (d:=k) X l finish topBound cut x.val j.val
    exact (Nat.add_le_add_left rows _).trans fit.2.2
  · intro f x r
    have bound:=(chart).seedFit top f x cut
    have before : ((chart).seedBank top f x).base+(row H g₀ l.operandLanes r).val < finish :=
      (Nat.add_lt_add_left ((row H g₀ l.operandLanes r).isLt.trans_le bound.2) _).trans_le bound.1.2.2
    exact (low _ before).trans (metadata f x r)

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
