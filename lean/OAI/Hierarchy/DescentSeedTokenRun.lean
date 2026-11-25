import OAI.Hierarchy.DescentSeedTokenProgram
import OAI.Hierarchy.DescentSeedTokenSourceRun

namespace OAI
/-! # Executing the original ballot census and publishing the first global role field -/
namespace Hierarchy.DescentDatedSeedStartup.Primitive
open DescentInitialHost DescentSeedRoot DescentPackedSeed DescentSIMDLookup
open DescentPrimitivePalette DescentCompiler DescentSixParty DescentSeedTokenTransposition
open DescentDyadicSpan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Catalyst
open ThreeFlat.RAM.PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {c p : ℕ} (X : Approximation F c p)
variable (D : PoweredGadget F) (op : RotorSpec) (R s Z payload k H G M base : ℕ)
local notation "O" => Fintype.card (Old X)
local notation "A" => DescentPackedSeed.Primitive.pieces payload s
local notation "a" => DescentPackedSeed.Primitive.roleBits s
local notation "b" => printedBits D s Z op
local notation "old" => DescentPackedSeed.Primitive.Source.bank X R s payload base
local notation "splitAt" => DescentPackedSeed.Primitive.Source.finish X R s payload base
local notation "nr" => DescentPackedSeed.Primitive.Source.jobs X R s payload

variable (host : Vertex X↪Fin H)
local notation "choose" => select X H host
local notation "unit" => hub D op s Z
local notation "afterProgram" => DescentSeedTokenTransposition.program splitAt O H G (2^k) a A M old choose unit
local notation "afterClock" => DescentSeedTokenTransposition.ticks splitAt O H G (2^k) a A M old choose unit
local notation "afterImage" => DescentSeedTokenTransposition.image splitAt O H G (2^k) a A M old choose unit
local notation "addr" => initialEnd X R s payload k H G M base

theorem any {w : ℕ} (m : Memory w) (prior : publicWords X+span nr ≤ base) (space : addr < 2^w)
    (native : payload ≤ w) (lanesLive : 0 < M) :
    (program X D op R s Z payload k H G M base host w).Exec m (image X D op R s Z payload k H G M base host m)
      (ticks X D op R s Z payload k H G M base host w) ∧
    CheapCode (program X D op R s Z payload k H G M base host w) ∧
      ∀u,u < base ∨ addr ≤ u → image X D op R s Z payload k H G M base host m u=m u :=by
  obtain ⟨firstBase,firstEnd⟩:=fences X R s payload k H G M base
  obtain ⟨one,small,kept⟩:=DescentPackedSeed.Primitive.Source.execute X R s payload w base m prior (firstEnd.trans_lt space) native
  have fit:=(DescentPackedSeed.Primitive.Source.raw_fit X R s payload w base (firstEnd.trans_lt space)).1
  obtain ⟨two,saved,cheap⟩:=DescentSeedTokenTransposition.any splitAt O H G (2^k) a A M old choose unit
    (DescentPackedSeed.Primitive.Source.image X R s payload w base m) lanesLive (Nat.two_pow_pos _) fit space
  refine ⟨?_,@cheap_seq w _ _ (@small) (@cheap),?_⟩
  · intro nPc nRegisters nPublic machine pc reg slot exit code advice cfg ini entry mm
    exact Procedure.Exec.then one two machine pc reg slot exit code advice cfg ini entry mm
  · rintro u (lo|hi)
    · exact (saved _ (.inl (lo.trans_le firstBase))).trans (kept _ (.inl lo))
    · exact (saved _ (.inr hi)).trans (kept _ (.inr (firstEnd.trans hi)))

end
end Hierarchy.DescentDatedSeedStartup.Primitive

end OAI
