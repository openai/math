import OAI.Hierarchy.DescentSeedHeaderFloorNumbers
import OAI.Hierarchy.DescentSeedPrintedPitch
import OAI.Hierarchy.DescentSeedTokenSourceProgram
import OAI.Hierarchy.DescentSeedTokenTransposition
import OAI.Hierarchy.DescentSeedSiteGeometry
import OAI.Hierarchy.DescentPrimitivePaletteToken

namespace OAI
/-! # First global primitive role page, native program and word costs -/
namespace Hierarchy.DescentDatedSeedStartup.Primitive
open DescentInitialHost DescentSeedRoot DescentPackedSeed DescentSIMDLookup
open DescentPrimitivePalette DescentCompiler DescentSixParty DescentSeedTokenTransposition
open DescentDyadicSpan ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Catalyst
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

def page := DescentSeedTokenTransposition.page splitAt O H G (2^k) a A M
def select (host : Vertex X↪Fin H) (h : Fin H) : Option (Option (Fin O)) :=
  (DescentSeedInitialTable.rack X host h).map
    (Sum.elim (fun v : Old X => some ((Fintype.equivFin (Old X)) v)) (fun _=>none))
def hub : Cell b := token D s Z op (.inl (.inr ()))

variable (host : Vertex X↪Fin H)
local notation "choose" => select X H host
local notation "unit" => hub D op s Z
local notation "afterProgram" => DescentSeedTokenTransposition.program splitAt O H G (2^k) a A M old choose unit
local notation "afterClock" => DescentSeedTokenTransposition.ticks splitAt O H G (2^k) a A M old choose unit
local notation "afterImage" => DescentSeedTokenTransposition.image splitAt O H G (2^k) a A M old choose unit
local notation "addr" => initialEnd X R s payload k H G M base

def program (w : ℕ) := (DescentPackedSeed.Primitive.Source.program X R s payload w base).seq ((afterProgram) w)
def ticks (w : ℕ) := DescentPackedSeed.Primitive.Source.clock X R s payload base+(afterClock) w
def image {w : ℕ} (m : Memory w) := (afterImage) (DescentPackedSeed.Primitive.Source.image X R s payload w base m)

omit [Field F] in
theorem page_ready {w : ℕ} (x : Fin (2^k)) (space : addr < 2^w) :
    (page X R s payload k H G M base x).Fits w addr ∧ H*chunks G M≤(page X R s payload k H G M base x).size :=
  DescentSeedTokenTransposition.page_ready splitAt O H G (2^k) a A M x space

omit [Field F] in
theorem fences : base ≤ splitAt ∧ splitAt ≤ addr :=by
  have one : base ≤ splitAt :=by unfold DescentPackedSeed.Primitive.Source.finish DescentPackedSeed.Primitive.Source.raw;omega
  obtain ⟨l,r,u⟩:=DescentSeedTokenTransposition.addresses splitAt O H G (2^k) a A M
  exact ⟨one,l.trans (r.trans ((Nat.le_add_right ..).trans u))⟩

end
end Hierarchy.DescentDatedSeedStartup.Primitive

end OAI
