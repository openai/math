import OAI.Hierarchy.DescentOverlapTables

namespace OAI
/-! # The shared physical pages for changing a venue's packed lane width -/
namespace Hierarchy.DescentVenueSlabs
open DescentSIMDLookup ProtocolRAM
noncomputable section

structure Shape where
  pages : ℕ
  hosts : ℕ
  groups : ℕ
  sourceLanes : ℕ
  targetLanes : ℕ
  bits : ℕ

variable (s : Shape)
local notation "n₀" => s.hosts*chunks s.groups s.sourceLanes
local notation "n₁" => s.hosts*chunks s.groups s.targetLanes
local notation "Q" => s.pages
local notation "V" => s.pages*s.hosts
def span (n:ℕ) :=2^Nat.clog 2 n
def gathered (base:ℕ):Bank:=⟨base,Nat.clog 2 (Q*n₀)⟩
def work (base:ℕ):=base+span (Q*n₀)
def page (base j:ℕ):Bank:=
  ⟨(Overlap.outputBank (work s base) V s.groups s.sourceLanes s.targetLanes s.bits).base+j*n₁,Nat.clog 2 n₁⟩
def endAddress (base:ℕ) :=
  Overlap.endAddress (work s base) V s.groups s.sourceLanes s.targetLanes s.bits +span n₁

theorem translates (base:ℕ) : endAddress s base=base+endAddress s 0:=by
  simp only [endAddress,Overlap.endAddress,Overlap.dest,Overlap.dictBase,work,Nat.zero_add,Nat.add_assoc]

end
end Hierarchy.DescentVenueSlabs

end OAI
