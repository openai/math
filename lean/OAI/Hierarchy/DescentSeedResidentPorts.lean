import OAI.Hierarchy.DescentSeedRegisterLayout
import OAI.Hierarchy.DescentSeedNativeStartup
import OAI.Hierarchy.DescentSeedRosterAccess
import OAI.Hierarchy.DescentDatedOperandHeader

namespace OAI
/-! # The actual address arguments of the first ordinary matcher -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentSeedRoot DescentPackedSeed DescentInitialHost DescentColonies DescentSIMDLookup
open DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM Catalyst DescentOperandStateBanks
open DescentPacking.PackedMatch.Local.Stage
open scoped Classical Fin.CommRing
noncomputable section
variable {F J : Type} [Field F] [Fintype J] [DecidableEq J] {k p R d G H w : ℕ}
    (X : Approximation F k p) (name : J≃Fin G) (digits : Fin R≃J×Block d) (host : Vertex X↪Fin H) (l : Layout)
local notation "M" => l.packedLanes
local notation "db" => directoryBase X l H G d
local notation "top" => endAddress X l H G d
local notation "bank" => DescentSeedInitialTable.bank db H G M 3
local notation "final" => output X name digits host l


local notation "P" => operands X l d H G

omit [_root_.Field F] in
theorem initial_access (floor : ℕ) (later : top≤ floor) (room : floor<2^w) :
    Accessible ((P).ports 3) (P).actors H G M w floor :=
  DescentSeedInitialTable.accessible db H G M 3 w floor later room

omit [Fintype J] [DecidableEq J] in
theorem initial_mounted (m : Memory w) :
    Mounted ((P).ports 3) (DescentSeedInitialTable.roster X host) (final m) G M :=
  directory X name digits host l m

omit [_root_.Field F] in
theorem wire_room (floor : ℕ) (later : top≤ floor) (room : floor<2^w) (x j : ℕ) :
    ((P).wire x j).Fits w floor ∧ H*chunks G M≤((P).wire x j).size := by
  let r:=H*chunks G M
  let pad:=DescentSeedInitialTable.stride H G M 3
  have cap : 2^Nat.clog 2 r≤ pad := by
    exact Nat.pow_le_pow_right (by decide) (Nat.clog_mono_right _ ((le_max_right _ _).trans (le_max_right _ _)))
  have natural : r≤2^Nat.clog 2 r := Nat.le_pow_clog (by decide) _
  let key:=j%512
  have keyLt : key<512:=Nat.mod_lt _ (by decide)
  have small:=Nat.mul_le_mul_right r keyLt.le
  have finish : Signed.Plane.output X l.base H G M+512*r≤ db := by
    have stage:=(fences X l H G d).2.1
    change Signed.Plane.output X l.base H G M+(512*H)*chunks G M≤ db at stage
    rw [Nat.mul_assoc] at stage
    exact stage
  have tail : db+11*pad≤ floor:=later
  change (0<2^Nat.clog 2 r ∧ 2^Nat.clog 2 r<2^w ∧
      Signed.Plane.output X l.base H G M+key*r+2^Nat.clog 2 r≤ floor) ∧ r≤2^Nat.clog 2 r
  exact ⟨⟨Nat.two_pow_pos _,by omega,by omega⟩,natural⟩

omit [Fintype J] [DecidableEq J] in
theorem static_census (m : Memory w) (floor : ℕ) (later : top≤ floor) (room : floor<2^w) :
    (P).hubs.Fits w floor ∧ H≤(P).hubs.size ∧
    (∀x,((P).atoms x).Fits w floor) ∧
    (∀x,DescentPackedZip.Source ((P).atoms x) (fun h (_ : Fin G)=>
      (((DescentSeedInitialTable.rack X host h).elim (0 : ℕ) (DescentSeedInitialTable.records X) : ℕ) : Cell l.fieldBits)) M (final m)) := by
  have rb (c : ℕ) (hc : c<3+8) : (bank c).Fits w floor := by
    have small:=DescentSeedInitialTable.bank_fits hc (later.trans_lt room)
    exact ⟨small.1,small.2.1,small.2.2.trans later⟩
  have capacity:=DescentSeedInitialTable.capacities H G M 3
  refine ⟨rb 4 (by decide),capacity.1,fun _=>?_,fun _=>?_⟩
  · exact ⟨rb 5 (by decide),trivial⟩
  · exact DescentPackedZip.source_column (bank 5) floor (rb 5 (by decide)) _ _ capacity.2.2
      (DescentSeedInitialTable.atoms X host db d l.wire l.history l.seedWidth l.fieldBits _)

end
end Hierarchy.DescentDatedSeedStartup

end OAI
