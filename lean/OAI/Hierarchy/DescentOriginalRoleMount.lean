import OAI.Hierarchy.DescentOriginalRoleWordBits
import OAI.Hierarchy.DescentTerminalRoleInstallation
import OAI.Hierarchy.DescentPrimitivePaletteToken

namespace OAI
/-! # Installed role and arity dictionaries for the original public terminal register -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler Chronology DescentPrimitivePalette DescentTerminalRoleTables
open DescentTerminalCombinedRole DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
noncomputable section
set_option quotPrecheck false
variable {F:Type} [Field F] (G:PoweredGadget F) (op:RotorSpec) (S:AtomSchedule)
    (p drift base roof:ℕ) {w:ℕ}
local notation "paletteSize" => DescentPrimitivePalette.colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op
local notation "bits" => originalRoleBits G op S p drift
local notation "codec₀" => DescentPrimitivePalette.codec (G:=G) (s:=S.firstWidth G.b p) (Z:=S.grainAt G.b p 0) op
local notation "cap" => NativeBranch.privateSlotCapacity G S drift
local notation "nodes" => S.epochPower^S.localTokenExponent
local notation "A₀" => max 8 (2^S.capGain)
local notation "groups₀" => S.groupCount S.length
variable (endAt:base+DescentTerminalRoleTables.count (originalRoleBits G op S p drift)≤roof) (room:roof<2^w)
local notation "data" => DescentTerminalRoleTables.literal (n:=paletteSize) (A:=A₀) (G:=cap) (p:=p)
  (R:=drift) (N:=nodes) (groups:=groups₀) codec₀ cap

def originalRoleMount : RoleMount w base roof where
  phase := ⟨DescentStaticWordColumn.program w base data (count bits),4+10*count bits,
    fun m=>DescentStaticWordColumn.image base data m (count bits),
    @DescentStaticWordColumn.cheap w base data (count bits)⟩
  run m := DescentStaticWordColumn.mount base (count bits) data m (endAt.trans_lt room)
  frame m j clear := DescentStaticWordColumn.frame base (count bits) data m j
    (clear.imp_right (fun top=>endAt.trans top))
  placed := (Nat.le_add_right ..).trans endAt

local notation "issued₀" => originalRoleMount G op S p drift base roof endAt room

theorem original_role_tariff :
    ((issued₀).phase.ticks+7*DescentStaticWordColumn.names (issued₀).phase.program)*w=
      (109+115*count bits)*w :=by
  change (4+10*count bits+7*DescentStaticWordColumn.names
    (DescentStaticWordColumn.program w base data (count bits)))*w=_
  rw [DescentStaticWordColumn.names_mount]
  ring

theorem original_role_static (input:Fin 6→Bank) (m:Memory w) :
    Static (A:=A₀) (G:=cap) (p:=p) (R:=drift) (N:=nodes) (M:=groups₀) codec₀
      (DescentTerminalRoleTables.role bits input base) ((issued₀).phase.image m) ∧
    CountStatic (n:=DescentPrimitivePalette.colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
      (A:=A₀) (G:=cap) (p:=p) (R:=drift) (N:=nodes) (M:=groups₀) cap
      (DescentTerminalRoleTables.arity bits input base) ((issued₀).phase.image m) :=by
  have space:=endAt.trans_lt room
  have got:=DescentTerminalRoleTables.mounted (n:=paletteSize) (wb:=w) (A:=A₀) (G:=cap)
    (p:=p) (R:=drift) (N:=nodes) (groups:=groups₀) codec₀ cap input base m space
  exact ⟨got.2.2.1,got.2.2.2.1⟩

theorem original_role_after_replay (input:Fin 6→Bank) (m later:Memory w)
    (retained:∀a<roof,later a=(issued₀).phase.image m a) :
    Static (A:=A₀) (G:=cap) (p:=p) (R:=drift) (N:=nodes) (M:=groups₀) codec₀
      (DescentTerminalRoleTables.role bits input base) later ∧
    CountStatic (n:=DescentPrimitivePalette.colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
      (A:=A₀) (G:=cap) (p:=p) (R:=drift) (N:=nodes) (M:=groups₀) cap
      (DescentTerminalRoleTables.arity bits input base) later :=by
  have space:=endAt.trans_lt room
  exact DescentTerminalRoleTables.persistent (n:=paletteSize) (wb:=w) (A:=A₀) (G:=cap) (p:=p)
    (R:=drift) (N:=nodes) (groups:=groups₀) codec₀ cap input base m space later
    (fun a _ upper=>retained a (upper.trans_le endAt))

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
