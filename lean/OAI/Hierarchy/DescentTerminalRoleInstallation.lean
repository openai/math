import OAI.Hierarchy.DescentTerminalRoleTableMount
import OAI.Hierarchy.DescentRoleMountSpan
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! The charged native role and arity dictionaries as the first terminal replay phase. -/
namespace Hierarchy.DescentTerminalRoleTables
open DescentTerminalVertexFields DescentEpochTagKeys DescentTerminalCombinedRole DescentSIMDLookup ProtocolRAM
open DescentSixParty.Chronology Computability.VPVNP.BurstRAM
noncomputable section

variable {U : Type} {n A G p R N groups : ℕ} (old : Codec U n) (slots : ℕ)
local notation "field" => fun f:Fin 6=>width n A G p R f*N*groups
local notation "data" => literal (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (groups:=groups) old slots

def phase (bw base : ℕ) : NativePhase bw :=
  ⟨DescentStaticWordColumn.program bw base data (count field),4+10*count field,
    fun m=>DescentStaticWordColumn.image base data m (count field),@DescentStaticWordColumn.cheap bw base data (count field)⟩

variable {bw : ℕ} (base : ℕ) (space : base+count (fun f:Fin 6=>DescentTerminalCombinedRole.width n A G p R f*N*groups)<2^bw)
local notation "mountedPhase" => phase (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (groups:=groups) old slots bw base

include space in
theorem issue (m : Memory bw) :
    (mountedPhase).Runs m ∧ ∀j,j<base ∨ base+count field ≤ j→(mountedPhase).image m j=m j :=
  ⟨DescentStaticWordColumn.mount base (count field) data m space,DescentStaticWordColumn.frame base (count field) data m⟩

def installation : RoleMount bw base (base+count field) where
  phase := mountedPhase
  run m := (issue (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (groups:=groups) old slots base space m).1
  frame m := (issue (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (groups:=groups) old slots base space m).2
  placed := Nat.le_add_right ..

local notation "mount_" => installation (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (groups:=groups) old slots base space
theorem installation_static (input : Fin 6→Bank) (m : Memory bw) :
    Static (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) old (role field input base) ((mount_).phase.image m) ∧
    CountStatic (n:=n) (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (M:=groups) slots (arity field input base)
      ((mount_).phase.image m) :=by
  have placed := mounted (A:=A) (G:=G) (p:=p) (R:=R) (N:=N) (groups:=groups) old slots input base m space
  exact ⟨placed.2.2.1,placed.2.2.2.1⟩

theorem installation_tariff :
    ((mount_).phase.ticks+7*DescentStaticWordColumn.names (mount_).phase.program)*bw=(109+115*count field)*bw :=by
  change (4+10*count field+7*DescentStaticWordColumn.names (DescentStaticWordColumn.program bw base data (count field)))*bw=_
  rw [DescentStaticWordColumn.names_mount]
  ring

end
end Hierarchy.DescentTerminalRoleTables

end OAI
