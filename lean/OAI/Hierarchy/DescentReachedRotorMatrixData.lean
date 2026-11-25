import OAI.Hierarchy.DescentPublicRelayPacket
import OAI.Hierarchy.DescentPreparedRotorInputs

namespace OAI
/-! # The full physical matrix read by a public rotor operand -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
set_option quotPrecheck false
open DescentRotorWindowArchive ProtocolRAM DescentPackedZip DescentSIMDLookup DescentResetPublicOperandBook DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "v" => a.successor
local notation "C" => (v).setup
variable (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (active : Expr) (reg : Fin 4→Expr)
local notation "ports" => publicPorts (a:=a) sh floor count hub g Y active reg
local notation:max "banks" w:arg => menu.banks sh floor count hub g Y w
local notation "base" => (v).operandFloor (a.rebased floor)
local notation "cfg" => publicOperands z roots menu.payload
local notation "idx" => menu.publicInputIndex




variable {H K : ℕ} (values : (publicPorts (a:=a) sh floor count hub g Y active reg).Values H K) (digits : (publicPorts (a:=a) sh floor count hub g Y active reg).casts.bits=a.successor.setup.fallbackBits)
variable (x : ℕ) (h : Fin H) (hi : Fin K)
local notation "basic" => (cfg).basic (menu.publicData sh floor count hub g Y active reg values digits x h hi)
local notation "F₀" => (cfg).oldConfig
local notation "n₀" => (v).middle.rotorBits
local notation "slot" i:arg => (finProdFinEquiv.symm i : Fin (F₀).donors×Fin (2*(F₀).oldCap)).1.val

local notation "raw" => menu.publicData sh floor count hub g Y active reg values digits x h hi

/-- The comparison and the six directed reservation fields come from the
matrix half of the reached root entry, in the original rotor input order. -/
theorem public_matrix_extra (e : (cfg).Extra) :
    ((cfg).oldData raw (.inr e)).val=
      ((ports).value values x h hi (.packet true (ix (cap:=(F₀).oldCap) (.inr e)).val)).val:=by
  let j:=(cfg).extraId e
  have read:=menu.publicData_val sh floor count hub g Y active reg values digits x h hi (Fin.natAdd ((F₀).inputs n₀) j)
  rw [Config.port_extra] at read
  exact read

/-- All matrix words have now been accounted for: the two old portions use
the original fallback packet and the remaining portion uses the sibling
matrix packet for the exact same actor and residual group. -/
theorem public_matrix_pair
    (fallback : DescentFallbackPeriod.Packet (F₀).oldDegree (F₀).donors (F₀).oldCap n₀ (F₀).residual (cfg).fieldBits)
    (order_ : Fin (F₀).donors→Fin (F₀).donors→Bool)
    (quota : Fin (F₀).oldDegree→Fin (F₀).oldDegree→Fin 6→Cell (cfg).fieldBits)
    (fall : ∀j,((ports).value values x h hi (.packet false (DescentFallbackPeriod.number j).val)).val=(fallback j).val)
    (matrix : ∀e : (cfg).Extra,((ports).value values x h hi (.packet true (ix (cap:=(F₀).oldCap) (.inr e)).val)).val=
      (observed fallback order_ quota (.inr e)).val) :
    (cfg).oldData raw=observed fallback order_ quota:=by
  funext j
  apply Fin.ext
  rcases j with (i|i)|e
  · exact (menu.public_fallback_packet sh floor count hub g Y active reg values digits x h hi (.inl i)).trans (fall (.inl i))
  · exact (menu.public_fallback_packet sh floor count hub g Y active reg values digits x h hi (.inr (.inl i))).trans
      (fall (.inr (.inl i)))
  · exact (menu.public_matrix_extra sh floor count hub g Y active reg values digits x h hi e).trans (matrix e)

variable {Ho Go : ℕ}
    (own : Fin Ho→Fin Go→Fin (publicOperands z roots menu.payload).oldConfig.donors→ℕ) (near : Fin Ho→Fin (publicOperands z roots menu.payload).oldConfig.oldDegree→Option (Fin Ho))
    (marks : Fin Ho→Fin Go→Fin (publicOperands z roots menu.payload).oldConfig.donors→Fin (2*(publicOperands z roots menu.payload).oldConfig.oldCap)→Option (DescentSharedCableNames.Stage.Live (publicOperands z roots menu.payload).oldConfig.oldDegree (publicOperands z roots menu.payload).oldConfig.oldCap))
    (rank : Fin Ho→Fin (DescentSharedBookScan.width (publicOperands z roots menu.payload).oldConfig.residual (2^a.successor.middle.rotorBits) (publicOperands z roots menu.payload).oldConfig.oldDegree)→ℕ)
    (comparison : Fin Ho→Fin Go→Fin (publicOperands z roots menu.payload).oldConfig.donors→Fin (publicOperands z roots menu.payload).oldConfig.donors→Bool)
    (reserved : Fin Ho→Fin (publicOperands z roots menu.payload).oldConfig.oldDegree→Fin (publicOperands z roots menu.payload).oldConfig.oldDegree→Fin 6→Cell (publicOperands z roots menu.payload).fieldBits)
    (owner : Fin Ho) (lane : Fin Go)
local notation "fromFallback" => DescentFallbackPeriod.inputs (field:=(cfg).fieldBits) own near marks rank owner lane
local notation "fromMatrix" => DescentFallbackPeriod.Projected.RootSources.paddedRow (n:=n₀) (r:=(F₀).residual)
      own near marks rank comparison reserved owner lane

/-- The two actual field pages recover the entire measured original padded
board, without any assumption on the occupancy of a scheduled rotor slot. -/
theorem public_reached_matrix
    (block : x<(ports).packets.blocks)
    (rooms : ∀j:DescentFallbackPeriod.Input (F₀).oldDegree (F₀).donors (F₀).oldCap n₀ (F₀).residual,
      (DescentFallbackPeriod.number j).val<((ports).packets.stage 0 false).fields)
    (wide : ∀e:(cfg).Extra,(ix (cap:=(F₀).oldCap) (.inr e)).val<((ports).packets.stage 0 true).fields)
    (fallen : ∀j,((values).packet false ⟨(DescentFallbackPeriod.number j).val,rooms j⟩ ⟨x,block⟩ h hi).val=(fromFallback j).val)
    (traffic : ∀e:(cfg).Extra,((values).packet true ⟨(ix (cap:=(F₀).oldCap) (.inr e)).val,wide e⟩ ⟨x,block⟩ h hi).val=
       (fromMatrix (ix (.inr e))).val) :
    ∀j,((cfg).oldData raw j).val=(fromMatrix (ix j)).val:=by
  have fieldWidth : (cfg).fieldBits = (C).rotorBits := rfl
  have fall j:=menu.public_fallback_word sh floor count hub g Y active reg values digits x h hi j (rooms j) block
    (by rw [fallen];simpa only [digits,menu.wordSize,fieldWidth] using (fromFallback j).isLt)
  have main : (cfg).oldData raw=observed fromFallback (comparison owner lane) (reserved owner):=by
    apply menu.public_matrix_pair sh floor count hub g Y active reg values digits x h hi
    · intro j
      exact (menu.public_fallback_packet sh floor count hub g Y active reg values digits x h hi j).symm.trans ((fall j).trans (fallen j))
    · intro e
      have yes:=traffic e
      have fit : ((values).packet true ⟨_,wide e⟩ ⟨x,block⟩ h hi).val<2^(ports).casts.bits:=by
        rw [yes]
        simpa only [digits,menu.wordSize,fieldWidth] using (fromMatrix (ix (.inr e))).isLt
      simpa only [Ports.value,dite_eq_left (And.intro (wide e) block),Fin.val_natCast,Nat.mod_eq_of_lt fit,
        DescentFallbackPeriod.Projected.RootSources.paddedRow,Equiv.symm_apply_apply] using yes
  intro j
  rw [main]
  simp only [DescentFallbackPeriod.Projected.RootSources.paddedRow,Equiv.symm_apply_apply]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
