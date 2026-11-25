import OAI.Hierarchy.DescentPublicOperandRows
import OAI.Hierarchy.DescentDatedOperandPacketRows
import OAI.Hierarchy.DescentFallbackWindowSources

namespace OAI
/-! The signed input and the two source coordinates read by the original true-trunk query. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
set_option quotPrecheck false
open ProtocolRAM DescentPackedZip DescentSIMDLookup DescentResetPublicOperandBook DescentResetOperandSetup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
local notation "v" => a.successor
local notation "C" => (v).setup
variable (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (active : Expr) (reg : Fin 4→Expr)
local notation "ports" => publicPorts (a:=a) sh floor count hub g Y active reg
local notation "banks" w => menu.banks sh floor count hub g Y w
local notation "base" => (v).operandFloor (a.rebased floor)
local notation "cfg" => publicOperands z roots menu.payload
local notation "idx" => menu.publicInputIndex




variable {H K : ℕ} (values : (publicPorts (a:=a) sh floor count hub g Y active reg).Values H K)
    (digits : (publicPorts (a:=a) sh floor count hub g Y active reg).casts.bits=a.successor.setup.fallbackBits)
variable (x : ℕ) (h : Fin H) (hi : Fin K)
local notation "basic" => (cfg).basic (menu.publicData sh floor count hub g Y active reg values digits x h hi)
local notation "F₀" => (cfg).oldConfig
local notation "n₀" => (v).middle.rotorBits
local notation "slot" i:arg => (finProdFinEquiv.symm i : Fin (F₀).donors×Fin (2*(F₀).oldCap)).1.val

theorem public_fallback_packet (j : DescentFallbackPeriod.Input (F₀).oldDegree (F₀).donors (F₀).oldCap n₀ (F₀).residual) :
    ((F₀).packet basic j).val=
      ((ports).value values x h hi (.packet false (DescentFallbackPeriod.number j).val)).val :=by
  let i:=(F₀).ports n₀ (.inr j)
  have read:=menu.publicData_val sh floor count hub g Y active reg values digits x h hi (Fin.castAdd (cfg).extraCount i)
  rw [Config.port_basic] at read
  unfold DescentFallbackOperandBranch.Config.packet Config.basic
  simpa only [i,Equiv.symm_apply_apply] using read

theorem public_donor_coordinate (i : Fin (F₀).count) (j : Fin 2) :
    ((F₀).digit basic i (j.castLE (by decide : 2≤12))).val=
      ((ports).value values x h hi (.coordinate j.castSucc (slot i))).val :=by
  let coord:=(F₀).ports n₀ (.inl (.inr (j.castLE (by decide : 2≤12),i)))
  have read:=menu.publicData_val sh floor count hub g Y active reg values digits x h hi (Fin.castAdd (cfg).extraCount coord)
  rw [Config.port_basic] at read
  unfold DescentFallbackOperandBranch.Config.digit Config.basic
  fin_cases j <;> simpa [coord] using read

theorem public_fallback_word
    (j : DescentFallbackPeriod.Input (F₀).oldDegree (F₀).donors (F₀).oldCap n₀ (F₀).residual)
    (within : (DescentFallbackPeriod.number j).val<((ports).packets.stage 0 false).fields)
    (block : x<(ports).packets.blocks)
    (wide : ((values.packet false ⟨_,within⟩ ⟨_,block⟩ h hi).val)<2^(ports).casts.bits) :
    ((F₀).packet basic j).val=(values.packet false ⟨_,within⟩ ⟨_,block⟩ h hi).val:=by
  rw [menu.public_fallback_packet sh floor count hub g Y active reg values digits x h hi j]
  simp only [Ports.value,dite_eq_left (And.intro within block),Fin.val_cast_of_lt wide]

theorem public_donor_word (i : Fin (F₀).count) (j : Fin 2)
    (block : x<2^(ports).coordinates.fine) (lo : slot i<2^(ports).coordinates.residual)
    (wide : ((values.coord j.castSucc ⟨x,block⟩ ⟨_,lo⟩ h hi).val)<2^(ports).casts.bits) :
    ((F₀).digit basic i (j.castLE (by decide : 2≤12))).val=
      (values.coord j.castSucc ⟨x,block⟩ ⟨_,lo⟩ h hi).val:=by
  rw [menu.public_donor_coordinate sh floor count hub g Y active reg values digits x h hi i j]
  simp only [Ports.value,dite_eq_left (And.intro block lo),Fin.val_cast_of_lt wide]

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

namespace Hierarchy.DescentFallbackPeriod
open DescentSharedCableNames.Stage DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {H G D L cap n r field : ℕ}
theorem raw_signed_input (own : Fin H→Fin G→Fin L→ℕ) (near : Fin H→Fin D→Option (Fin H))
    (marks : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap))
    (rank : Fin H→Fin (DescentSharedBookScan.width r (2^n) D)→ℕ)
    (h : Fin H) (g : Fin G) (i : Fin L) (j : Fin (2*cap)) (fit : DescentSignedCableCodec.width D cap≤field) :
    signed (inputs (field:=field) own near marks rank h g) i j=marks h g i j:=by
  have small:=(DescentSignedCableCodec.encode (marks h g i j)).isLt.trans_le (Nat.pow_le_pow_right (by decide) fit)
  simp only [signed,inputs,Fin.val_cast_of_lt small,Fin.cast_val_eq_self,DescentSignedCableCodec.decode_encode]

end
end Hierarchy.DescentFallbackPeriod

namespace Hierarchy.DescentOperandRootPull.Pair
set_option quotPrecheck false
open DescentSIMDLookup DescentFallbackPeriod DescentSharedCableNames.Stage
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap n r field H0 G0 H G : ℕ} (device : DescentOperandRootPull.Pair)
    (dims : (device.stage 0 false).fields=inputCount D L cap n r)
    (words : Fin H0→Fin G0→Fin L→ℕ) (near : Fin H0→Fin D→Option (Fin H0))
    (marks : Fin H0→Fin G0→Fin L→Fin (2*cap)→Option (Live D cap))
    (rank : Fin H0→Fin (DescentSharedBookScan.width r (2^n) D)→ℕ)
    (owner : Fin H→Fin H0) (lane : Fin device.blocks→Fin G→Fin G0)
    (matrix : Fin (device.stage 0 true).fields→Fin device.blocks→Fin H→Fin G→Cell field)
    (readable : (s : Bool)→Fin (device.stage 0 s).fields→Fin device.blocks→Fin H→Fin G→Cell field)

local notation "fallback" => fun (j : Fin (device.stage 0 false).fields) x h g=>
  inputs (field:=field) words near marks rank (owner h) (lane x g) (number.symm (j.cast dims))
variable (issued : HEq readable (device.fieldRows (fun j x h g=>
  inputs (field:=field) words near marks rank (owner h) (lane x g) (number.symm (j.cast dims))) matrix))

include issued in
theorem fallback_inputs_at (x : Fin device.blocks) (h : Fin H) (g : Fin G) :
    (fun j=>readable false ((number (n:=n) (r:=r) j).cast dims.symm) x h g)=
      inputs (field:=field) words near marks rank (owner h) (lane x g):=by
  have same : readable=device.fieldRows fallback matrix:=eq_of_heq issued
  funext j
  simp [same,fieldRows]

include issued in
theorem fallback_donor_at (x : Fin device.blocks) (h : Fin H) (g : Fin G) (i : Fin L) (j : Fin (2*cap))
    (s : Bool) (bound : ∀t,words t (lane x g) i+1<2^field) (width : DescentSignedCableCodec.width D cap≤field) :
    let p:=fun k=>readable false ((number (n:=n) (r:=r) k).cast dims.symm) x h g
    localWord p i=words (owner h) (lane x g) i ∧ signed p i j=marks (owner h) (lane x g) i j ∧
      arrival p s i j=(marks (owner h) (lane x g) i j).bind (fun z=>if z.target=s then
        (near (owner h) z.neighbor).map (fun t=>(z.neighbor,words t (lane x g) i)) else none):=by
  dsimp only
  rw [fallback_inputs_at device dims words near marks rank owner lane matrix readable issued x h g]
  exact ⟨own_read words near marks rank _ _ i (Nat.lt_of_succ_lt (bound _)),
    raw_signed_input words near marks rank _ _ i j width,
    arrival_read words near marks rank _ _ s i j bound width⟩

end
end Hierarchy.DescentOperandRootPull.Pair

end OAI
