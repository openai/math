import OAI.Hierarchy.DescentOriginalPacketComponents

namespace OAI
/-! # Original, possibly narrower, fields in a public operand -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu
open DescentFallbackPeriod DescentRotorWindowArchive DescentSIMDLookup
open DescentResetPublicOperandBook DescentResetOperandSetup DescentPackedZip ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {a : PhysicalReset} {z : a.Atlas} {roots : a.RootInputs} (menu : OperandMenu z roots)
    (sh : a.StencilShape) (floor : ℕ) (bank hub : Bank) (gain Y : ℕ) (active : Expr) (reg : Fin 4→Expr)
local notation "ports" => publicPorts (a:=a) sh floor bank hub gain Y active reg
local notation "cfg" => publicOperands z roots menu.payload
local notation "F₀" => (cfg).oldConfig
local notation "n₀" => a.successor.middle.rotorBits
variable {H K D L cap n r field : ℕ}
    (v : (ports).Values H K) (digits : (ports).casts.bits=a.successor.setup.fallbackBits)
    (x : Fin (ports).packets.blocks) (h : Fin H) (g : Fin K)
    (dD : (cfg).oldDegree=D) (dL : (cfg).donors=L) (dc : (cfg).oldCap=cap)
    (dn : n₀=n) (dr : (cfg).residual=r) (room : field≤(ports).casts.bits)
    (fc : ((ports).packets.stage 0 false).fields=DescentFallbackPeriod.inputCount D L cap n r)
    (mc : ((ports).packets.stage 0 true).fields=count D L cap)
    (fallback : Packet D L cap n r field) (board : RowData D L cap field)
    (localOld : ∀j,board (.inl (.inl j))=fallback (.inl j))
    (signedOld : ∀j,board (.inl (.inr j))=fallback (.inr (.inl j)))
    (fallen : ∀j,(v.packet false ((number j).cast fc.symm) x h g).val=(fallback j).val)
    (traffic : ∀j,(v.packet true ((ix j).cast mc.symm) x h g).val=(board j).val)
local notation "raw" => menu.publicData sh floor bank hub gain Y active reg v digits x.val h g

include localOld signedOld fallen traffic room in
/-- Read the two original row families after expanding their cells to the ROM's field width.
The original packet ordinals survive both the type-index casts and the width change. -/
theorem public_original_fields :
    (∀j : DescentFallbackPeriod.Input (cfg).oldDegree (cfg).donors (cfg).oldCap n₀ (cfg).residual,
      ((F₀).packet ((cfg).basic raw) j).val=
        (fallback (number.symm ((number j).cast (by rw [dD,dL,dc,dn,dr])))).val) ∧
    ∀j : DescentRotorWindowArchive.Input (cfg).oldDegree (cfg).donors (cfg).oldCap,
      ((cfg).oldData raw j).val=(board (ix.symm ((ix j).cast (by rw [dD,dL,dc])))).val:=by
  subst D L cap n r
  simp only [Fin.cast_refl, id_eq, Equiv.symm_apply_apply]
  have limit : 2^field≤2^(ports).casts.bits:=Nat.pow_le_pow_right (by decide) room
  have first (j : DescentFallbackPeriod.Input (cfg).oldDegree (cfg).donors (cfg).oldCap n₀ (cfg).residual) :
      ((F₀).packet ((cfg).basic raw) j).val=(fallback j).val:=by
    exact (menu.public_fallback_word sh floor bank hub gain Y active reg v digits x.val h g j
      ((number j).cast fc.symm).isLt x.isLt ((fallen j).trans_lt ((fallback j).isLt.trans_le limit))).trans (fallen j)
  refine ⟨first,?_⟩
  rintro ((j|j)|q)
  · rw [localOld]
    exact first (.inl j)
  · rw [signedOld]
    exact first (.inr (.inl j))
  · rw [menu.public_matrix_extra sh floor bank hub gain Y active reg v digits x.val h g q]
    have valid : (ix (cap:=(cfg).oldCap) (.inr q)).val < ((ports).packets.stage 0 true).fields :=
      ((ix (cap:=(cfg).oldCap) (.inr q)).cast mc.symm).isLt
    simp only [Ports.value,dite_eq_left (And.intro valid x.isLt),Fin.val_natCast]
    exact (congrArg (fun t : ℕ => t % 2^(ports).casts.bits) (traffic (.inr q))).trans
      (Nat.mod_eq_of_lt ((board (.inr q)).isLt.trans_le limit))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset.OperandMenu

end OAI
