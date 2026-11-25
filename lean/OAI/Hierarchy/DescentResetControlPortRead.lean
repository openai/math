import OAI.Hierarchy.DescentResetControlRegisterReceipt

namespace OAI
namespace Hierarchy.DescentResetControlRegisters.Chart
open DescentSIMDLookup DescentPackedZip DescentVenueQuantityPlanes ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (c : Chart) (base : ℕ) {w : ℕ}
local notation "p" => c.dims
local notation "M" => c.dims.lanes
local notation "H" => c.dims.hosts
local notation "G" => c.dims.groups
local notation "S" => c.dims.shapes
local notation "rows" => H*chunks G M
local notation "raw" => c.dims.oldHosts*S

private theorem bank_base (b n : ℕ) : (bank b n).base = b := rfl

theorem host_read (m : Memory w) (keep : c.Resident base m) (roof : c.endAddress base<2^w)
    (inverse : Bank) (cap : inverse.Fits w (c.endAddress base)) (j : Row H G M) (h : j.1.val< inverse.size) :
    (c.hostId base inverse).eval m ((row H G M j).val:Word w)=m (inverse.base+j.1.val):=by
  let i:=row H G M j
  have pos:0<chunks G M:=Nat.zero_lt_of_lt j.2.isLt
  have host:i.val/chunks G M=j.1.val:=by
    change (j.2.val + chunks G M * j.1.val) / chunks G M = _
    rw [Nat.add_mul_div_left _ _ pos,Nat.div_eq_of_lt j.2.isLt,Nat.zero_add]
  change inverse.read m ((bank (c.first base) rows).read m (i.val:Word w))=_
  rw [bank_read _ m (i.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)) (c.sections base roof).1,bank_base,
     (c.lookups base keep).1 i.val i.isLt,host,bank_read _ m h cap]

theorem ports_read (m : Memory w) (keep : c.Resident base m) (roof : c.endAddress base<2^w)
    (x cap : ℕ) (inverse depth levels : Bank) (j : Row H G M) (mask : Cell (1*M))
    (used : (c.active base x).eval m ((row H G M j).val:Word w)=(mask.val:Word w))
    (h : Fin raw) (rawAt : (c.hostId base inverse).eval m ((row H G M j).val:Word w)=(h.val:Word w))
    (d level : ℕ) (old : h.val/S<depth.size) (atDepth : m (depth.base+h.val/S)=(d:Word w))
    (fitsD : depth.Fits w (c.endAddress base)) (fitsL : levels.Fits w (c.endAddress base))
    (available : d<levels.size) (atLevel : m (levels.base+d)=(level:Word w))
    (localRoom : ∀t∈[1,cap,level,h.val%S],t<2^c.bits) :
    (c.live base x).eval m ((row H G M j).val:Word w)=((c.withMask mask 1).val:Word w) ∧
    ∀i : Fin 4,(c.ports base cap x inverse depth levels i).eval m ((row H G M j).val:Word w)=
      ((c.withMask mask (![cap,level,0,h.val%S] i)).val:Word w):=by
  let pos:Word w:=(row H G M j).val
  have fit:=c.sections base roof
  have seen:=c.lookups base keep
  have amt (z : ℕ) (hz : z<2^c.bits) (e : Expr) (read : e.eval m pos=(z:Word w)) :
      (c.broadcast base x e).eval m pos=((c.withMask mask z).val:Word w):=by
    have addr:2^c.bits<2^w:=fit.2.2.2.1.2.1
    simpa only [read,Fin.val_cast_of_lt (hz.trans addr),Nat.mod_eq_of_lt hz] using
      c.broadcast_read base m keep roof x e pos mask used
  have qRoom : h.val<span raw:=h.isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)
  refine ⟨amt 1 (localRoom _ (by simp)) (.lit 1) rfl,?_⟩
  intro i
  fin_cases i
  · exact amt cap (localRoom _ (by simp)) (.lit cap) rfl
  · apply amt level (localRoom _ (by simp))
    change levels.read m (depth.read m ((bank (c.oldHost base) raw).read m ((c.hostId base inverse).eval m pos)))=_
    rw [rawAt,bank_read _ m qRoom fit.2.1,bank_base,seen.2.1 _ h.isLt,bank_read _ m old fitsD,atDepth,
      bank_read _ m available fitsL,atLevel]
  · change (0:Word w)=((c.withMask mask 0).val:Word w)
    simp [withMask, encode]
  · apply amt (h.val%S) (localRoom _ (by simp))
    change (bank (c.shape base) raw).read m ((c.hostId base inverse).eval m pos)=_
    rw [rawAt,bank_read _ m qRoom fit.2.2.1,bank_base,seen.2.2.1 _ h.isLt]

end
end Hierarchy.DescentResetControlRegisters.Chart

end OAI
