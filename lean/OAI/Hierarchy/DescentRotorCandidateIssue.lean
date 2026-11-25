import OAI.Hierarchy.DescentInstalledRotorCandidate
import OAI.Hierarchy.DescentRotorStencilMode
import OAI.Hierarchy.DescentIssuedGoodHeaders

namespace OAI
/-! # Short per-operation cable candidates from the actual reset's prior fields -/
namespace Hierarchy.DescentRotorCandidateIssue
open DescentSIMDLookup DescentPackedFallbackTree.Image DescentPackedZip DescentIssuedGoodHeaders
open DescentRotorOperandTicket DescentResetLocalRoster DescentResetHostSize DescentSharedCableNames
open DescentPacking.PackedMatch.Local.Gather
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {n h r H G w field M : ℕ} (board : NonlinearExpanders.Graph n h)
local notation "Q" => DescentCommonPalette.rotor board

def bound (Ht r Y : ℕ) := 2*(rootSlots r Y*max (Fintype.card (Q).Edge) (2^(Ht+1)))

/-- The extra zero code is an absent operand. The payload is relative to one receiver's
    private sector. Capacity is read from the preceding stage as in its actual gate-role program. -/
def panel (Ht packet f m stop : ℕ) (side : Bool) (root : Code r) (e : (Q).Edge) (x : Fin 3→Cell field) :
    Cell (Packed.bits (bound board Ht r (2^n))*stop) :=
  encode _ stop fun j=>
    if (x 1).val=root.val.1+1 ∧ (x 2).val%2=0 ∧ j.val<DescentRecordedRotorLayers.layers n packet f (x 0).val*m then
      Packed.token (some (candidate board Ht r (2^n) side root e))
    else 0

theorem present (Ht packet f m stop : ℕ) (side : Bool) (root : Code r) (e : (Q).Edge) (x : Fin 3→Cell field)
    (hit : (x 1).val=root.val.1+1 ∧ (x 2).val%2=0) (realLayers : ℕ)
    (height : realLayers=DescentRecordedRotorLayers.layers n packet f (x 0).val)
    (layer : Fin realLayers) (batch : Fin m) (room : layer.val*m+batch.val<stop) :
    digit (Packed.bits (bound board Ht r (2^n))) (layer.val*m+batch.val)
      (panel board Ht packet f m stop side root e x).val=(candidate board Ht r (2^n) side root e).val+1 := by
  let rowId : Fin stop:=⟨_,room⟩
  have live : rowId.val<realLayers*m:=by
    change layer.val*m+batch.val<realLayers*m
    calc _<layer.val*m+m:=Nat.add_lt_add_left batch.isLt _
         _=(layer.val+1)*m:=by rw [Nat.add_mul,Nat.one_mul]
         _≤_:=Nat.mul_le_mul_right m layer.isLt
  change digit _ rowId.val _=_
  rw [panel,digit_encode,ite_eq_left ⟨hit.1,hit.2,height ▸ live⟩]
  rfl

theorem absent (Ht packet f m stop : ℕ) (side : Bool) (root : Code r) (e : (Q).Edge) (x : Fin 3→Cell field)
    (j : Fin stop) (absent : ¬((x 1).val=root.val.1+1 ∧ (x 2).val%2=0 ∧ j.val<DescentRecordedRotorLayers.layers n packet f (x 0).val*m)) :
    digit (Packed.bits (bound board Ht r (2^n))) j.val (panel board Ht packet f m stop side root e x).val=0 := by
  rw [panel,digit_encode,ite_eq_right absent]
  rfl

/-- Each gate/short operand kind uses a fixed rotor template edge, with one numerical
    source per physical candidate. The data gathering spans exactly three prior banks. -/
theorem issued (Ht packet f m stop : ℕ) (side : Bool) (root : Code r) (e : (Q).Edge)
    (tables : Fin 3→Tables) (reads : Fin 3→Expr) (menu : DescentSIMDLookup.Banks) (mid out : ℕ)
    (x : Fin H→Fin G→Fin 3→Cell field) (pos : 0<M)
    (mem : Memory w) (bounds : Bounds (w:=w) (d:=field) (M:=M) tables reads mid)
    (constants : ∀j,Static (tables j) (setField (d:=field) j) M mem)
    (source : ∀j,Source (reads j) (fun a g=>x a g j) M mem) (room : mid+H*chunks G M<2^w)
    (fit : DescentSIMDLookup.Fits menu (field*3) (Packed.bits (bound board Ht r (2^n))*stop) M H G w out)
    (rom : resident (panel board Ht packet f m stop side root e ∘ (encode field 3).symm) menu H G M mem)
    (dictLow : menu.dictionary.base+2^((field*3)*M)≤ mid) (maskLow : menu.mask.base+H*chunks G M≤ mid)
    (wire : menu.source.base=mid) :
    let act:=assembly tables reads
    let rows:=H*chunks G M
    let dst:=imageBank H G M out menu (image mid rows act mem)
    ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w)).Exec mem dst
      ((4+rows*(2*act.work+4))+(4+44*rows)) ∧
    (∀a g,digit (Packed.bits (bound board Ht r (2^n))*stop) (lane g pos).val
      (dst (out+(row H G M (position a g pos)).val)).val=(panel board Ht packet f m stop side root e (x a g)).val) ∧
    ∀addr,(addr< mid ∨ mid+rows≤addr)→(addr<out ∨ out+rows≤addr)→dst addr=mem addr :=
  gathered _ tables reads menu mid out x pos mem bounds constants source room fit rom dictLow maskLow wire

end
end Hierarchy.DescentRotorCandidateIssue

end OAI
