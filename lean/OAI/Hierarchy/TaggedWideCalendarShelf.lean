import OAI.Hierarchy.TaggedWireTurnPhysical
import OAI.Hierarchy.TaggedWideControlDense
import OAI.Hierarchy.TaggedWideControlBoard

namespace OAI
/-! # The terminal comparator on the dense paid CPU and the public output aperture -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin.Gate
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat Routing
open WireTelescope
open scoped Classical

variable {F : Type*} [Field F] {E Q D : Type} [Fintype E] [Fintype Q] [Fintype D] (G : Gate)
local notation "V" => SitePins E Q D G

/-- A fixed address and bit from the physically installed paid CPU read port.
The high-bit case is the literal zero extension of the native RAM word. -/
def shelfBit (a : ℕ×ℕ) : V⊕Bool :=
  if ha : a.1<G.u then
    if hb : a.2<G.W+1 then .inl (.inr (.inr (.inr (⟨a.1,ha⟩,⟨a.2,hb⟩))))
    else .inr false
  else .inr false

omit [Fintype E] [Fintype Q] [Fintype D] in
theorem shelfBit_read (dense : ∀i : Fin G.u,(G.addr i).val=i.val) (out : Memory G.W)
    (ext : E→Bool) (sel : Q→Bool) (data : D→Bool) (a bit : ℕ) (inside : a<G.u) :
    Sum.elim (Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))) id (G.shelfBit (a,bit)) =
      (out a).val.testBit bit := by
  by_cases low : bit<G.W+1
  · simp only [shelfBit,dite_eq_left inside,dite_eq_left low,Sum.elim_inl,Sum.elim_inr]
    change (out (G.addr ⟨a,inside⟩).val).val.testBit bit=_
    rw [dense]
  · have beyond : G.W≤bit:=by omega
    have bound := (out a).isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2) beyond)
    simp [shelfBit,inside,low,Nat.testBit_lt_two_pow bound]

def shelfNet {sites slots p e : ℕ} (base : ℕ) (s : Fin sites) (lens : TurnShelf.Aperture p e→D⊕Bool) :
    BitNetwork F (Fintype.card V) :=
  TurnShelf.physical (r:=slots) base s G.shelfBit
    (fun d=>Sum.map (fun w : D=>(.inr (.inr (.inl w)) : V)) id (lens d))

theorem shelfNet_cost {sites slots p e : ℕ} (base : ℕ) (s : Fin sites) (lens : TurnShelf.Aperture p e→D⊕Bool) :
    let net:=G.shelfNet (F:=F) (E:=E) (Q:=Q) (slots:=slots) base s lens
    net.cells+net.internal≤ slots*(2308*TurnShelf.width p e*(e+p+2)) :=
  TurnShelf.physical_bill ..

theorem shelf_inside {sites slots : ℕ} (base : ℕ) (s : Fin sites) (t : Fin slots) (f : Fin 5)
    (room : base+5*(sites*slots)≤G.u) : TurnShelf.addr base s t f<G.u := by
  have h₀:=Nat.mul_le_mul_right slots s.isLt
  have h₁:=Nat.mul_le_mul_right (sites*slots) f.isLt
  have h₂:=t.isLt
  unfold TurnShelf.addr
  simp only [Nat.succ_mul,one_mul] at h₀ h₁
  omega

theorem shelfNet_value {sites slots p e : ℕ} (base : ℕ) (s : Fin sites)
    (lens : TurnShelf.Aperture p e→D⊕Bool) (dense : ∀i : Fin G.u,(G.addr i).val=i.val)
    (room : base+5*(sites*slots)≤G.u) (out : Memory G.W) (ext : E→Bool) (sel : Q→Bool) (data : D→Bool) :
    TypedWiring.value (G.shelfNet (F:=F) (slots:=slots) base s lens)
      (Sum.elim ext (Sum.elim sel (Sum.elim data (G.terminal out)))) =
    TypedWiring.value (TurnShelf.network F slots p e) (TurnShelf.nativeView base s out (Sum.elim data id ∘ lens)) := by
  unfold shelfNet
  rw [TurnShelf.physical_value (m:=out)]
  · apply congrArg (TypedWiring.value _)
    apply congrArg (TurnShelf.nativeView base s out)
    funext d
    cases h:lens d <;> simp [h]
  · exact fun t c=>G.shelfBit_read dense out ext sel data _ _ (G.shelf_inside base s t _ room)

end Hierarchy.Tagged.WideControlJoin.Gate

end
end OAI
