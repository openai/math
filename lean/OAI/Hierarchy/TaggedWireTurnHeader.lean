import OAI.Hierarchy.TaggedWireTurnShelf
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # Ordinary circuit pins for the actual five field-major RAM words -/
noncomputable section
namespace Hierarchy.WireTelescope.TurnShelf
open ThreeFlat Routing Tagged
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped BigOperators Classical

variable {p e : ℕ}

def rowField (z : RowData p e) : Fin 5→ℕ :=
  ![(z.role false).val,(z.role true).val,(z.start false).val,(z.start true).val,z.live.val]

def projection : Control p e→Fin 5 × ℕ
  | .inl j=>(4,j.val)
  | .inr (b,.inl j)=>(if b then 3 else 2,j.val)
  | .inr (b,.inr j)=>(if b then 1 else 0,j.val)

def addr {sites slots : ℕ} (base : ℕ) (site : Fin sites) (slot : Fin slots) (f : Fin 5) :=
  base+f.val*(sites*slots)+site.val*slots+slot.val

/-- No computation is needed at a Boolean pin: it is an exposed bit of a
fixed address of the control CPU, common to every tag and selector. -/
def wire {sites slots : ℕ} (base : ℕ) (s : Fin sites) (q : Pin slots p e) :
    (ℕ × ℕ) ⊕ Aperture p e :=
  match q with
  | .inl (t,c) => let j:=projection c; .inl (addr base s t j.1,j.2)
  | .inr a=>.inr a

def nativeView {W sites slots : ℕ} (base : ℕ) (s : Fin sites) (m : Memory W)
    (v : Aperture p e→Bool) : Pin slots p e→Bool :=
  Sum.elim (fun j : ℕ×ℕ=>(m j.1).val.testBit j.2) v ∘ wire base s

theorem header_bit (z : RowData p e) (j : Control p e) :
    header z j=(rowField z (projection j).1).testBit (projection j).2 := by
  rcases j with t|⟨b,t|t⟩
  · rfl
  · cases b <;> rfl
  · cases b <;> rfl

theorem nativeView_eq {W sites slots : ℕ} (base : ℕ) (s : Fin sites) (m : Memory W)
    (z : Fin slots→RowData p e) (v : Aperture p e→Bool)
    (read : ∀t f,(m (addr base s t f)).val=rowField (z t) f) :
    nativeView base s m v=pins z v := by
  funext q
  rcases q with ⟨t,c⟩|a
  · change (m (addr base s t (projection c).1)).val.testBit (projection c).2=header (z t) c
    rw [read,header_bit]
  · rfl

/-- Obtain all codes directly from the final memory, with a fieldwise fit
proof sufficient to identify their unsigned values. -/
def fromRAM {W sites slots : ℕ} (base : ℕ) (s : Fin sites) (m : Memory W) (t : Fin slots)
    (roles : ∀ b : Bool,(m (addr base s t (if b then 1 else 0))).val<2^p)
    (starts : ∀ b : Bool,(m (addr base s t (if b then 3 else 2))).val<2^e)
    (live : (m (addr base s t 4)).val<2^(e+p+1)) : RowData p e where
  role b:=⟨_,roles b⟩
  start b:=⟨_,starts b⟩
  live:=⟨_,live⟩

theorem fromRAM_read {W sites slots : ℕ} (base : ℕ) (s : Fin sites) (m : Memory W)
    (roles : ∀t : Fin slots,∀b : Bool,(m (addr base s t (if b then 1 else 0))).val<2^p)
    (starts : ∀t : Fin slots,∀b : Bool,(m (addr base s t (if b then 3 else 2))).val<2^e)
    (live : ∀t : Fin slots,(m (addr base s t 4)).val<2^(e+p+1)) (t : Fin slots) (f : Fin 5) :
    rowField (fromRAM base s m t (roles t) (starts t) (live t)) f=(m (addr base s t f)).val := by
  fin_cases f <;> rfl

end Hierarchy.WireTelescope.TurnShelf

end
end OAI
