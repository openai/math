import OAI.Hierarchy.TaggedWireTurnHeader
import OAI.Hierarchy.ProtocolRAMTurnShelf

namespace OAI
/-! # The five gate fields recovered from exact native turn-scatter readback -/
noncomputable section
namespace Hierarchy.WireTelescope.TurnShelf
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical
variable {W N sites slots p e : ℕ}
variable (base : ℕ) (m : Memory W) (col : Fin N→Fin 7→ℕ)
  (put : ProtocolRAMTurnShelf.Live col ↪ ProtocolRAMTurnShelf.Seats sites slots)
  (written : ∀ (f : Fin 5) (a : Fin sites × Fin slots),
    m (addr base a.1 a.2 f)=ProtocolRAMTurnShelf.entry col put f a)
  (fieldFit : ∀u : ProtocolRAMTurnShelf.Live col,∀ f : Fin 5,col u.val (f.castLE (by decide))<2^W)

include written fieldFit in
theorem scatter_present (u : ProtocolRAMTurnShelf.Live col) (f : Fin 5) :
    (m (addr base (put u).1 (put u).2 f)).val = col u.val (f.castLE (by decide)) := by
  rw [written f (put u),ProtocolRAMTurnShelf.entry,put.injective.extend_apply]
  exact Nat.mod_eq_of_lt (fieldFit u f)

include written in
theorem scatter_absent (a : Fin sites×Fin slots) (absent : a∉Set.range put) (f : Fin 5) :
    (m (addr base a.1 a.2 f)).val=0 := by
  rw [written f a,ProtocolRAMTurnShelf.entry,Function.extend_apply' _ _ _ absent]
  rfl

include written fieldFit in
/-- Fields of the native record are read at the same fixed base used by the
committed output of the CPU. The physical equality gate sees its literal
bit wires, including each high unoccupied row which has been zeroed. -/
theorem scatter_view (s : Fin sites) (v : Aperture p e→Bool)
    (fits : ∀u : ProtocolRAMTurnShelf.Live col,
      (∀b : Bool,col u.val (if b then 1 else 0)<2^p) ∧
      (∀b : Bool,col u.val (if b then 3 else 2)<2^e) ∧ col u.val 4<2^(e+p+1)) :
    ∃ z : Fin slots→RowData p e,nativeView base s m v=pins z v ∧
      (∀ u : ProtocolRAMTurnShelf.Live col,(put u).1=s→∀ f : Fin 5,
        rowField (z (put u).2) f=col u.val (f.castLE (by decide))) ∧
      (∀ t,(s,t)∉Set.range put→∀f,rowField (z t) f=0) := by
  classical
  have general (t : Fin slots) (f : Fin 5) (b : ℕ) (hb : 0<b)
      (cap : ∀u : ProtocolRAMTurnShelf.Live col,col u.val (f.castLE (by decide))<b) :
      (m (addr base s t f)).val<b := by
    by_cases h : (s,t)∈Set.range put
    · obtain ⟨u,atSlot⟩:=h
      have eq:=scatter_present base m col put written fieldFit u f
      rw [atSlot] at eq
      rw [eq]
      exact cap u
    · rw [scatter_absent base m col put written (s,t) h f]; exact hb
  have role (t : Fin slots) (b : Bool) :
      (m (addr base s t (if b then 1 else 0))).val<2^p := by
    apply general _ _ _ (Nat.two_pow_pos p)
    intro u
    cases b with
    | false => exact (fits u).1 false
    | true => exact (fits u).1 true
  have start (t : Fin slots) (b : Bool) :
      (m (addr base s t (if b then 3 else 2))).val<2^e := by
    apply general _ _ _ (Nat.two_pow_pos e)
    intro u
    cases b with
    | false => exact (fits u).2.1 false
    | true => exact (fits u).2.1 true
  have live (t : Fin slots) : (m (addr base s t 4)).val<2^(e+p+1) :=
    general _ _ _ (Nat.two_pow_pos _) (fun u=>(fits u).2.2)
  let z t:=fromRAM base s m t (role t) (start t) (live t)
  have identity (t f) : rowField (z t) f=(m (addr base s t f)).val:=
    fromRAM_read base s m role start live t f
  refine ⟨z,nativeView_eq base s m z v (fun t f=>(identity t f).symm),?_,?_⟩
  · intro u site f
    rw [identity,←site]
    exact scatter_present base m col put written fieldFit u f
  · intro t empty f
    exact (identity t f).trans (scatter_absent base m col put written (s,t) empty f)

end Hierarchy.WireTelescope.TurnShelf

end
end OAI
