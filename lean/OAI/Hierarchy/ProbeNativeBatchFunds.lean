import OAI.Hierarchy.ProbeNativeDemandFunds
import OAI.Hierarchy.ProbeStripFormat

namespace OAI
/-! # Stock sufficiency on the actual native strip query and histogram admission test -/

namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Fin.CommRing Classical BigOperators
noncomputable section
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E} {box : Set (E→ℝ)} {ε tree : ℝ} {N : ℕ}
  {q goods digits w : ℕ}

theorem debited_useBits (m : Probe.FixedMenu F edge req box ε tree N) (i : m.index) (e : E) (copies : ℕ) :
    debited (fun a : Probe.PositiveDemand req i.val.val=>req a.val) (copies*(m.packet i).width) e =
      copies*useBits m i e := by
  classical
  rw [debited,←Finset.sum_filter,Finset.sum_const]
  simp [useBits,Fintype.card_subtype,Nat.mul_assoc,Nat.mul_comm]

/-- A true finite lookup coefficient, including all occurrences, supplies the
real width operand of the native debit program before it inspects the selector. -/
theorem batch_need (menu : Probe.FixedMenu F edge req box ε tree N) (test : StripTest digits)
    (terms codes enabled selectors stocks : Bank) (owner : Expr) (copies maxWidth : ℕ)
    (ports : Fin goods→E) (slot : Fin goods→Option Expr) (index : menu.index) (v : Fin goods)
    (mem : Memory w) (row : Word w) (room : 1+Fintype.card menu.index≤2^w)
    (cap : maxWidth<2^w) (width : useBits menu index (ports v)≤ maxWidth) (fit : copies*maxWidth<2^w) :
    let b := batch (q:=q) menu test terms codes enabled selectors stocks owner copies maxWidth ports slot
    (b.packet.eval mem row).val=(Fintype.equivFin menu.index index).val+1 →
    ((b.need v).eval mem row).val=debited (fun a : Probe.PositiveDemand req index.val.val=>req a.val)
      (copies*(menu.packet index).width) (ports v) := by
  intro b hit
  have read : (b.perCopy v).eval mem row=(useBits menu index (ports v):Word w) :=
    entry_read menu b.packet (fun j => useBits menu j (ports v)) index mem row room hit
  have val := (congrArg Fin.val read).trans (Fin.val_cast_of_lt (width.trans_lt cap))
  calc
    ((b.need v).eval mem row).val = b.copies*((b.perCopy v).eval mem row).val :=
      b.need_bits mem row v (val.le.trans width) cap (by rw [val]; exact (Nat.mul_le_mul_left _ width).trans_lt fit)
    _ = copies*useBits menu index (ports v) := congrArg (copies * ·) val
    _ = _ := (debited_useBits menu index (ports v) copies).symm

/-- Every field of this very lookup row is stocked. Non-stock roles receive
exactly their posted debit; ordinary fields check the current integer bit bank. -/
theorem batch_funded (menu : Probe.FixedMenu F edge req box ε tree N) (test : StripTest digits)
    (terms codes enabled selectors stocks : Bank) (owner : Expr) (maxWidth : ℕ)
    (ports : Fin goods→E) (slot : Fin goods→Option Expr) (mem : Memory w) (row : Word w)
    (rounded : E→ℝ) (legal : rounded∈box) (failed : ε≤Probe.discrepancy F edge req rounded)
    {J : Type*} [Fintype J] (width : J→ℕ) (code : menu.index→J) (layout : ∀j,width (code j)=(menu.packet j).width)
    (phase : PhasePrice) (lane : Fin goods→ℕ) (K mult : ℕ) {γ : ℝ}
    (ha : 0<phase.a) (hs : 0<phase.time) (bonus : ∀v,0≤phase.bonus (lane v)) (M : 0≤phase.M)
    (hw : 0<phase.bits) (kp : 0<K) (large : 2*(K*commonWidth width)≤phase.bits) (hp : 0≤γ) (small : γ≤ menu.margin)
    (arity : Fintype.card A≤ mult) (rate : (mult:ℝ)/K≤phase.time*phase.a*γ) (room : 1+Fintype.card menu.index≤2^w)
    (cap : maxWidth<2^w) (fit : (phase.bits/(K*commonWidth width))*maxWidth<2^w) :
    let index := menu.select ⟨rounded,legal,failed⟩
    let copies := phase.bits/(K*commonWidth width)
    let b := batch (q:=q) menu test terms codes enabled selectors stocks owner copies maxWidth ports slot
    (b.packet.eval mem row).val=(Fintype.equivFin menu.index index).val+1 →
    (∀v,useBits menu index (ports v)≤ maxWidth) →
    (∀v addr,slot v=some addr → rounded (ports v)≤phase.quote (lane v) (stocks.read mem (addr.eval mem row)).val) →
    ∀v, ((b.need v).eval mem row).val≤((b.stock v).eval mem row).val := by
  intro index copies b lookup maxCoeff rounds v
  cases field : slot v with
  | none => rw [batch_cash (q:=q) menu test terms codes enabled selectors stocks owner copies maxWidth ports slot v field]
  | some addr =>
    rw [batch_stock (q:=q) menu test terms codes enabled selectors stocks owner copies maxWidth ports slot v addr field,
      batch_need (q:=q) menu test terms codes enabled selectors stocks owner copies maxWidth ports slot index v mem row room cap (maxCoeff v) fit lookup]
    exact failed_menu_funded menu rounded legal failed (ports v) width code layout phase (lane v) _ K mult ha hs (bonus v) M hw kp large hp small (rounds v addr field) arity rate

end
end Hierarchy.ProtocolRAM.StripDirectory

end OAI
