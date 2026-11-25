import OAI.Hierarchy.ProbeCatalystMenuDebit
import OAI.Hierarchy.ProbeCatalystCashRead
import OAI.Hierarchy.ProbeStripMenuLookup

namespace OAI
/-! # Signed catalyst amounts of the actually selected native ballot -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open AdaptiveProbe ColumnWires Computability.VPVNP.BurstRAM PrivateRAM Calendar Calendar.StockCommit RepairHistogram
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing

variable {F E A B C H : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  [Fintype B] [Fintype C] [Fintype H] {k sites N w q D n z d balls : ℕ} [Nonempty (Fin sites)]
  {edge : E→ Chord sites} {req : A→E} {box : Set (E→ℝ)} {ε tree : ℝ}

theorem live_debit {s : StockCommit} {b : Batch q D} {m : Memory w} (l : PortPlan s b m balls)
    (j : Fin balls) (live : j∈liveRows b m balls) (i : Fin D) :
    consumedBits s.columns m (l.enum ⟨j,i⟩)=((b.need i).eval m (j.val:Word w)).val := by
  rw [(l.read j i).2,debit_eval _ _ _ _ l.termRoom l.copyRoom l.sumRoom,ite_eq_left (Finset.mem_filter.mp live).2]

variable [Nonempty (Role C H (A⊕B) k)] {M : ℝ} {len : H→ℝ} {cap : A→ℝ}
local notation "Roles" => Role C H (A⊕B) k
local notation "needRoles" => demand (I:=C) (H:=H) (k:=k) (Sum.inl (α:=A) (β:=B))
local notation "prices" => (fun y:A→ℝ => quote (I:=C) (k:=k) M len (LocalCommodity.extraPrice (B:=B) y)) '' Set.Icc 0 cap

/-- Read a complete primitive role from the final enabled batch, using its
actual frozen packet word. The selector's term alphabet can vary with the
entry. Neither the emitted histogram nor a padding lane is presumed valid. -/
theorem menu_live_cash {e : Roles→ Chord sites} (menu : Probe.FixedMenu F e needRoles prices ε tree N)
    {s : StockCommit} {b : Batch q D} {m : Memory w} (layout : PortPlan s b m balls)
    (bound : Fintype.card Roles≤D) (j : Fin balls) (live : j∈liveRows b m balls)
    (room : 1+Fintype.card menu.index≤2^w)
    (capFits : b.maxWidth<2^w) (wide : b.copies*b.maxWidth<2^w)
    (maximum : ∀ i v,StripDirectory.useBits menu i v≤b.maxWidth)
    (compiled : ∀ v, b.perCopy (PortPadding.inject bound (Fintype.equivFin Roles v)) =
      StripDirectory.entry menu b.packet (fun i => StripDirectory.useBits menu i v))
    (v : Roles) (kind : RepairHistogram.kind (goods:=s.goods) s.plan.bank s.columns m
      (layout.enum ⟨j,PortPadding.inject bound (Fintype.equivFin Roles v)⟩)=none ↔ account id v=none) :
    let picked := menuIndex menu.index (b.packet.eval m (j.val:Word w)).val
    cashWord layout (j,PortPadding.inject bound (Fintype.equivFin Roles v))=
      released v (b.copies*(picked.elim 0 (fun i=>cashRate M (menu.packet i).width))) := by
  intro picked
  let row : Word w := j.val
  let ix := PortPadding.inject bound (Fintype.equivFin Roles v)
  have nz := (Finset.mem_filter.mp live).2.1.2.1
  have positive : 0<(b.packet.eval m row).val := Nat.pos_of_ne_zero (fun h=>nz (Fin.ext h))
  have coeff := entry_word menu b.packet (fun i=>StripDirectory.useBits menu i v) m row room positive
  have lim : picked.elim 0 (fun i=>StripDirectory.useBits menu i v)≤b.maxWidth := by
    cases hp : picked with
    | none => exact Nat.zero_le _
    | some i => exact maximum i v
  change _=((picked.elim 0 (fun i=>StripDirectory.useBits menu i v) : ℕ) : Word w) at coeff
  have coef : ((b.perCopy ix).eval m row).val=picked.elim 0 (fun i=>StripDirectory.useBits menu i v) := by
    rw [compiled,coeff,Fin.val_cast_of_lt (lim.trans_lt capFits)]
  have debit := b.need_bits m row ix (coef.le.trans lim) capFits (by rw [coef];exact (Nat.mul_le_mul_left _ lim).trans_lt wide)
  rw [coef] at debit
  simp only [cashWord,kind,live_debit _ _ live]
  change (if account id v=none then ((b.need ix).eval m row).val else 0) = _
  rw [debit]
  cases hp : picked with
  | none => cases v <;> simp [released]
  | some i =>
    have quote := menu_cash menu i id v
    cases v with
    | catalyst c axis => simp_all [released,ColumnWires.account]
    | radius c axis sign => simp_all [released,ColumnWires.account]
    | cross c a s t => simp_all [released,ColumnWires.account]
    | horizontal h lane => simp_all [released,ColumnWires.account]
    | extra v => cases v <;> simp_all [released,ColumnWires.account]

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
