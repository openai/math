import OAI.Hierarchy.DescentTerminalCohortOrder
import OAI.Hierarchy.DescentExteriorReplay

namespace OAI
/-! # One ancestry computation per original slab and frozen coordinate -/

namespace Hierarchy.DescentTerminalExteriorPackets
open DescentGL DescentColonies DescentExterior Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {j r E b f w : ℕ} {A V : Type}
local notation "k" => j+(j+r)
local notation "P" => Σ _:Fin (2^k),Fin E
variable {start : (Σ _ : Fin (2 ^ (j + (j + r))), Fin E) → Bits (j + (j + r))}
    {live : (Σ _ : Fin (2 ^ (j + (j + r))), Fin E) → Bits b}
    {before : (Σ _ : Fin (2 ^ (j + (j + r))), Fin E) → A}
    {after : (Σ _ : Fin (2 ^ (j + (j + r))), Fin E) → V}
    (s : Spine start live before after f) (seed : Fin E → Layout (j + (j + r)))

/-- One real original pin at the representative coordinate of an ancestry.
Its leading remixed bits are the specified frozen word and its live word is zero. -/
def representative (s : Spine start live before after f) (seed : Fin E → Layout (j + (j + r)))
    (a : Fin E×Fin (2^f)) : P :=
  ⟨address k ((seed a.1).symm (s.cut.symm (0,(address f).symm a.2))),a.1⟩

theorem representative_frozen (openPin : ∀u:P,start u=seed u.2 ((address k).symm u.1))
    (u : Fin E×Fin (2^f)) :
    (s.cut (start (representative s seed u))).2=(address f).symm u.2 := by
  simp [openPin,representative]

/-- The index is independent of the hidden selector and reachable host order.
The native per-row base table is common to all candidate histories with this calendar. -/
def previous (room : j≤b) (width : f+b=k) (i : Fin (E*2^(j+r))) : Fin E×Fin (2^f) :=
  let t:=finProdFinEquiv.symm i
  (t.1,⟨t.2.val/2^(b-j),by
    have fac : j+r=f+(b-j) := by omega
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
    simpa only [←pow_add,←fac] using t.2.isLt⟩)

theorem chart_previous (room : j≤b) (opened : ∀u:P,start u=seed u.2 ((address k).symm u.1))
    (u : P) :
    previous room ((Nat.add_comm f b).trans s.width) (chart (rotor s seed) u).1 =
      (u.2,address f (s.cut (start u)).2) := by
  let y:=frozenFirst s (start u)
  have upper:=row_high (j:=j) (r:=r) y
  have eqn : (rowOrd j r (coords j r y).2).val/2^(b-j)=(address f (s.cut (start u)).2).val := by
    rw [←upper,Nat.div_div_eq_div_mul,←pow_add,show j+(b-j)=b by omega]
    exact frozen_digit s _
  have coded : (chart (rotor s seed) u).1 =
      finProdFinEquiv (u.2, rowOrd j r (coords j r y).2) := by
    dsimp only [y]
    rw [opened u]; rfl
  rw [coded]
  apply Prod.ext
  · simp only [previous, Equiv.symm_apply_apply]
  · apply Fin.ext
    simpa only [previous, Equiv.symm_apply_apply] using eqn

theorem owner_previous (room : j≤b) (opened : ∀u:P,start u=seed u.2 ((address k).symm u.1))
    (same : ∀u v:P,u.2=v.2→before u=before v) (i : Fin (E*2^(j+r))) :
    owner s seed i=after (representative s seed (previous room ((Nat.add_comm f b).trans s.width) i)) := by
  let u:P:=(chart (rotor s seed)).symm (i,⟨0,Nat.two_pow_pos j⟩)
  have row : (chart (rotor s seed) u).1=i := by simp [u]
  rw [←row,chart_previous s seed room opened]
  change after ((chart (rotor s seed)).symm ((chart (rotor s seed) u).1,⟨0,_⟩))=_
  rw [row]
  change after u=_
  let v := representative s seed (u.2, address f (s.cut (start u)).2)
  change after u = after v
  refine s.host_eq u v (same u v rfl) ?_
  dsimp only [v]
  rw [representative_frozen s seed opened, Equiv.symm_apply_apply]

/-- Distinct replay work is reduced by the complete surviving radix,
including every residual group. This identity includes empty exterior. -/
theorem size_frozen (sized : b+f=k) : (E*2^f)*2^b=E*2^k := by
  rw [Nat.mul_assoc,←pow_add,Nat.add_comm f b,sized]

/-- Only the final cohort pass reads these computed ancestries at physical
word width. The preceding history loop has one entry per frozen value. -/
theorem replay_bill (_room : j≤b) (sized : b+f=k) (hs : List DescentExteriorReplay.Hop) :
    DescentExteriorReplay.clocks (E*2^f) hs*2^b ≤
      (hs.length*4+4)*2^b+96*hs.length*(E*2^k) := by
  have bounds:=Nat.mul_le_mul_right (2^b) (DescentExteriorReplay.total_price (E*2^f) hs)
  calc
    _ ≤ _ := bounds
    _ = (hs.length*4+4)*2^b+96*hs.length*((E*2^f)*2^b) := by ring
    _ = _ := by rw [size_frozen sized]

end
end Hierarchy.DescentTerminalExteriorPackets

end OAI
