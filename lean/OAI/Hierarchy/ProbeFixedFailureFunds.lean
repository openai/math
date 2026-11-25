import OAI.Hierarchy.ProbeNativeRoleAddress
import OAI.Hierarchy.ProbeNativeActivePorts
import OAI.Hierarchy.ProtocolRAMNativeOccurrenceFormat

namespace OAI
/-! # Reading aggregate repair funding from the physical occurrence header

An occurrence that actually moves bits belongs to a committed row. Its
destination expression names an ordinary slot in that row. The two injective
placements of the strip construction (payload or purchased) therefore charge
every real commodity at most once, including when the role stride is padded.
-/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.StockCommit

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe RepairHistogram
open scoped Classical Fin.CommRing BigOperators

variable {w q : ℕ} {A : Type*} (h : PortHeader) (start goods limit : ℕ)
  (old reserve half price : Bank) (mode : Expr) (slot : Fin h.ports → Option Expr)
  (b : Batch q h.ports) (tabs : Fin h.ports → Fin q → Expr) (mem : Memory w)
  (loaded : h.Loaded mem) (portFit : h.ports ≤ 2^w) (termFit : q ≤ 2^w)
  (copyFit : b.copies < 2^w) (sumFit : q*b.copies < 2^w) (bankFit : start+goods < 2^w)

local notation "dest" => StripDirectory.destination h goods slot
local notation "commit" => fresh (h.area start goods limit) (h.sources old reserve half price mode dest b tabs)
local notation "plan" => h.plan mem start goods limit old reserve half price mode dest b tabs
  loaded portFit termFit copyFit sumFit
local notation "kind" => RepairHistogram.kind (goods:=goods) (commit).plan.bank (commit).columns mem
local notation "put" => installedBits (n:=h.count) (commit).columns mem
local notation "take" => consumedBits (n:=h.count) (commit).columns mem
local notation "live" => ↥(liveRows b mem h.rows)

variable (field : A → Fin h.ports) (operand : A → Expr)
  (decode : ∀ v x,slot v=some x → ∃ a,field a=v ∧ operand a=x)
  (place : ↥(liveRows b mem h.rows) × A ↪ Fin goods)
  (address : ∀ (j : ↥(liveRows b mem h.rows)) a,
    ((operand a).eval mem (j.val.val:Word w)).val=(place (j,a)).val)

include loaded portFit termFit copyFit sumFit bankFit field operand decode place address

theorem PortHeader.moving_unique {i : Fin goods} {e f : Fin h.count}
    (le : kind e=some i) (lf : kind f=some i) (pe : 0 < put e+take e)
    (pf : 0 < put f+take f) : e=f := by
  have locate (j : Fin h.rows) (v : Fin h.ports) (real : kind (h.enum ⟨j,v⟩)=some i)
      (moving : 0 < put (h.enum ⟨j,v⟩)+take (h.enum ⟨j,v⟩)) :
      ∃ (r : live) (a : A), r.val=j ∧ field a=v ∧ place (r,a)=i := by
    have on : j∈liveRows b mem h.rows := by
      by_contra bad
      have outside : ((plan).enum.symm ((plan).enum ⟨j,v⟩)).1 ∉ liveRows b mem h.rows := by
        simpa only [Equiv.symm_apply_apply] using bad
      have off := (plan).off ((plan).enum ⟨j,v⟩) outside
      change put (h.enum ⟨j,v⟩)=0 ∧ take (h.enum ⟨j,v⟩)=0 at off
      omega
    obtain ⟨x,slotEq,atSlot⟩ := (StripDirectory.fresh_kind_iff h start goods limit old reserve half price
      mode slot b tabs mem loaded portFit bankFit j v i).mp real
    obtain ⟨a,atField,rfl⟩ := decode v x slotEq
    exact ⟨⟨j,on⟩,a,rfl,atField,Fin.ext ((address ⟨j,on⟩ a).symm.trans atSlot)⟩
  obtain ⟨⟨j,v⟩,rfl⟩ := h.enum.surjective e
  obtain ⟨⟨l,t⟩,rfl⟩ := h.enum.surjective f
  obtain ⟨r,a,rfl,rfl,ha⟩ := locate j v le pe
  obtain ⟨s,c,rfl,rfl,hc⟩ := locate l t lf pf
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (place.injective (ha.trans hc.symm))
  rfl

/-- The actual signed debit scatter is funded at every physical bank address.
The incoming stock is the word read by the very row that passed the gate. -/
theorem PortHeader.funded_of_slots
    (source : ∀ v x,slot v=some x → b.stock v=.lookup old x)
    (seed : ∀ i : Fin goods,old.read mem (i.val:Word w)=mem (start+i.val)) (i : Fin goods) :
    OuterBank.resourceBits kind take i ≤ (mem (start+i.val)).val := by
  apply (plan).funded i
  · intro j v hit
    exact StripDirectory.fresh_stock_position h start goods limit old reserve half price mode slot b tabs
      mem loaded portFit bankFit j v i (source v) (seed i) hit
  · intro e f he hf de df
    exact h.moving_unique start goods limit old reserve half price mode slot b tabs mem loaded portFit
      termFit copyFit sumFit bankFit field operand decode place address he hf
      (de.trans_le (Nat.le_add_left (take e) (put e)))
      (df.trans_le (Nat.le_add_left (take f) (put f)))

/-- The same uniqueness bounds all additions by the maximum physical port
credit, even if a different address is charged at another positive role. -/
theorem PortHeader.credit_bound_of_slots (maxCredit : ℕ) (i : Fin goods)
    (credit : ∀ (j : Fin h.rows) (v : Fin h.ports), ((b.wire (tabs v)).eval mem (j.val:Word w)).val ≤ maxCredit) :
    OuterBank.resourceBits kind put i ≤ maxCredit := by
  apply funded_of_unique kind put (fun _ => maxCredit) i
  · intro e _
    obtain ⟨⟨j,v⟩,rfl⟩ := h.enum.surjective e
    exact ((plan).read j v).1.le.trans (credit j v)
  · intro e f he hf de df
    apply h.moving_unique start goods limit old reserve half price mode slot b tabs mem loaded portFit
      termFit copyFit sumFit bankFit field operand decode place address he hf <;> omega

theorem PortHeader.credit_fit_of_slots (maxCredit : ℕ) (i : Fin goods)
    (credit : ∀ (j : Fin h.rows) (v : Fin h.ports), ((b.wire (tabs v)).eval mem (j.val:Word w)).val ≤ maxCredit)
    (size : (mem (start+i.val)).val+maxCredit < 2^w) :
    (mem (start+i.val)).val+OuterBank.resourceBits kind put i < 2^w := by
  have cap:=h.credit_bound_of_slots start goods limit old reserve half price mode slot b tabs mem loaded
    portFit termFit copyFit sumFit bankFit field operand decode place address maxCredit i credit
  exact lt_of_le_of_lt (Nat.add_le_add_left cap _) size

end Hierarchy.ProtocolRAM.Calendar.StockCommit
end

end OAI
