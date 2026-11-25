import OAI.Hierarchy.DescentOrdinaryPriorRetile
import OAI.Hierarchy.DescentOrdinaryRoleRetileRate
import OAI.Hierarchy.DescentDatedOverlapAperture
import OAI.Hierarchy.DescentDatedPriorOperandRate
import OAI.Hierarchy.DescentOrdinaryOverlapReserve

namespace OAI
/-! Address and instruction counts for the standard seven pages of every previous operand. -/
namespace Hierarchy.DescentOrdinaryPriorRetile
open DescentSIMDLookup DescentDatedPriorOperand DescentStaticWordColumn
open ProtocolRAM DescentPackedZip DescentColonies.SplitRAM Filter DescentDatedAddressBook
set_option quotPrecheck false
noncomputable section
variable (l:Layout) (lanes base prior w:ℕ)
local notation "P" => Overlap.pieces l.groups l.lanes lanes
local notation "rows" => (shape l lanes).rows
local notation "K" => 1+40*P
local notation "out" => output l lanes base

theorem affine : roof l lanes base=base+roof l lanes 0:=by
  simp only [roof,output,Overlap.dest,Overlap.dictBase,Nat.zero_add,Nat.add_assoc]

theorem tariff :
    (phase l lanes base prior w).ticks+7*names (phase l lanes base prior w).program ≤
      327+115*(out-base)+pages l*((4+rows*(2*K+4))+7*(11+4*K)) :=
  (roster l lanes).tariff base (sources l prior) w

def rowBill := (pages l+1)*(l.rows+(shape l lanes).rows+P+1)
def lookupBill := (P+1)*(l.lanes+1)*2^(digits l*l.lanes)

theorem shared_fee (old : 0<l.lanes) (next : 0<lanes) :
    (phase l lanes base prior w).ticks+7*names (phase l lanes base prior w).program ≤
      4096*(lookupBill l lanes+rowBill l lanes) :=
  (roster l lanes).shared_fee base (sources l prior) w old next

/-- The table is bought once. The rest of the measured native time is linear in the
two authentic packed row counts even for unrelated lane counts and nonempty tail rows. -/
theorem cofinal_fee (factor saving : ℕ) :
    ∀ᶠ h:ℕ in atTop,∀(l : Layout) (lanes base prior w J original : ℕ),
      J≤Nat.log 2 h → 2^h≤original → 0<l.lanes → 0<lanes → l.lanes≤h → lanes≤h →
      digits l*l.lanes≤h/2 → w+1≤factor*h →
      ((phase l lanes base prior w).ticks+7*names (phase l lanes base prior w).program)*(w+1)
        ≤original/(2^J)^saving+4096*(rowBill l lanes)*(factor*h) :=by
  filter_upwards [Overlap.charged_half_pages (4096*factor) 1 0 saving] with h gates
  intro l lanes base prior w J original small large old next a b packed arch
  have half:=Overlap.half_pages h l.groups l.lanes lanes (digits l) a b packed
  have smallFee:=gates J 0 original small (by simp) large
  have page : 4096*(lookupBill l lanes)*(factor*h)≤original/(2^J)^saving :=by
    apply le_trans _ smallFee
    change 4096*((Overlap.pieces l.groups l.lanes lanes+1)*(l.lanes+1)*2^(digits l*l.lanes))*(factor*h)≤_
    simp only [pow_zero,Nat.mul_one]
    nlinarith only [Nat.mul_le_mul_left (4096*factor*h) half]
  calc
    _ ≤ (4096*(lookupBill l lanes+rowBill l lanes))*(factor*h) :=
      Nat.mul_le_mul (shared_fee l lanes base prior w old next) arch
    _ = 4096*(lookupBill l lanes)*(factor*h)+4096*(rowBill l lanes)*(factor*h) := by ring
    _ ≤ _ := Nat.add_le_add_right page _

theorem address_bound {ι : ℕ→Type*} (l : ∀h,ι h→Layout) (lanes base : ∀h,ι h→ℕ)
    (hosts : Bounded (fun h i=>(l h i).hosts))
    (groups : Bounded (fun h i=>(l h i).groups))
    (old : Bounded (fun h i=>(l h i).lanes))
    (nxt : Bounded lanes)
    (count : Bounded (fun h i=>pages (l h i)))
    (origin : Bounded base)
    (packed : ∃k:ℕ,∀ᶠ h:ℕ in Filter.atTop,∀i,digits (l h i)*(l h i).lanes≤k*h) :
    Bounded (fun h i=>roof (l h i) (lanes h i) (base h i)) :=by
  have section_:=Overlap.address_rate (a:=fun h i=>digits (l h i)) hosts groups old nxt packed
  have grid : Bounded (fun h i=>chunks (l h i).groups (lanes h i)) :=
    (groups.add nxt).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have raw : Bounded (fun h i=>(shape (l h i) (lanes h i)).rows) := hosts.mul grid
  apply ((origin.add section_).add (count.mul raw)).of_le
  intro h i
  rw [affine]
  apply le_of_eq
  change base h i+(output (l h i) (lanes h i) 0+pages (l h i)*(shape (l h i) (lanes h i)).rows+
    2^Nat.clog 2 ((shape (l h i) (lanes h i)).rows+1))=
    (base h i+(output (l h i) (lanes h i) 0+2^Nat.clog 2 ((shape (l h i) (lanes h i)).rows+1)))+
      pages (l h i)*(shape (l h i) (lanes h i)).rows
  ac_rfl

theorem prior_aperture {ι : ℕ→Type*} (l : ∀h,ι h→Layout) (lanes base : ∀h,ι h→ℕ)
    (previous : Layout.ScalarRoom l) (newLanes : Bounded lanes) (priorEnd : Bounded base) :
    Bounded (fun h i=>roof (l h i) (lanes h i) (base h i)) := by
  obtain ⟨C,packed⟩:=previous.width
  exact address_bound l lanes base previous.hosts previous.groups previous.lanes newLanes
    (((Bounded.const 7).mul previous.arities).mul previous.blocks) priorEnd
    ⟨C,packed.mono (fun h good i=>(good i).1)⟩


end
end Hierarchy.DescentOrdinaryPriorRetile

end OAI
