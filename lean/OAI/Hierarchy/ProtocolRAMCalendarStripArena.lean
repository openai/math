import OAI.Hierarchy.ProtocolRAMStripSlabData
import OAI.Hierarchy.ProtocolRAMCalendarStripChart
import OAI.Hierarchy.ProtocolRAMCalendarBoot
import OAI.Hierarchy.ProtocolRAMPurchaseMarketCost

namespace OAI
/-! # Height-linear chronological slabs containing private histograms, advice, and outputs -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen
open PurchaseStage StripDirectory PortPadding
open scoped Classical
variable {z d k q depth : ℕ}
local notation "N" => List.length (Fabric.shapes (permutationFabric z d))
local notation "P" => Fintype.card (PayloadRole N k)
local notation "R" => Fintype.card (PurchasedRole depth k)
local notation "D" => max P R

namespace Slab
variable (v : Slab) (s : Boards z d k q depth)

def rowFactor := count z d k*s.sampler.degree^depth
def rows := rowFactor s*2^z
/-- Include the actual power-of-two Bank.size in the address allocator so
every generated indexed load satisfies the native prefix read contract. -/
def selectorSpan := 2^(z+q*rowFactor s)
def failureSpan := 2^(z+rowFactor s)
def first (base : ℕ) := base+selectorSpan s+failureSpan s+2^(z+v.thresholdExtra)
def flags (base : ℕ) := first v s base+count z d k*blockSize z d s.sampler.degree depth+
  2*(paths z s.sampler.degree depth+1)
def goods (z d k : ℕ) := PurchaseInventory.footprint z (permutationFabric z d).shapes.length k
def mask (base : ℕ) := flags v s base+rows s+1+(goods z d k+1)+(goods z d k+1)+(rows s+1)
def digits (z d k depth : ℕ) :=
  max (Fintype.card (PayloadStrip.Quotes (permutationFabric z d).shapes.length k))
    (Fintype.card (ChainStrip.Axes depth k))
def stride :=
  PostLayout.column (mask v s 0) (z+rowFactor s) (rows s) (17+3*D+digits z d k depth)+1+
    5*(rows s*D)+rows s+8*goods z d k+4
def arena : Arena := ⟨v.headerEnd,stride v s⟩

/-- The flat private selector table starts at the event base. The failed-root
words follow it, then the immutable sign threshold table and all sampler stages.
The final stock commit has a disjoint bank for positive spills. -/
def localize {digits ports : ℕ} (b : StripDirectory.Boards z d k q digits ports) (base : ℕ) :
    StripDirectory.Boards z d k q digits ports :=
  let th := base+selectorSpan s+failureSpan s
  let sh := {b.market.shelf with thresholdBase:=th,tableBits:=z+v.thresholdExtra,firstBase:=first v s base}
  {b with
    market := {b.market with shelf := sh}
    test := {b.test with base := base+selectorSpan s, rowBits := z+rowFactor s}
    selectors := ⟨base,z+q*rowFactor s⟩
    indexBits := z+rowFactor s}

def install (c : Mesh) : Boards z d k q depth :=
  {s with
    outer := fun p a=>localize v s (s.outer p a) ((arena v s).base c (.attempt (.outer p a)))
    inner :=fun p a j t=>localize v s (s.inner p a j t) ((arena v s).base c (.attempt (.inner p a j t)))}

theorem rows_eq : rows s=count z d k*paths z s.sampler.degree depth := by
  unfold rows rowFactor PurchaseFrozen.paths
  ring

theorem selector_room : q*rows s≤2^(z+q*rowFactor s) := by
  rw [pow_add]
  calc q*rows s = 2^z*(q*rowFactor s) := by unfold rows; ring
       _ ≤ _ := Nat.mul_le_mul_left _ (Nat.lt_two_pow_self (n:=q*rowFactor s)).le

theorem row_room : rows s≤2^(z+rowFactor s) := by
  rw [pow_add]
  calc rows s = 2^z*rowFactor s := Nat.mul_comm ..
       _ ≤ _ := Nat.mul_le_mul_left _ (Nat.lt_two_pow_self (n:=rowFactor s)).le

theorem mask_shift (base : ℕ) : mask v s base=base+mask v s 0 := by
  unfold mask flags first
  omega

def coefficient :=
  let a := rowFactor s
  let b := count z d k*factor d s.sampler.degree depth
  let g := 1+N*(2*k)
  2^(q*a) + 2^a + 2^v.thresholdExtra + b + 2*s.sampler.degree^depth +
    (21+3*D+digits z d k depth)*a + 10*g + 2^a + 5*(a*D) + 15

/-- This clock-independent bound includes every initialized sampler and hidden
selector cell of every attempt, followed by all post and signed stock rows. -/
theorem stride_linear : stride v s≤coefficient v s*2^z := by
  have one : 1≤2^z := Nat.one_le_two_pow
  simp only [stride,PostLayout.column,PostLayout.startColumns,mask,flags,first,selectorSpan,failureSpan,rows,goods,coefficient,
    PurchaseFrozen.blockSize,PurchaseFrozen.paths,PurchaseInventory.footprint,pow_add,zero_add]
  nlinarith only [one]

theorem size_linear (c : Mesh) {C : ℕ} (initial : v.headerEnd≤C*2^z) :
    (arena v s).endAddress c≤(C+(events c).length*coefficient v s)*2^z := by
  calc (arena v s).endAddress c = v.headerEnd+(events c).length*stride v s := rfl
       _ ≤ C*2^z+(events c).length*(coefficient v s*2^z) :=
         Nat.add_le_add initial (Nat.mul_le_mul_left _ (stride_linear v s))
       _ = _ := by ring

variable (F : Type*) [Field F]
  [SiteNaming (ColumnSite (PayloadStrip.Columns (List.length (Fabric.shapes (permutationFabric z d)))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
variable (c : Mesh) (initial : ℕ)
local notation "A" => arena v s
local notation "B" => install v s c
local notation "profiles" => formats F c A initial B

theorem sizes (a : Attempt) :
    let f := profiles a
    let base := (A).base c (.attempt a)
    f.market.rows=rows s ∧ f.market.failures.base=base+selectorSpan s ∧
      f.market.shelf.table.base=base+selectorSpan s+failureSpan s ∧ f.market.shelf.firstBase=first v s base ∧
      f.market.flags=flags v s base ∧ f.indexBits=z+rowFactor s ∧ f.occurrences=rows s*D ∧
      f.coordinates=goods z d k := by
  rw [rows_eq s]
  cases a <;> exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem mask_eq (a : Attempt) : (profiles a).maskStart=mask v s ((A).base c (.attempt a)) := by
  let f := profiles a
  obtain ⟨r,_,_,_,g,_,_,_⟩ := sizes v s F c initial a
  change f.market.flags+f.market.rows+1+(_+1)+(_+1)+(_+1)=_
  have excess : f.batch.tests.excess.rows=goods z d k := by cases a <;> rfl
  have payload : f.batch.tests.payload.rows=goods z d k := by cases a <;> rfl
  have fail : f.market.failures.rows=f.market.rows := by cases a <;> rfl
  change f.market.flags+f.market.rows+1+(f.batch.tests.excess.rows+1)+(f.batch.tests.payload.rows+1)+
    (f.market.failures.rows+1)=_
  rw [fail,excess,payload,r,g]
  rfl

theorem quote_extent (a : Attempt) : (profiles a).batch.batch.quotes.length≤digits z d k depth := by
  cases a with
  | outer p t =>
    change (List.ofFn (_ : Fin (Fintype.card (PayloadStrip.Quotes N k)) → Expr)).length≤_
    rw [List.length_ofFn]
    exact Nat.le_max_left ..
  | inner p t j b =>
    change (List.ofFn (_ : Fin (Fintype.card (ChainStrip.Axes depth k)) → Expr)).length≤_
    rw [List.length_ofFn]
    exact Nat.le_max_right ..

theorem fit (a : Attempt) : (profiles a).pricedArea.stop≤(A).base c (.attempt a)+(A).stride := by
  let f := profiles a
  let base := (A).base c (.attempt a)
  obtain ⟨r,_,_,_,_,bits,occ,coord⟩ := sizes v s F c initial a
  have maskAt := mask_eq v s F c initial a
  have price := quote_extent v s F c initial a
  have upper := f.pricedArea.span
  change f.pricedArea.stop≤PostLayout.column f.maskStart f.indexBits f.market.rows
    (17+3*D+f.batch.batch.quotes.length)+1+f.occurrences+4*f.occurrences+f.market.rows+8*f.coordinates+4 at upper
  rw [maskAt,bits,occ,r,coord,mask_shift] at upper
  have cols := Nat.mul_le_mul_right (rows s) (Nat.add_le_add_left price (17+3*D))
  unfold PostLayout.column PostLayout.startColumns at upper
  change f.pricedArea.stop≤base+
    (mask v s 0+2^(z+rowFactor s)+rows s+2+(17+3*D+digits z d k depth)*rows s+1+
      5*(rows s*D)+rows s+8*goods z d k+4)
  dsimp only [f,base] at upper cols ⊢
  omega

theorem order (a : Attempt) :
    let f := profiles a
    let base := (A).base c (.attempt a)
    base≤f.market.failures.base ∧ base≤f.market.shelf.firstBase ∧ base≤f.testsStart := by
  obtain ⟨r,fail,_,stage,g,_,_,_⟩ := sizes v s F c initial a
  dsimp only
  rw [Format.testsStart,fail,stage,g,r]
  let base := (A).base c (.attempt a)
  have early : base ≤ first v s base := by
    unfold first
    simp only [Nat.add_assoc]
    exact Nat.le_add_right ..
  have paid : base ≤ flags v s base :=
    (early.trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  exact ⟨Nat.le_add_right ..,early,paid.trans (Nat.le_add_right ..)⟩

end Slab
end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
