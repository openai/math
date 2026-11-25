import OAI.Hierarchy.DescentDatedOrdinaryRate
import OAI.Hierarchy.DescentPackedLayoutFinish

namespace OAI
/-! # Price flag and elected rotation following the actual ordinary matcher -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary
open DescentPackedColony DescentSIMDLookup ProtocolRAM DescentDatedAddressBook Filter
noncomputable section
variable (a : Ordinary)
def batch := (2^(a.k+1)*a.H)*chunks a.G a.lanesAt
def shapeAt := shape (2^a.k) a.D (2*a.cap) a.profile
def flagEnd (old : Bank) (floor : ℕ) :=
  let m:=a.matcher old floor
  LayoutSum.Finish.stop a.shapeAt a.lanesAt m.layout.topology m.layout.out a.batch
def rotationEnd (old : Bank) (floor : ℕ) := a.flagEnd old floor+2^a.k+1

theorem packed_last (old : Bank) (floor : ℕ) :
    let m:=a.matcher old floor
    m.layout.topology.base+m.layout.topology.size≤ m.layout.out ∧ m.layout.out+a.batch=m.endAddr := by
  refine ⟨?_,rfl⟩
  dsimp only [matcher,Gather.ROM.place,Gather.ROM.column,Gather.ROM.stop]
  omega

/-- The old-key bank and normalize/tariff scans share their actual topology
coordinates. Only the last clipped matching output needs padding to a power of two. -/
theorem flag_at (old : Bank) (floor : ℕ) :
    let m:=a.matcher old floor
    a.flagEnd old floor=m.layout.out+2^Nat.clog 2 a.batch+SixBirths.entries a.shapeAt a.lanesAt+
      2^Nat.clog 2 a.batch+2*2^(SixBirths.width a.shapeAt a.lanesAt)+4*a.batch+3 := by
  intro m
  have left:= (a.packed_last old floor).1
  have join : SixBirths.tableStart m.layout.topology (SixBirths.tapeBank m.layout.out a.batch)=
      m.layout.out+2^Nat.clog 2 a.batch := by
    change max _ _=_
    exact max_eq_right (left.trans (Nat.le_add_right ..))
  change LayoutSum.Finish.stop a.shapeAt a.lanesAt m.layout.topology m.layout.out a.batch=_
  unfold LayoutSum.Finish.stop LayoutSum.Finish.chart LayoutSum.plan LayoutSum.Finish.base LayoutSum.Finish.bank
  dsimp only [LayoutSum.Finish.births,SixBirths.outputBase,SixBirths.tapeBank,Bank.size] at join ⊢
  rw [join]

theorem rotation_bound (old : Bank) (floor : ℕ) (width : SixBirths.unit a.shapeAt≤a.unit) :
    a.rotationEnd old floor≤(a.matcher old floor).endAddr+4*2^(a.payload/2)+8*a.batch+2^a.k+6 := by
  let m:=a.matcher old floor
  have packed : a.unit*a.lanesAt≤a.payload/2 := by
    simpa only [lanesAt,Nat.mul_comm a.unit] using lanes_fit a.payload a.unit
  have last:=a.packed_last old floor
  have endAt:=LayoutSum.Finish.extent a.shapeAt a.lanesAt m.layout.topology m.layout.out a.batch
    a.unit a.payload width packed last.1
  change a.flagEnd old floor≤ m.layout.out+8*a.batch+4*2^(a.payload/2)+5 at endAt
  have out : m.layout.out+a.batch=m.endAddr:=last.2
  unfold rotationEnd
  dsimp only [m] at endAt out
  omega

theorem rotation_add (old : Bank) (base bump : ℕ) :
    a.rotationEnd old (bump+base)=bump+a.rotationEnd old base := by
  have first:=(a.packed_last old (bump+base)).2
  have second:=(a.packed_last old base).2
  have step:=a.matcher_add old base bump
  unfold rotationEnd
  rw [a.flag_at old (bump+base),a.flag_at old base]
  omega

theorem rotation_rate {ι : ℕ→Type*} (a : ∀h,ι h→Ordinary) (old : ∀h,ι h→Bank)
    (b : ScalarRoom a) (width : ∀h i,SixBirths.unit (a h i).shapeAt≤(a h i).unit) :
    DescentDatedAddressBook.Bounded (fun h i=>(a h i).rotationEnd (old h i) 0) := by
  have ram:=matcher_rate a old b
  obtain ⟨K,words⟩:=b.payload
  have half : DescentDatedAddressBook.Bounded (fun h i=>2^((a h i).payload/2)) := DescentDatedAddressBook.Bounded.pow_of_linear (K:=K)
    (words.mono fun h wh i=>(Nat.div_le_self ..).trans (wh i))
  have lanes : DescentDatedAddressBook.Bounded (fun h i=>(a h i).lanesAt) :=
    (DescentDatedAddressBook.Bounded.pow_of_linear (K:=K) words).of_le fun _ _=>(Nat.div_le_self ..).trans Nat.lt_two_pow_self.le
  have rows : DescentDatedAddressBook.Bounded (fun h i=>chunks (a h i).G (a h i).lanesAt) :=
    ((b.groups.add lanes).sub (y:=fun _ _=>1)).div
  have r := b.radix
  have succ : DescentDatedAddressBook.Bounded (fun h i=>2^((a h i).k+1)) := by simpa only [Nat.pow_succ] using r.mul (DescentDatedAddressBook.Bounded.const 2)
  have n : DescentDatedAddressBook.Bounded (fun h i=>(a h i).batch) := (succ.mul b.hosts).mul rows
  exact ((((ram.add ((DescentDatedAddressBook.Bounded.const 4).mul half)).add ((DescentDatedAddressBook.Bounded.const 8).mul n)).add r).add (DescentDatedAddressBook.Bounded.const 6)).of_le
    fun h i=>(a h i).rotation_bound (old h i) 0 (width h i)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Dated.Ordinary

end OAI
