import OAI.Hierarchy.DescentDatedLocalScale
import OAI.Hierarchy.DescentNamedResetSheets
import OAI.Hierarchy.DescentNamedFundedScale

namespace OAI
/-! # Every original candidate slot and short field at a calibrated reset date -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentSixParty.Chronology
open DescentResetLocalRoster DescentNamedFundedChart DescentFallbackPeriod DescentFallbackShapeTable
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders Filter
noncomputable section
set_option quotPrecheck false
variable {ι : ℕ→Type*} (J : ℕ→ℕ)

structure LocalFields (s : ∀h,ι h→CandidateSheets) (shape original : ∀h,ι h→ℕ) : Prop where
  block : SmallAt J fun h i=>(s h i).blocks
  shapes : SmallAt J shape
  slots : SmallAt J fun h i=>(s h i).candidates
  jobs : SmallAt J fun h i=>(s h i).jobs
  contact : SmallAt J fun h i=>(s h i).contacts
  private_ : SmallAt J fun h i=>(s h i).privates
  «meta» : SmallAt J fun h i=>(s h i).metaBits
  old : SmallAt J fun h i=>(s h i).stemBits
  select_ : SmallAt J fun h i=>(s h i).selectorBits
  short : SmallAt J fun h i=>(s h i).shortBits
  blank : SmallAt J fun h i=>(s h i).zeroBits
  halo : SmallAt J fun h i=>(s h i).haloBits
  argument : SmallAt J fun h i=>(s h i).argBits
  stem : SmallAt J fun h i=>(s h i).stemSources.width
  original_ : SmallAt J original

variable {n d : ℕ} (board : NonlinearExpanders.Graph n d) (D f g : ℕ)
  (S : ∀h,ι h→AtomSchedule) (k tail age cap lanes : ∀h,ι h→ℕ)
local notation "Ht" => GroupStage.depthBound D n f g
local notation "s" =>fun h i=>fromBoard (S h i) board (k h i) (tail h i) (age h i) D f g (cap h i) (lanes h i)
local notation "shapes" =>fun h i=>(DescentDenseHostOrder.roster board (k h i) Ht).card
local notation "original" =>fun h i=>originalBits D (k h i) n Ht (cap h i) (programCount board Ht) g

theorem local_fields (window : SmallAt J (fun h i=>2^(k h i))) (capacity : SmallAt J cap) :
    LocalFields J s shapes original :=by
  let c z:=SmallAt.const (ι:=ι) J z
  have depth:=window.of_le (a:=k) fun _ _=>Nat.lt_two_pow_self.le
  have window' : SmallAt J (fun h i=>2^(k h i+1)):=by
    simpa only [pow_succ] using window.mul (c 2)
  have shp:SmallAt J shapes :=
    ((c (2*((2^n+1)+((2*d+4)*2^n+(2^n+1)*2^(Ht+1))))).mul window').of_le fun _ _=>DescentDenseHostOrder.roster_bound ..
  have roots : SmallAt J (fun h i=>rootSlots (k h i) (2^n)):=window'.add (window'.mul (c (2^n+1)))
  have choices:=roots.mul (c (2^n+2^Ht))
  have contacts:=(c 2).mul choices
  have pri:=(c 2).mul (roots.mul (c (DescentResetCableSlots.cableCap board Ht)))
  have candidates:=((c 2).mul (window.mul ((c 2).mul capacity))).add ((c 1).add (contacts.add pri))
  have pc:=((c (2^g)).mul capacity)
  have mb:=((c 5).max (pc.add (c 2))).clog.max (((c (D+2)).clog).add ((shp.add (c 1)).clog))
  have port:=(capacity.add (c 1)).clog
  have signed : SmallAt J (fun h i=>DescentSignedCableCodec.width D (cap h i)) :=
    ((c (D+1)).clog).add (port.add (port.add (port.add (c 2))))
  have old:=signed.max ((depth.add (c 1)).max ((c (2*(D+1)+2)).clog))
  have interval:=(depth.add (c 1)).mul window
  have rows:=interval.mul (c (2^n+1))
  have sender:=((c 2).mul depth).add (c (2*n)) |>.add (c Ht) |>.add port |>.add (c 10)
  have inField:=((c (Ht+2)).max (signed.max ((c 2).add rows.clog))).max
    ((depth.add (c 1)).max ((c (n+1)).max (port.max sender)))
  have span:=(window.add (c 1)).mul (c (D+2)) |>.mul window
  have site:=((c (D+2)).mul interval).add ((c (D+2)).mul (interval.mul (c (2^n+1))))
  have shafts:=site.add ((site.mul (c (max (2^n) (2^Ht)))).add
    ((c 2).mul (site.mul (c (programCount board Ht)))))
  have numbers:=(c 2).mul (((c 2).mul (span.mul (capacity.mul capacity))).add shafts)
  refine ⟨window,shp,candidates,window.mul (contacts.add pri),contacts,pri,mb,old,
    (choices.add (c 1)).clog,((choices.max ((c (D+2)).max shp)).add (c 1)).clog,
    c 1,(c (D+2)).clog,((c 1).max pri).clog,?_,?_⟩
  · exact inField.max (mb.max (mb.mul (c 7)))
  · exact (((c 5).max (pc.add (c 1))).max numbers).clog

/-- The previous cap is the actual chronological prefix. The host count,
group padding and lane choices never enter these local fields. -/
theorem scale_at {F:Type} [Field F] (G:PoweredGadget F) (t reset τ B : ℕ)
    (mag age batch : ∀h,ι h→ℕ) :
    let j:=fun h=>Nat.log 2 h/(2*B)
    let sched:=fun h i=>stageNumbers G t (j h) f g reset (mag h i) (TerminalScale.tail τ (j h))
    let k₀:=fun h=>groupBits t (j h) (hostRate t reset) (capRate G t g) (cutRate t f g)
    let actual:=fun h i=>((capCalendar G.b t g (j h)).take (age h i)).prod*256
    LocalFields j (fun h i=>fromBoard (sched h i) board (k₀ h) (TerminalScale.tail τ (j h))
      (age h i) D f g (actual h i) (batch h i))
      (fun h _=>(DescentDenseHostOrder.roster board (k₀ h) Ht).card)
      (fun h i=>originalBits D (k₀ h) n Ht (actual h i) (programCount board Ht) g) :=by
  intro j sched k₀ actual
  have window : SmallAt (ι:=ι) j (fun h _=>2^(k₀ h)) :=
    ⟨1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g,
      Eventually.of_forall fun h _=>Nat.pow_le_pow_right (by decide) (groupBits_linear ..)⟩
  have ports : SmallAt j actual:=⟨8+((capPeriod G.b t g).map (·+1)).prod,
    Eventually.of_forall fun h i=>capPrefix G.b t g (j h) (age h i)⟩
  exact local_fields j board D f g sched (fun h _=>k₀ h) (fun h _=>TerminalScale.tail τ (j h)) age actual batch window ports

/-- The group coordinate of a stem uses only the public residual basis.
The shared original-site query ranges over one prior degree plus the true
native shape palette. -/
theorem coordinate_scale {F:Type} [Field F] (G:PoweredGadget F) (t reset τ B : ℕ)
    (mag age batch : ∀h,ι h→ℕ) :
    let j:=fun h=>Nat.log 2 h/(2*B)
    let sched:=fun h i=>stageNumbers G t (j h) f g reset (mag h i) (TerminalScale.tail τ (j h))
    let k₀:=fun h=>groupBits t (j h) (hostRate t reset) (capRate G t g) (cutRate t f g)
    let actual:=fun h i=>((capCalendar G.b t g (j h)).take (age h i)).prod*256
    let sh:=fun h i=>fromBoard (sched h i) board (k₀ h) (TerminalScale.tail τ (j h))
      (age h i) D f g (actual h i) (batch h i)
    SmallAt j (fun h i=>(sh h i).stemDimension) ∧
    SmallAt j (fun h (_:ι h)=>D+(DescentDenseHostOrder.roster board (k₀ h) Ht).card) :=by
  intro j sched k₀ actual sh
  let c z:=SmallAt.const (ι:=ι) j z
  have bounds:=scale_at board D f g G t reset τ B mag age batch
  have dep:=bounds.block.of_le (a:=fun h (_:ι h)=>k₀ h) fun _ _=>Nat.lt_two_pow_self.le
  have jj : SmallAt (ι:=ι) j (fun h _=>j h) :=
    ⟨1,Eventually.of_forall fun h _=>by change j h≤2^(1*(j h+1));rw [one_mul];exact (Nat.le_succ _).trans Nat.lt_two_pow_self.le⟩
  have residual:= (c τ).mul (jj.add (c 1))
  have remaining : SmallAt j (fun h i=>(sched h i).length-age h i):=
    ((c (t+1)).mul jj).of_le fun _ _=>Nat.sub_le ..
  exact ⟨(residual.add (dep.mul remaining)).add dep,(c D).add bounds.shapes⟩

end
end Hierarchy.DescentDatedAddressBook.CandidateSheets

end OAI
