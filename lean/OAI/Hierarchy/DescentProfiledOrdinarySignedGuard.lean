import OAI.Hierarchy.DescentProfiledOrdinaryOffer
import OAI.Hierarchy.DescentDatedSignedSpace
import OAI.Hierarchy.DescentDatedMeter
import OAI.Hierarchy.DescentSeedNumberRates

namespace OAI
/-! # Additional address space above the signed program on every ordinary offer -/
namespace Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer
open DescentCompiler DescentCompiler.TerminalScale DescentResetInvoice DescentInitialHost Chronology
open DescentDatedAddressBook DescentDatedSeedStartup DescentPacking.PackedMatch.Local.Stage
open DescentHostDegree DescentHaloWalkRAM DescentSIMDLookup Filter
open ThreeFlat.Routing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d) (op : RotorSpec)
    (t f g reset τ drift degreeMax B : ℕ)
local notation "idx" h:arg => ProfiledOrdinaryOffer G f g board op t reset τ drift degreeMax B h
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg => stageNumbers G t (J_ h) f g reset (x:idx h).slot.sites (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "D_" h:arg x:arg => DonorDate.atDate G (S_ h x) g (k_ h) (x:idx h).slot.age x.slot.p

section Varying
variable {ι : ℕ → Type*} (tailRate budget : ∀h,ι h → ℕ)
variable (point : ∀h (i : ι h),ProfiledOrdinaryOffer G f g board op t reset (tailRate h i) drift degreeMax (budget h i) h)
local notation "epoch" h:arg i:arg => Nat.log 2 h/(2*budget h i)
local notation "cal" h:arg i:arg => stageNumbers G t (epoch h i) f g reset (point h i).slot.sites (tail (tailRate h i) (epoch h i))
local notation "digits" h:arg i:arg => groupBits t (epoch h i) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "donor" h:arg i:arg => DonorDate.atDate G (cal h i) g (digits h i) (point h i).slot.age (point h i).slot.p

/-- Packing and the native ticket give the guard bound on any jointly bounded family of dates. -/
theorem guard_from_axes
    (oldHost : Bounded (fun h i=>(cal h i).hostSize (point h i).slot.age))
    (newHost : Bounded (fun h i=>(cal h i).hostSize ((point h i).slot.age+1)))
    (newGroup : Bounded (fun h i=>(cal h i).groupCount ((point h i).slot.age+1)))
    (blockCount : Bounded (fun h i=>2^(digits h i))) :
    Bounded (fun h i=>let x:=point h i; x.model.signedGuard x.stageFloor-x.model.signedEnd x.stageFloor) := by
  let s (h) (i : ι h):=(point h i).model.signed
  have signedShape (h) (i : ι h) : s h i=SignedStage.signedAt G (cal h i) g (digits h i) (point h i).slot.age h :=
    congrArg PhysicalOrdinary.StaticCore.signed (point h i).core
  have actual (h) (i : ι h) : (point h i).model.ticket.donorDate=donor h i :=
    congrArg PhysicalOrdinary.StaticCore.donor (point h i).core
  have degree_bound (h) (i : ι h) : (donor h i).degree≤ initialDegreeMax t := seed_degree t G.b _
  have table (A : ℕ→ℕ) : Bounded (fun h (i : ι h)=>A (donor h i).degree) := by
    let K:=(Finset.range (initialDegreeMax t+1)).sup A
    exact (Bounded.const K).of_le fun h i=>Finset.le_sup (s:=Finset.range (initialDegreeMax t+1))
      (f:=A) (Finset.mem_range.mpr (Nat.lt_succ_of_le (degree_bound h i)))
  have lowHost : Bounded (fun h (i : ι h)=>(s h i).priorHosts) :=
    oldHost.padded.of_le fun h i=>by rw [signedShape]; rfl
  have highHost : Bounded (fun h (i : ι h)=>(s h i).hosts) :=
    newHost.padded.of_le fun h i=>by rw [signedShape];exact (NativePitch.hosts_bounds _ _ (point h i).slot.active).2
  have grp : Bounded (fun h (i : ι h)=>(s h i).groups) :=
    newGroup.of_le fun h i=>by rw [signedShape]; rfl
  have lanesB : Bounded (fun h (i : ι h)=>(s h i).lanes) := by
    refine ⟨1,Eventually.of_forall fun h i=>?_⟩
    change (s h i).lanes ≤ 2^(1*h)
    rw [signedShape,Nat.one_mul]
    exact (Nat.div_le_self h _).trans (Nat.lt_two_pow_self.le)
  have chunk := (grp.add lanesB).of_le (y:=fun h (i : ι h)=>chunks (s h i).groups (s h i).lanes)
    (fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..))
  have sheets := ((highHost.mul chunk).add (lowHost.mul chunk)).of_le
    (y:=fun h (i : ι h)=>max (s h i).slab (s h i).oldSlab)
    (fun _ _=>max_le (Nat.le_add_right ..) (Nat.le_add_left ..))
  have reach : Bounded (fun h (i : ι h)=>(s h i).reach) :=
    (table breadth).of_le fun h i=>by rw [signedShape]; rfl
  have sockets:= table (fun j=>2^packExponent 20 j+2)
  have block : Bounded (fun h (i : ι h)=>2^((digits h i)+1)) := by
    simpa only [Nat.pow_succ] using blockCount.mul (Bounded.const 2)
  have lows : Bounded (fun h (i : ι h)=>(s h i).lowSites) :=
    (block.mul sockets).of_le fun h i=>by rw [signedShape]; rfl
  have pitch : Bounded (fun h (i : ι h)=>(point h i).model.materialPitch) := by
    apply (block.mul sockets).of_le
    intro h i
    have old : (point h i).model.prior.placement.degree=(donor h i).degree:=congrArg DonorDate.degree (actual h i)
    have code : (point h i).model.k=digits h i:=congrArg DonorDate.exponent (actual h i)
    change (2^((point h i).model.k+1)-1)*(2^packExponent 20 (point h i).model.stage.Δ+2)≤_
    rw [(Dated.Meter.ticket_shape (point h i).model.ticket).2,old,code]
    exact Nat.mul_le_mul_right _ (Nat.sub_le ..)
  have sq:=reach.mul reach
  have price:=((((((sheets.add (lowHost.mul sq)).add (lowHost.mul pitch)).add lows).add highHost).add lowHost).add sq).add (Bounded.const 1)
  apply price.of_le
  intro h i
  dsimp only [s,PhysicalOrdinary.signedGuard]
  omega

end Varying

/-- The guard contains only row, host, and static alphabet counts. All of those are bounded even
when the signed lane count is zero, so this estimate needs no positive-lane hypothesis. -/
theorem signed_guard_excess : Bounded (fun h (x : idx h)=>
    x.model.signedGuard x.stageFloor-x.model.signedEnd x.stageFloor) := by
  let sites (h) (x : idx h):=x.slot.sites
  let age (h) (x : idx h):=x.slot.age
  let grain (h) (x : idx h):=x.slot.p
  have source : Bounded sites := ⟨2,Eventually.of_forall fun h x=>by
    simpa only [sites,←pow_mul,Nat.mul_comm h 2] using x.slot.siteLimit⟩
  have geo:=PhysicalOrdinary.ordinary_geometry G t f g reset τ B sites age grain source
    (fun h x=>x.slot.active.le)
  exact guard_from_axes G board op t f g reset drift degreeMax (fun _ _=>τ) (fun _ _=>B)
    (fun _ x=>x) geo.axis.oldHost geo.axis.newHost geo.axis.newGroup geo.blocks

end
end Hierarchy.DescentSixParty.SeedNamed.ProfiledOrdinaryOffer

end OAI
