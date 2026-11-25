import OAI.Hierarchy.DescentRecipeResetSuccessor
import OAI.Hierarchy.DescentIssuedCanonicalReset
import OAI.Hierarchy.DescentClosedReset

namespace OAI
/-! # The selected physical reset carries its own paid scalar occurrences -/

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentColonies DescentFineTerminals DescentResetInvoice DescentBaseProfile
open DescentRotor DescentMixedRouter DescentHostDegree
open LinearAlgebra.SpectralBooks ThreeFlat
open Expander NonlinearExpanders
open scoped Classical BigOperators
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z w hist : ℕ}

namespace ClosedReset

variable {W : MarkedWorld F d P bits} {D n h C f g cut tail : ℕ}
    {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (b : ClosedReset input ctl)
local notation "key" => (DescentOrderedReset.grains W b.count b.order)

/-- The optimizer uses the actual predecessor numbering, load table, and marked contact rows. -/
structure MeasuredChoice : Prop where
  basis : b.frame.basis =
    (input.placement.numberedHeader (S.resetInputDigits ctl.base ctl.radix i) input.vertex).chosenBasis
      input.placement f (quota S.rounds)
  depth : ∀ v, b.reset.placement.b (b.frame.host v) =
    (input.placement.numberedHeader (S.resetInputDigits ctl.base ctl.radix i) input.vertex).depth
      input.placement f v

/-- All true paid scalar occurrences on the same selected physical bank for
which the reset placement, rotor and native census were issued. -/
structure Recorded (p : ℕ) : Prop where
  positive : 0<p
  divides : p∣b.reset.unit
  tagged : ∀u,b.raw.hub (b.raw.pos u).2=b.reset.reentryTag b.terminals u
  entries : HEq b.raw.records (b.reset.recipeRecords b.terminals input.placement.records
    (b.reset.laneRecipe key (b.reset.unit/p) p positive (Nat.div_mul_cancel divides).symm))
  sizes : ∀v,(b.raw.records v).length=(b.reset.recipeRecords b.terminals input.placement.records
    (b.reset.laneRecipe key (b.reset.unit/p) p positive (Nat.div_mul_cancel divides).symm) v).length
  measured : b.MeasuredChoice
  reserve : (w : ℝ) * b.reset.pay ≤ ((2^f * (w*(z*G.b)*input.placement.cap) : ℕ) : ℝ)
  reserve_exact : (w : ℝ) * b.reset.pay = ((2^f * (w*(z*G.b)*input.placement.cap) : ℕ) : ℝ)
  neighbors : b.raw.near=b.reset.emittedNear b.terminals


end ClosedReset

theorem close_recipe_branch {W : MarkedWorld F d P bits} {D n h C f g cut tail p : ℕ}
    (input : Reached W G q ε S k i z D w hist) (ctl : ResetRates G S k D n h C f g cut tail)
    (age : i<S.length) (budget : ε=((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
    (hp : 0<p) (grainAt : z=S.grainAt G.b p (i+1)) (base : G.b≤2^S.capGain)
    (wire : w=S.epochPower^S.priceExponent) (history : hist=S.firstWidth G.b p) :
    ∃b : ClosedReset input ctl,b.Recorded p := by
  rcases input with @⟨V, vFin, vDec, A, ready, rfl, rfl, rfl, rfl, order, vertex, edgeName, siteName⟩
  let prior : Reached W G q ε S k i A.z A.degree A.wire A.hist :=
    { V := V, finite := vFin, eqV := vDec, placement := A, valid := ready,
      grain := rfl, edges := rfl, atoms := rfl, branch := rfl,
      order := order, vertex := vertex, edgeName := edgeName, siteName := siteName }
  let depth:=S.groupWidth k tail i
  let digits:=S.resetInputDigits ctl.base ctl.radix i
  have pop : 2^(depth+k-k)=S.groupCount i:=by simpa [depth] using S.group_power ctl.base ctl.radix i
  have fg : f≤g:=by rw [ctl.gain];exact Nat.le_add_right ..
  let H := A.numberedHeader digits vertex
  have numbered : H.vertex A = vertex.trans Fin.valEmbedding := by ext u; rfl
  have raw:=A.issued_reset_canonical_rosters S ctl.board order ready age.le digits pop ctl.radix ctl.fixed budget
    ctl.fcut fg ctl.gk (by omega : k≤depth+k) ctl.degree ctl.enough (Nat.succ_pos _)
    ctl.bits_positive ctl.rows ctl.menu ctl.loss H
  obtain ⟨Z,T,bill,zk,depthEq,dim,count,unit,width,graph,frame,basis,depthRead,roster,tickets⟩:=raw
  rw [numbered] at roster
  have used : T.commonDepth=depth:=by simpa using depthEq
  have range : Z.k-T.commonDepth≤k:=by rw [zk,used];omega
  let code:=S.resetOutputDigits ctl.base ctl.radix age used
  let key:=DescentOrderedReset.grains W A.grainCount order
  obtain ⟨N,paid,z',w',hist',degree,capacity,site,block,hubFlag,neighbors,tagged,entries,sizes⟩:=
    A.recipe_reset_successor S ready Z T key code budget ctl.height age ctl.radix ctl.fixed count unit
      frame.originalHub bill ctl.gain range (by simpa [dim,GroupStage.depthBound] using ctl.host)
      ctl.cap ctl.fineCap ctl.seed hp grainAt base wire history
  let b : ClosedReset prior ctl := {
    count:=A.grainCount,count_eq:=rfl,fit:=A.grainCount_fit S ready,order:=order,order_eq:=rfl,
    reset:=Z,terminals:=T,age:=age,commonDepth:=used,keyWidth:=zk,tickets:=tickets,unit:=unit,dimension:=dim,width:=width,graph:=graph,
    frame:=frame,roster:=roster,raw:=N,rawGeometry:=⟨site,block⟩,rawHub:=hubFlag,valid:=paid,grain:=z',wire:=w',atoms:=hist',degree:=degree,capacity:=capacity}
  let m:=ResetInput.calendarLanes S G.b (i+1)
  have fit : Z.unit=m*p:=ResetInput.calendar_fit Z S G.b p (i+1) (unit.trans (congrArg (·*G.b) grainAt))
  have div : p∣Z.unit:=⟨m,fit.trans (Nat.mul_comm _ _)⟩
  have same : Z.unit/p=m:=by rw [fit,Nat.mul_div_cancel _ hp]
  have laneEq (a b' : ℕ) (eqn : a=b') (fa : Z.unit=a*p) (fb : Z.unit=b'*p) :
      Z.laneRecipe key a p hp fa=Z.laneRecipe key b' p hp fb := by subst b';rfl
  have agree:=laneEq (Z.unit/p) m same (Nat.div_mul_cancel div).symm fit
  refine ⟨b,hp,div,tagged,?_,?_,⟨basis,depthRead⟩,bill.reserve,bill.reserve_exact,neighbors⟩
  · change HEq N.records (Z.recipeRecords T A.records (Z.laneRecipe key (Z.unit/p) p hp _))
    rw [agree]
    exact entries
  · intro v
    change (N.records v).length=(Z.recipeRecords T A.records (Z.laneRecipe key (Z.unit/p) p hp _) v).length
    rw [agree]
    exact sizes v

end
end Hierarchy.DescentSixParty

end OAI
