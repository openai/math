import OAI.Hierarchy.DescentNamedBookPublicEntry
import OAI.Hierarchy.DescentNamedSourceSorted
import OAI.Hierarchy.DescentTerminalBookMeasured
import OAI.Hierarchy.DescentTerminalResidentRank

namespace OAI
/-! Authentic six-field input to the fixed row plan from the reached chronology. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


local notation "s" => S.firstWidth G.b p
local notation "net" => ((Epochs.finish G hu he r).state c).graph
local notation "E" => Fintype.card (Port P X.width)
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))



open DescentTerminalGraphPositions DescentTerminalCableOrder DescentTerminalLocalPortBook DescentSharedCableNames DescentColonies
open ThreeFlat.Routing
local notation "retained" => S.groupWidth k tail S.length+k
local notation "O" => leafOrder X G S b hp base width
local notation "placement" => b.target.placement
local notation "native" => b.target.order.trans Fin.valEmbedding
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k
  (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount S.length)) (b.target.vertex.trans Fin.valEmbedding))
local notation "pinRank" v => (densePinEquiv X G S b hp base v).toEmbedding.trans Fin.valEmbedding
local notation "operand" v => leafOperands X G S b hp base v
local notation "calendar" => fun g row => ((S.resetInputDigits base radix S.length).symm (g,row)).val
local notation "scale" => ((placement).z*G.b)/p


open DescentTerminalPaidHeaderEvents DescentTerminalGrainProfiles DescentTerminalPeerChronology DescentTerminalGraphRows
open DescentSortedRoster DescentPhysicalOrder DescentPacking
local notation "H0" => S.hostSize S.length
local notation "hosts" => b.target.vertex.trans (Fin.castLEEmb b.target.valid.host)
local notation "nodeRank" => ((placement).site b.target.vertex b.target.valid.coordinates).trans Fin.valEmbedding
local notation "outs" => leafExternal X G S b hp base width
local notation "ins" => leafOperands X G S b hp base
variable (elapsed:0<S.length) (room:j≤S.groupWidth k tail S.length+k) (whole:p∣S.firstWidth G.b p)
    (raw:Fin (S.hostSize S.length)→Fin b.target.placement.degree→Option (Fin (S.hostSize S.length)))
local notation "R" => indexed raw
variable (boards:Fin (S.hostSize S.length)→Board b.target.placement.degree (S.groupCount S.length) (2^k) b.target.placement.cap)
    (seen:Board.Observed (p:=p) b.target.placement (b.target.vertex.trans (Fin.castLEEmb b.target.valid.host)) S b.target.valid b.target.order raw boards)
local notation "grid" => fun (arity : ℕ) (home : Fin H0) => (boards home).directory arity scale (s/p) (2^retained) calendar

private theorem coarseWidth : (placement).z*G.b=scale*p := by
  apply (Nat.div_mul_cancel _).symm
  rw [b.target.grain];exact dvd_mul_right p _

include seen in
private theorem nativeCovers (e:(net).Edge) (_:0<(net).width e) :
    b.target.home ((net).dst e)∈present R (b.target.home ((net).src e)) ∧
      b.target.home ((net).src e)∈present R (b.target.home ((net).dst e)) := by
  have endpoints:=Counter.all_adjacent placement hosts raw seen.roster e
  rw [←Counter.mounted_present placement hosts raw seen.roster, ←Counter.mounted_present placement hosts raw seen.roster] at endpoints
  simpa [Reached.home] using endpoints

include seen elapsed room whole in
private theorem field (A:ℕ) (i:Fin H0) (v:(net).Site) (home:b.target.home v=i)
    (g:Order.Group O i) (nm:Order.At O i g) (part:Part net p v)
    (trueName:nm.val=DescentTerminalGraphPositions.name net part)
    (a:Fin A) (same:(number net p v (ins v) part).val=a.val) :
    ∃(u:Fin ((placement).degree+1)) (n:ℕ),label R i u=some g.val ∧
      (Order.inGroup O i g nm).val=n ∧
      (grid A i).address (finProdFinEquiv (((placement).pos v).1,(placement).block v)) a=some (u,n) := by
  subst i
  let h:=b.target.home v
  have coarse:=coarseWidth X G S b
  have divides:p∣(placement).z*G.b:=⟨_,coarse.trans (Nat.mul_comm ..)⟩
  have nameSorted:=site_order placement hosts b.target.vertex (fun _=>rfl) b.target.valid.coordinates (b.target.siteName elapsed)
  have sorted:=final_sourceSorted X G S b elapsed
  have limit:(number net p v (ins v) part).val<A:=same.trans_lt a.isLt
  have position:(⟨_,limit⟩:Fin A)=a:=Fin.ext same
  obtain ⟨bound,digit⟩:=part
  cases bound with
  | inl e=>
    let u:=groupSlot R net b.target.home b.target.order outs nodeRank ins hp (nativeCovers X G S b raw boards seen) h g
    have tag:=socket_name R net b.target.home b.target.order outs nodeRank ins hp (nativeCovers X G S b raw boards seen) h g
    have step:=Board.cable_entry placement hosts S b.target.valid b.target.order raw seen.roster (sorted_mounted raw)
      nameSorted sorted b.target.valid.coordinates outs nodeRank (fun v=>pinRank v) hp coarse v e digit g nm trueName u tag
      (boards h) (seen.side h) (seen.signed ((placement).pos v).2) A (s/p) (2^retained) calendar limit
    exact ⟨u,_,tag,rfl,position ▸ step⟩
  | inr port=>
    have public_:g.val=none:=by rw [←nm.property.2,trueName];rfl
    have step:=book_public_entry X G S b hp base width room whole divides v port digit g public_ nm trueName
      (boards h) (seen.resident h) A limit
    exact ⟨0,_,by rw [public_];rfl,rfl,position ▸ step⟩

include seen elapsed room whole in
def book_aligned (A:ℕ) (i:Fin H0) : Aligned ((O).site i) (grid A i) := by
  have coarse:=coarseWidth X G S b
  have el (e:(net).Edge):p∣(net).width e:=by
    have d := b.target.valid.divides e
    rw [b.target.grain] at d
    exact (dvd_mul_right p G.b).trans d
  have pl (z:Σ _:Fin S.copies,Fin E):p∣(s*1):=by simpa using whole
  have «public» (z:Σ _:Fin S.copies,Fin E):(s*1)=(s/p)*p:=by simpa using (Nat.div_mul_cancel whole).symm
  have present:=seen.resident i
  let node:=b.target.calendar i
  have nodeOrder (x y:Order.Nodes O i): (O).nodes i x<(O).nodes i y ↔ node x<node y := by
    rw [Order.nodes,ordered_lt];exact b.target.calendar_compare i x y
  apply DescentTerminalLocalPortBook.aligned net b.target.home b.target.order outs nodeRank ins R hp el pl
    (sorted_mounted raw) (nativeCovers X G S b raw boards seen) i _ node nodeOrder
  · exact Board.counts_read placement hosts S b.target.valid b.target.order raw boards seen b.target.valid.coordinates
      (site_order placement hosts b.target.vertex (fun _=>rfl) b.target.valid.coordinates (b.target.siteName elapsed))
      (final_sourceSorted X G S b elapsed) hp coarse (s/p) «public» i
  · intro u
    change (boards i).venue (finProdFinEquiv.symm (node u)).1 (finProdFinEquiv.symm (node u)).2 = _
    rw [show node u = finProdFinEquiv (((placement).pos u.val).1,(placement).block u.val) from rfl, Equiv.symm_apply_apply]
    exact present.active u.val u.property
  · intro c none
    obtain ⟨⟨g,x⟩,rfl⟩:=finProdFinEquiv.surjective c
    simp only [Board.directory,Equiv.symm_apply_apply]
    apply present.vacant
    rintro ⟨v,h,atG,atX⟩
    exact none ⟨v,h⟩ (congrArg finProdFinEquiv (Prod.ext atG atX))
  · intro n j a eqn
    let v:=Order.node O i n
    let all:=number net p v (ins v)
    let part:=all.symm j
    exact field X G S b hp base width elapsed room whole raw boards seen A i v (((O).nodes i).symm n).property
      _ _ part (at_name net b.target.home b.target.order outs nodeRank ins i n j) a
      ((congrArg Fin.val (all.apply_symm_apply j)).trans eqn)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
