import OAI.Hierarchy.DescentDatedOperandHeaderTriplet
import OAI.Hierarchy.DescentDatedSourcePathHeaders

namespace OAI
/-! # Unconditional bounded execution of the prior chip, route directory, and old local ranks -/
namespace Hierarchy.DescentDatedSourcePathDirectory
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentHaloWalkRAM DescentSharedCableNames
open DescentSharedLeafLookup DescentPackedZip DescentSIMDLookup DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false

theorem all_pages_step {H G M D w : ℕ} (B : Banks) (base : ℕ) (m : Memory w)
    (fit : Fits B H (breadth D) base w) (space : stop base H G M D<2^w) :
    Step base (stop base H G M D) (allPages B base H G M D w) m :=by
  let hot:=(hostJob B H D).atBase base w
  let mid:=hot.image m
  let lo:=hostEnd base H D
  let I:=Public.literals lo 1 H G M (Packed.bits (breadth D)) w
  have span:H≤ stride H:=Nat.le_pow_clog (by decide) _
  have clipped (i : ℕ) (hi : i<breadth D*(D+1)) : (columns B H D i).Fits w base:=by
    rw [columns,dite_eq_left hi]
    apply body_fits B fit
  have low:lo≤ stop base H G M D:=end_le ..
  have ran:=SignedPrefix.Job.any (hostJob B H D) base m ⟨span,clipped⟩ (low.trans_lt space)
  have prior:Step base lo hot m:=⟨Nat.le_add_right ..,ran.1,ran.2⟩
  have len : I.low+I.length=stop base H G M D:=by
    change lo+(stop base H G M D-lo)=_
    exact Nat.add_sub_of_le low
  have install:=I.issue mid (len.trans_lt space)
  have later : Step lo (stop base H G M D) (broadcast base H G M D w) mid:=by
    refine ⟨low,install.1,?_⟩
    intro i hi
    exact install.2.2 i hi
  exact prior.thenStep later

theorem local_rank_step {w H D : ℕ} (B : Local.Directory) (base : ℕ) (m : Memory w)
    (ep : B.endpoints.Fits w base) (_rk : B.localRank.Fits w base) (space : Local.stop base H D<2^w) :
    Step base (Local.stop base H D) ((Local.job B H D).atBase base w) m :=by
  let col:=fun i=>if hi:i<breadth D then Local.entry B H ⟨i,hi⟩ else (.lit 0:Expr)
  have clipped (i : ℕ) (hi : i<breadth D) : (col i).Fits w base :=by
    simp only [col,dite_eq_left hi]
    exact Local.entry_fits B ep _
  have span:H≤ stride H:=Nat.le_pow_clog (by decide) _
  have run:=SignedPrefix.Job.any (Local.job B H D) base m ⟨span,clipped⟩ space
  exact ⟨Nat.le_add_right ..,run.1,run.2⟩
end
end Hierarchy.DescentDatedSourcePathDirectory

namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentDatedOperandReadPipeline DescentPackedZip DescentDatedSourcePathDirectory
open DescentPacking.PackedMatch.Local.Stage.Chooser DescentHaloWalkRAM DescentRawCablePanel
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
set_option quotPrecheck false
variable {F Pin : Type} [Field F] (v : PhysicalOrdinary F Pin)
variable (floor : ℕ) (A : v.ArgumentEntry)
local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "H₀" => (e₀).oldHosts
local notation "G₀" => (e₀).groups
local notation "M₀" => (e₀).lanes
local notation "D₀" => (fmt₀).degree
local notation "lo₀" => v.originMouthEnd floor
local notation "path₀" => v.operandPathStart floor
local notation "rank₀" => v.operandRankStart floor
local notation "stop₀" => v.operandOldHeaderStart floor

theorem before_headers_any {w : ℕ} (m : Memory w) (below : A.venue.panel.base+A.venue.panel.size≤lo₀)
    (rows : H₀*DescentSIMDLookup.chunks (e₀).oldGroups (e₀).oldLanes≤A.venue.panel.size)
    (wide : (e₀).oldLanes*max (DepotRAM.totalBits fmt₀) (e₀).fieldBits≤w/2)
    (pathFit : Fits (nativeBanks H₀ G₀ M₀ D₀ (v.donorEnd floor)) H₀ (breadth D₀) path₀ w)
    (ep : (v.operandRanks floor).endpoints.Fits w rank₀) (rk : (v.operandRanks floor).localRank.Fits w rank₀)
    (space : stop₀<2^w) :
    Step lo₀ stop₀ (v.operandBeforeHeaders floor w A) m :=by
  have one : lo₀≤path₀:=by
    rw [operandPathStart,DescentDatedOperandPages.affine]
    exact Nat.le_add_right ..
  have two : path₀≤rank₀:=(Nat.le_add_right ..).trans (end_le ..)
  have three : rank₀≤ stop₀:=Nat.le_add_right ..
  have raw:=DescentDatedOperandPages.any fmt₀ v.operandDepotLayout lo₀ A.venue.panel m below rows wide
    (two.trans_lt (three.trans_lt space))
  let dep:=v.operandDepot floor w A
  let search:=v.operandPaths floor w
  have a : Step lo₀ path₀ dep m:=⟨one,raw.1,raw.2⟩
  have b : Step path₀ rank₀ search (dep.image m):=all_pages_step _ path₀ _ pathFit (three.trans_lt space)
  have c : Step rank₀ stop₀ (v.operandRankPhase floor w) (search.image (dep.image m)):=local_rank_step _ rank₀ _ ep rk space
  exact (a.thenStep b).thenStep c

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
