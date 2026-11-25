import OAI.Hierarchy.DescentDatedSampledMaterialValues
import OAI.Hierarchy.DescentDatedOperandNarrowPrefix
import OAI.Hierarchy.DescentDatedOperandHeadTransfer

namespace OAI
/-! # The two narrow source families in the original signed host coordinates -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentDatedAddressBook DescentRawCablePanel DescentPackedZip DescentSIMDLookup DescentHaloWalkRAM
open DescentSharedCableNames DescentSharedLeafLookup DescentDatedSourcePathDirectory DescentPackedColony
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F I : Type} [Field F] (v : PhysicalOrdinary F I) (floor : ℕ)
local notation "e₀" => v.material
local notation "fmt₀" => v.ticket.depotShape v.short
local notation "D" => (fmt₀).degree
local notation "P₀" => breadth D
local notation "H" => (e₀).oldHosts
local notation "K" => (e₀).hosts
local notation "G" => (e₀).groups
local notation "M" => (e₀).lanes
local notation "L" => (e₀).blocks
local notation "base₀" => v.operandPathStart floor
local notation "rank₀" => v.operandRankStart floor
local notation "end₀" => v.operandOldHeaderStart floor
local notation "map₀" => v.receiverMap floor
local notation "b" => Packed.bits P₀
local notation "pathB" => nativeBanks H G M D (v.donorEnd floor)
local notation "rankB" => v.operandRanks floor
local notation "mapStart" => (e₀).projectionStart (v.materialStart floor)
local notation "mapEnd" => DepotRAM.Material.Route.Projection.roof (e₀).fieldBits L M K G P₀ mapStart

theorem narrow_mapped_fits {w out hostCount groupCount laneCount fieldWidth : ℕ} {hdr : Header} (ready : Readable hdr 1 hostCount groupCount laneCount fieldWidth w out)
    {mapB : Bank} (fit : mapB.Fits w out) :
    (DepotRAM.Material.Route.lift mapB (hostCount*chunks groupCount laneCount) (DescentSharedLeafLookup.source hdr (0:Fin 1))).Fits w out :=by
  have key : (Expr.lookup mapB .row).Fits w out:=⟨fit,trivial⟩
  have src : (DescentSharedLeafLookup.source hdr (0:Fin 1)).Fits w out :=
    ⟨ready.fit _ (by simp),⟨ready.fit _ (by simp),trivial⟩,ready.fit _ (by simp),⟨ready.fit _ (by simp),trivial⟩,trivial⟩
  have sub (x y : Expr) (hx : x.Fits w out) (hy : y.Fits w out) : (x.atRow y).Fits w out :=by
    induction x <;> simp_all [Expr.Fits,Expr.atRow]
  exact ⟨key,trivial,trivial,sub _ _ src key⟩

theorem received_map {w : ℕ} (original later : Memory w) (earlier : mapEnd≤base₀)
    (space : base₀<2^w) (blocks : 0<L)
    (stable : ∀i,i< mapEnd→later i=(DepotRAM.Material.Route.Projection.stage H K G M P₀ (e₀).fieldBits L
      v.materialPitch mapStart w).image original i) :
    (map₀).Fits w base₀ ∧ K*chunks G M≤(map₀).size ∧
      ∀j : Row K G M,later ((map₀).base+(row K G M j).val)=(DepotRAM.Material.Route.index H v.materialPitch j:Computability.VPVNP.BurstRAM.Word w) :=by
  have small : K*chunks G M≤(map₀).size:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  have bound : (map₀).base+(map₀).size ≤ mapEnd:=Nat.le_add_right ..
  have fit : (map₀).Fits w base₀ :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((bound.trans earlier).trans_lt space),bound.trans earlier⟩
  let p : Fin P₀:=⟨0,by simp [breadth]⟩
  have posted:=DepotRAM.Material.Route.Projection.installed H K G M (e₀).fieldBits L v.materialPitch mapStart original
    (0:DepotRAM.Material.Route.Port) p ⟨0,blocks⟩
  exact ⟨fit,small,fun j=>(stable _ ((Nat.add_lt_add_left ((row K G M j).isLt.trans_le small) _).trans_le bound)).trans (posted.2.1 j)⟩

theorem narrow_heads_from_local {w : ℕ} (m : Memory w) (R : Fin H → Fin D → Option (Fin H))
    (access : Fits pathB H P₀ base₀ w) (rankFit : Local.Accessible rankB H D w rank₀)
    (visits : DescentDatedSourcePathDirectory.Reads pathB (Gather.reaching R) m)
    (prior : DescentOrdinaryDonorRankDirectory.Reads R rankB ((v.operandPaths floor w).image m))
    (space : end₀<2^w) (safe : H*chunks G M<2^w) (mapFit : (map₀).Fits w base₀) (cap : K*chunks G M≤(map₀).size)
    (ix : ∀j : Row K G M,m ((map₀).base+(row K G M j).val)=(DepotRAM.Material.Route.index H v.materialPitch j:Computability.VPVNP.BurstRAM.Word w)) :
    let run:=(v.operandPaths floor w).seq (v.operandRankPhase floor w)
    run.Runs m ∧ (∀i,i<base₀ ∨ end₀ ≤ i → run.image m i=m i) ∧
      ∀key : v.NarrowHead,(v.narrowHead floor key).Fits w end₀ ∧ Source (v.narrowHead floor key) (v.narrowValue R key) M (run.image m) :=by
  intro run
  have checked:=narrow_prefix_at_rank pathB rankB base₀ R m access rankFit visits prior space
  have stopLe : rank₀≤end₀:=Nat.le_add_right ..
  have lo : base₀≤rank₀:=(Nat.le_add_right ..).trans (end_le base₀ H G M D)
  have later (bank : Bank) (ok : bank.Fits w rank₀) : bank.Fits w end₀:=
    ⟨ok.1,ok.2.1,ok.2.2.trans stopLe⟩
  have mapFit' : (map₀).Fits w end₀:=⟨mapFit.1,mapFit.2.1,mapFit.2.2.trans (lo.trans stopLe)⟩
  have realMap (j : Row K G M) :
      run.image m ((map₀).base+(row K G M j).val)=(DepotRAM.Material.Route.index H v.materialPitch j:Computability.VPVNP.BurstRAM.Word w) :=
    (checked.2.1 _ (.inl ((Nat.add_lt_add_left ((row K G M j).isLt.trans_le cap) _).trans_le mapFit.2.2))).trans (ix j)
  refine ⟨checked.1,checked.2.1,?_⟩
  rintro (i|p)
  · obtain ⟨⟨p,d⟩,rfl⟩:=finProdFinEquiv.surjective i
    let hdr:=DescentDatedSourcePathDirectory.chart base₀ H G M p d
    have pre:=geometry base₀ p d (stopLe.trans_lt space)
    have geo : Readable hdr 1 H G M b w end₀:=⟨fun bank mem=>later bank (pre.fit bank mem),pre.ranks,pre.starts,pre.cuts,pre.repeats⟩
    have data:=checked.2.2.1 p d
    let key : v.NarrowHead := .inl (finProdFinEquiv (p,d))
    have headAt : v.narrowHead floor key = DepotRAM.Material.Route.lift (map₀) (H*chunks G M)
        (DescentSharedLeafLookup.source hdr (0:Fin 1)) := by
      simp only [key,narrowHead,previousPathHead,Equiv.symm_apply_apply,hdr]
    have valueAt : v.narrowValue R key = fun (h : Fin K) (_ : Fin G) =>
        (DepotRAM.Material.Route.receiver H v.materialPitch h).elim 0
          (fun z => DescentDatedSourcePathDirectory.token R z p d) := by
      funext h g
      simp only [key,narrowValue,Equiv.symm_apply_apply]
    change (v.narrowHead floor key).Fits w end₀ ∧ Source (v.narrowHead floor key) (v.narrowValue R key) M (run.image m)
    rw [headAt,valueAt]
    exact ⟨narrow_mapped_fits geo mapFit', DescentDatedSourcePathDirectory.source base₀ p d R (run.image m) end₀
      v.materialPitch hdr (map₀) rfl geo data.1 data.2 mapFit' cap safe realMap⟩
  · have data:=checked.2.2.2 p
    exact ⟨narrow_mapped_fits data.1 mapFit',Local.source base₀ p R (run.image m) end₀ v.materialPitch (map₀)
      data.1 (checked.2.2.1 p 0).1 data.2.2 mapFit' cap safe realMap⟩

theorem narrow_heads_after_rank {w : ℕ} (m : Memory w) (R : Fin H → Fin D → Option (Fin H))
    (access : Fits pathB H P₀ base₀ w) (rankFit : DescentOrdinaryDonorRankDirectory.Fits rankB base₀ H P₀ w)
    (visits : DescentDatedSourcePathDirectory.Reads pathB (Gather.reaching R) m)
    (prior : DescentOrdinaryDonorRankDirectory.Reads R rankB m)
    (space : end₀<2^w) (safe : H*chunks G M<2^w) (mapFit : (map₀).Fits w base₀) (cap : K*chunks G M≤(map₀).size)
    (ix : ∀j : Row K G M,m ((map₀).base+(row K G M j).val)=(DepotRAM.Material.Route.index H v.materialPitch j:Computability.VPVNP.BurstRAM.Word w)) :
    let run:=(v.operandPaths floor w).seq (v.operandRankPhase floor w)
    run.Runs m ∧ (∀i,i<base₀ ∨ end₀ ≤ i → run.image m i=m i) ∧
      ∀key : v.NarrowHead,(v.narrowHead floor key).Fits w end₀ ∧ Source (v.narrowHead floor key) (v.narrowValue R key) M (run.image m) :=by
  have low : base₀≤rank₀:=(Nat.le_add_right ..).trans (end_le base₀ H G M D)
  have path:=all_issued pathB base₀ access ((show rank₀≤end₀ from Nat.le_add_right ..).trans_lt space) R m visits
  have kept:=saved_directory R rankB rankFit prior (fun i hi=>path.2.1 i (.inl hi))
  have lift {bank : Bank} (h : bank.Fits w base₀) : bank.Fits w rank₀:=⟨h.1,h.2.1,h.2.2.trans low⟩
  exact v.narrow_heads_from_local floor m R access
    ⟨lift rankFit.endpoints,lift rankFit.localFit,rankFit.endpointsSize,rankFit.localSize,rankFit.sentinel⟩
    visits kept space safe mapFit cap ix

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
