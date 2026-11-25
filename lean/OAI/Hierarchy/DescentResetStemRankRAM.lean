import OAI.Hierarchy.DescentPeerRankWork
import OAI.Hierarchy.DescentResetSourceClassRAM
import OAI.Hierarchy.DescentResetStemCompactOrder

namespace OAI
/-! # Computing the genuine group and host ordinals for stem chronology -/
namespace Hierarchy.DescentResetStemCompactOrder
open DescentFallbackRankRAM DescentFallbackLeafScan DescentSortedRoster ProtocolRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open DescentSixParty DescentSixParty.GroupStage DescentIssuedFallbackPanel DescentSharedCableNames.Stage
open DescentCompiler DescentGL DescentColonies DescentHostDirectory DescentPacking
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {w : ℕ}

def orderAt {pitch N : ℕ} (data : Fin N→Option (Fin pitch)) (q : Fin pitch) :=
  before (fun _ : Fin pitch=>data) q q

/-- The previous coarse cell has one independent scalar directory per group,
shared by all host rows; the physical neighbor directory has one per host,
shared by all groups. Ranks discard duplicate inputs and its marker word. -/
theorem rankSources {pitch rows cols : ℕ} (data : Fin rows→Fin cols→Option (Fin pitch)) (src : Fin cols→Expr)
    (query : Expr) (out : Bank) (mem : Memory w) (targetAt : Fin rows→Fin pitch)
    (small : pitch<2^w) (_wide : cols<2^w) (fits : ∀j,(src j).Fits w out.base)
    (qFit : query.Fits w out.base) (space : out.base+rows<2^w)
    (read : ∀r : Fin rows,∀i,(src i).eval mem (r.val:Word w)=(DescentPackedColony.target (data r i):Word w))
    (wanted : ∀r : Fin rows,(query.eval mem (r.val:Word w)).val=(targetAt r).val) :
    let op:=calculate src query
    let done:=image out.base rows op mem
    let code:=scan w out.base rows op
    code.Exec mem done (4+rows*(2*op.work+4)) ∧
      (∀r : Fin rows,done (out.base+r.val)=(orderAt (data r) (targetAt r):Word w)) ∧
      (∀x,x<out.base ∨ out.base+rows≤x→done x=mem x) ∧
      DescentStaticWordColumn.names code=11+4*op.work ∧ CheapCode code := by
  intro op done code
  refine ⟨scan_exec _ _ _ _ (DescentResetSourceClassRAM.rank_fits src query fits qFit) space,?_,?_,DescentStaticWordColumn.names_scan ..,@scan_cheap _ _ _ _⟩
  · intro r
    exact (ProtocolRAMGeneratedWrite.read_image out.base rows op mem r).trans
      (rank_read (fun _=>data r) mem (r.val:Word w) src (targetAt r) small (read r) query (targetAt r) (wanted r))
  · intro x away
    exact ProtocolRAMGeneratedWrite.frame_image out.base rows op mem x away


theorem orderAt_read {pitch N : ℕ} (data : Fin N→Option (Fin pitch)) (xs : Finset ℕ)
    (has : ∀t : Fin pitch,t.val∈xs ↔ ∃j,data j=some t) (range : ∀a∈xs,a<pitch) (q : Fin pitch) :
    orderAt data q=compress xs q.val := by
  let all:=present (fun _ : Fin pitch=>data) q
  have exactSet : all.map Fin.valEmbedding=xs := by
    ext a
    constructor
    · intro yes;obtain ⟨t,seen,rfl⟩:=Finset.mem_map.mp yes
      exact (has t).mpr (Finset.mem_filter.mp seen).2
    · intro yes
      let t : Fin pitch:=⟨a,range a yes⟩
      exact Finset.mem_map.mpr ⟨t,Finset.mem_filter.mpr ⟨Finset.mem_univ _,(has t).mp yes⟩,rfl⟩
  rw [←exactSet]
  simp only [compress,Finset.filter_map,Finset.card_map,orderAt,before,all]; rfl

variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V]
    {groups d k m c rows : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k)
variable (digits : Block m≃Fin groups×Block k) (basis : Layout m) (fits : c≤ m) (vertex : V↪Fin (Fintype.card V))
local notation "L" => 2^(m-c)

def groupRows (v : V) (hi : Block c) (j : Fin L) : Option (Fin groups) := some (donor digits basis fits v hi j).1.1

omit [Fintype V] [DecidableEq V] in
theorem group_read (v : V) (hi : Block c) (u : Fin groups) :
    orderAt (groupRows digits basis fits v hi) u=compress (groupDomain digits basis fits v hi) u.val := by
  apply orderAt_read
  · intro t
    constructor
    · intro yes;obtain ⟨j,_,eqn⟩:=Finset.mem_image.mp yes
      exact ⟨j,congrArg some (Fin.ext eqn)⟩
    · rintro ⟨j,hit⟩
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,congrArg Fin.val (Option.some.inj hit)⟩
  · intro a yes
    obtain ⟨j,_,rfl⟩:=Finset.mem_image.mp yes
    exact (donor digits basis fits v hi j).1.1.isLt

theorem host_read {N : ℕ} (v : V) (data : Fin N→Option (Fin (Fintype.card V))) (u : Fin (Fintype.card V))
    (seen : ∀z, (∃j,data j=some z) ↔ ∃h∈insert v (A.near v),vertex h=z) :
    orderAt data u=compress (hostDomain A vertex v) u.val := by
  apply orderAt_read
  · intro target
    rw [seen]
    constructor
    · intro yes;obtain ⟨h,hm,eqn⟩:=Finset.mem_image.mp yes
      exact ⟨h,hm,Fin.ext eqn⟩
    · rintro ⟨h,hm,rfl⟩
      exact Finset.mem_image.mpr ⟨h,hm,rfl⟩
  · intro a yes
    obtain ⟨h,_,rfl⟩:=Finset.mem_image.mp yes
    exact (vertex h).isLt

end
end Hierarchy.DescentResetStemCompactOrder

end OAI
