import OAI.Hierarchy.DescentAffineCanonical
import OAI.Hierarchy.DescentChosenOccupied
import OAI.Hierarchy.DescentChosenShrink
import OAI.Hierarchy.DescentIntegralSiteLoad
import OAI.Hierarchy.DescentStageHistory
import OAI.Hierarchy.DescentHostDegree

namespace OAI
/-! # One measured shrink stage from the old graph and the scanned addresses -/

namespace Hierarchy.DescentSixParty.StarKeys
open DescentPacking DescentColonies DescentGL DescentWalshTables Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

variable {F : Type*} [Field F] {d k : ℕ} {P : Type*} {bits : P→ℕ}
variable {V : Type} [Fintype V] [DecidableEq V] {Atoms : Type*}
variable (A : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (pos : A.graph.Site→V) (blk : A.graph.Site→Block k) (hub : A.graph.Site→Bool)
variable (rec : A.graph.Site→List Atoms) (wire hist z cap Δ : ℕ) (near : V→Finset V)
local notation "full" => A.siteUnits hub rec wire 256 hist
local notation "unit" => (wire*(z*G.b))
local notation "D" => DescentHostDegree.gap Δ
local notation "a" => DescentHostDegree.packExponent 20 Δ

private theorem univ_eq_of_fintypes {ι : Type*} (left right : Fintype ι) :
    @Finset.univ ι left = @Finset.univ ι right :=
  congrArg (fun inst : Fintype ι => @Finset.univ ι inst) (Subsingleton.elim left right)

/-- The finite history returned by the scan retains the actual multiplier,
affine color, native paired edges and their profile assignment. Later
placements may read this graph and the locators of every physical gadget vertex. -/
def IsScannedAt (hk : 0<k) (small : ∀v i,blockMass A.graph pos blk full v i≤unit*cap)
    (H : Histories F d P bits) (μ : Nonzero k) (α : DescentWalshTables.Bits k) (β : ZMod 2) : Prop :=
    let score := fun m : Nonzero k=>colonyCount
      (fun _ : Unit=>blockMass A.graph pos blk full) (fun v w=>w∈near v)
      a (unit*cap) Δ (fun _=>small) (multiplier hk m)
    (scanMinimum score (nonzeroWords k)).1=some (μ,score μ) ∧
    let L := multiplier hk μ
    let blocks := reindexedBlock A.graph blk L
    let fits := small_reindexed A.graph pos blk full small L
    let home := occupiedHome A.graph pos blocks full near D a (unit*cap) fits
    let color := fun v=>decide (binaryRow α ((address k).symm (blocks v))+β=0)
    let I := NativePair A.graph A.core home color cap
    let pick := colorPick A.graph A.core home color cap
    ∃ (hz : 0<z) (fit : ∀(i : I) s,A.graph.width (pick (i,s))=z*G.b)
      (profile : H.Choice ≃ (I→Profile G.C)),
      ∀ c,H.state c=A.selected G pick (fun _=>z) (fun _=>hz) fit
        (coloredPack A.graph A.core home color cap) (profile c)

/-- A history with some scanned multiplier and affine color. -/
def IsScanned (hk : 0<k) (small : ∀v i,blockMass A.graph pos blk full v i≤unit*cap)
    (H : Histories F d P bits) : Prop :=
  ∃ (μ : Nonzero k) (α : DescentWalshTables.Bits k) (β : ZMod 2),
    IsScannedAt A G pos blk hub rec wire hist z cap Δ near hk small H μ α β ∧
      FirstPaint A.graph A.core pos (reindexedBlock A.graph blk (multiplier hk μ)) full near D a cap unit
        (small_reindexed A.graph pos blk full small (multiplier hk μ)) (DescentAffineColors.code α β)

set_option maxHeartbeats 1200000 in
/-- Both discrete choices act on the original adjacency and integer load columns.
Each resulting physical profile has a separately bounded core and tether invoice;
its coefficient occurs with exactly unit weight in the finite expansion. -/
theorem scanned_shrink_named_of_bound (hk : 0<k) (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ)
    (hw : 0<wire) (hz : 0<z) (hc : 0<cap)
    (small : ∀v i,blockMass A.graph pos blk full v i≤unit*cap)
    (adj : ∀e∈A.core,pos (A.graph.dst e)∈near (pos (A.graph.src e)))
    (rev : ∀e∈A.core,pos (A.graph.src e)∈near (pos (A.graph.dst e)))
    (same : ∀e∈A.core,blk (A.graph.src e)=blk (A.graph.dst e))
    (fixed : ∀e∈A.core,A.graph.width e=z*G.b)
    (inside : ∀ e∈A.core,hub (A.graph.src e)=false ∧ hub (A.graph.dst e)=false)
    (outside : ∀ e∉A.core,hub (A.graph.src e)≠hub (A.graph.dst e))
    (q ε : ℝ) (hq : 0<q) (he : 0≤ε)
    (retain : (q*hist)*(∑v,((rec v).length:ℝ))≤ε)
    (slack : (Fintype.card V:ℝ)*((2:ℝ)^a*(q*(unit*cap:ℕ)))≤ε)
    (μ : Nonzero k)
    (selected :
      let score := fun m : Nonzero k =>
        colonyCount (fun _ : Unit => blockMass A.graph pos blk full) (fun v w => w∈near v)
          a (unit*cap) Δ (fun _ => small) (multiplier hk m)
      (scanMinimum score (nonzeroWords k)).1=some (μ,score μ))
    (α : DescentWalshTables.Bits k) (β : ZMod 2)
    (balanced : affineBalance A.graph A.core pos (reindexedBlock A.graph blk (multiplier hk μ))
      full near D a cap unit (small_reindexed A.graph pos blk full small (multiplier hk μ)) α β) :
    ∃ H : Histories.{_, _, 0} F d P bits,
      IsScannedAt A G pos blk hub rec wire hist z cap Δ near hk small H μ α β ∧(∀ x,H.value x=A.value x) ∧ (∀ c,H.weight c=1) ∧
      ∀ c,(H.state c).tetherWidth ≤ A.tetherWidth ∧
        (q*wire)*(H.state c).liveWidth ≤ (1-(2-G.rate)/4)*((q*wire)*A.liveWidth)+
          (2-G.rate)*((257*((q*wire)*A.tetherWidth)+ε)/4) := by
  have hb := G.base_pos
  have posUnit : 0<unit := by positivity
  have two : 2≤2^a := Nat.le_trans (by decide : 2≤2^20)
    (Nat.pow_le_pow_right (by decide) (by unfold DescentHostDegree.packExponent; omega))
  obtain ⟨μ₀,minimum,count⟩ := chosen_occupied_colonies A.graph pos blk full hk near a (unit*cap) Δ
    small degree branch (by positivity) two
  have found : μ₀=μ := congrArg Prod.fst (Option.some.inj (minimum.symm.trans selected))
  subst μ₀
  let L := multiplier hk μ
  let blocks := reindexedBlock A.graph blk L
  let fits := small_reindexed A.graph pos blk full small L
  let home := occupiedHome A.graph pos blocks full near D a (unit*cap) fits
  have same' (e) (h : e∈A.core) : blocks (A.graph.src e)=blocks (A.graph.dst e) :=
    reindexed_preserves A.graph blk (same e h)
  have cover v : unit*live (nativeTraffic A.graph A.core home) v≤full v :=
    A.siteUnits_outgoing hub rec wire 256 hist home unit (fun e he=>by rw [fixed e he]) (by decide) v
  have mass := A.siteUnits_density hub rec wire 256 hist q hq a (unit*cap)
  have scale : q*(unit*cap:ℕ)=(q*wire)*(z*G.b:ℕ)*cap := by push_cast;ring
  rw [mass,scale] at count
  rw [scale] at slack
  obtain ⟨fit,conserve,invoice⟩ := chosen_shrink_of_bound A G pos blocks full near D a cap unit fits
    Δ degree posUnit cover adj rev same' z hz fixed (q*wire) (by positivity) hub rec 256 (q*hist) ε
    (Fintype.card V) he (by norm_num) hc inside outside retain (DescentHostDegree.pack_cutoff Δ)
    slack count α β balanced
  let color := fun v=>decide (binaryRow α ((address k).symm (blocks v))+β=0)
  let I := NativePair A.graph A.core home color cap
  let pick := colorPick A.graph A.core home color cap
  let family := A.selected G pick (fun _=>z) (fun _=>hz) fit (coloredPack A.graph A.core home color cap)
  let H : Histories.{_, _, 0} F d P bits := ⟨I→Profile G.C,inferInstance,family,fun _=>1⟩
  refine ⟨H,⟨selected,hz,fit,Equiv.refl _,fun _=>rfl⟩,fun x=>?_,fun _=>rfl,fun c=>?_⟩
  · change (∑ c : I → Profile G.C, (1:F) * (family c).value x) = A.value x
    simp only [one_mul]
    refine Eq.trans (Finset.sum_congr ?_ ?_) (conserve x)
    · exact univ_eq_of_fintypes _ _
    · intro c _
      rfl
  · change (family c).tetherWidth ≤ A.tetherWidth ∧
      (q*wire)*(family c).liveWidth ≤ (1-(2-G.rate)/4)*((q*wire)*A.liveWidth)+
        (2-G.rate)*((257*((q*wire)*A.tetherWidth)+ε)/4)
    have bill := invoice c
    norm_num only at bill
    refine ⟨?_, ?_⟩
    · exact bill.1
    · convert bill.2 using 1; first | rfl

set_option maxHeartbeats 1200000 in
/-- Both discrete choices act on the original adjacency and integer load columns.
Each resulting physical profile has a separately bounded core and tether invoice;
its coefficient occurs with exactly unit weight in the finite expansion. -/
theorem scanned_shrink_named (hk : 0<k) (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ)
    (hw : 0<wire) (hz : 0<z) (hc : 0<cap)
    (small : ∀v i,blockMass A.graph pos blk full v i≤unit*cap)
    (adj : ∀e∈A.core,pos (A.graph.dst e)∈near (pos (A.graph.src e)))
    (rev : ∀e∈A.core,pos (A.graph.src e)∈near (pos (A.graph.dst e)))
    (same : ∀e∈A.core,blk (A.graph.src e)=blk (A.graph.dst e))
    (fixed : ∀e∈A.core,A.graph.width e=z*G.b)
    (inside : ∀ e∈A.core,hub (A.graph.src e)=false ∧ hub (A.graph.dst e)=false)
    (outside : ∀ e∉A.core,hub (A.graph.src e)≠hub (A.graph.dst e))
    (q ε : ℝ) (hq : 0<q) (he : 0≤ε)
    (retain : (q*hist)*(∑v,((rec v).length:ℝ))≤ε)
    (slack : (Fintype.card V:ℝ)*((2:ℝ)^a*(q*(unit*cap:ℕ)))≤ε) :
    ∃ H : Histories.{_, _, 0} F d P bits,
      IsScanned A G pos blk hub rec wire hist z cap Δ near hk small H ∧(∀ x,H.value x=A.value x) ∧ (∀ c,H.weight c=1) ∧
      ∀ c,(H.state c).tetherWidth ≤ A.tetherWidth ∧
        (q*wire)*(H.state c).liveWidth ≤ (1-(2-G.rate)/4)*((q*wire)*A.liveWidth)+
          (2-G.rate)*((257*((q*wire)*A.tetherWidth)+ε)/4) := by
  have hb := G.base_pos
  have posUnit : 0<unit := by positivity
  have two : 2≤2^a := Nat.le_trans (by decide : 2≤2^20)
    (Nat.pow_le_pow_right (by decide) (by unfold DescentHostDegree.packExponent; omega))
  obtain ⟨μ,minimum,_⟩ := chosen_occupied_colonies A.graph pos blk full hk near a (unit*cap) Δ
    small degree branch (by positivity) two
  let L := multiplier hk μ
  let blocks := reindexedBlock A.graph blk L
  let fits := small_reindexed A.graph pos blk full small L
  let home := occupiedHome A.graph pos blocks full near D a (unit*cap) fits
  have cover v : unit*live (nativeTraffic A.graph A.core home) v≤full v :=
    A.siteUnits_outgoing hub rec wire 256 hist home unit (fun e he=>by rw [fixed e he]) (by decide) v
  obtain ⟨j,first,balanced⟩ := first_paint A.graph A.core pos blocks full near D a cap unit fits posUnit cover
  let α := DescentAffineColors.linear j
  let β := DescentAffineColors.offset j
  obtain ⟨H,witness,remaining⟩ := scanned_shrink_named_of_bound A G pos blk hub rec wire hist z cap Δ near
    hk branch degree hw hz hc small adj rev same fixed inside outside q ε hq he retain slack μ minimum α β balanced
  refine ⟨H,⟨μ,α,β,witness,?_⟩,remaining⟩
  simpa only [α,β,DescentAffineColors.code_linear_offset] using first

theorem scanned_shrink (hk : 0<k) (branch : 2≤Δ) (degree : ∀v,(near v).card≤Δ)
    (hw : 0<wire) (hz : 0<z) (hc : 0<cap)
    (small : ∀v i,blockMass A.graph pos blk full v i≤unit*cap)
    (adj : ∀e∈A.core,pos (A.graph.dst e)∈near (pos (A.graph.src e)))
    (rev : ∀e∈A.core,pos (A.graph.src e)∈near (pos (A.graph.dst e)))
    (same : ∀e∈A.core,blk (A.graph.src e)=blk (A.graph.dst e))
    (fixed : ∀e∈A.core,A.graph.width e=z*G.b)
    (inside : ∀ e∈A.core,hub (A.graph.src e)=false ∧ hub (A.graph.dst e)=false)
    (outside : ∀ e∉A.core,hub (A.graph.src e)≠hub (A.graph.dst e))
    (q ε : ℝ) (hq : 0<q) (he : 0≤ε)
    (retain : (q*hist)*(∑v,((rec v).length:ℝ))≤ε)
    (slack : (Fintype.card V:ℝ)*((2:ℝ)^a*(q*(unit*cap:ℕ)))≤ε) :
    ∃ H : Histories.{_, _, 0} F d P bits,(∀ x,H.value x=A.value x) ∧ (∀ c,H.weight c=1) ∧
      ∀ c,(H.state c).tetherWidth ≤ A.tetherWidth ∧
        (q*wire)*(H.state c).liveWidth ≤ (1-(2-G.rate)/4)*((q*wire)*A.liveWidth)+
          (2-G.rate)*((257*((q*wire)*A.tetherWidth)+ε)/4) := by
  obtain ⟨H,_,paid⟩ := scanned_shrink_named A G pos blk hub rec wire hist z cap Δ near hk
    branch degree hw hz hc small adj rev same fixed inside outside q ε hq he retain slack
  exact ⟨H,paid⟩

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
