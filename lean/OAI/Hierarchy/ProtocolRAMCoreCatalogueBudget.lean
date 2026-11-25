import OAI.Hierarchy.ProbeAdvisedCost
import OAI.Hierarchy.ProtocolRAMCoreCatalogueRowBudget
import OAI.Hierarchy.ProtocolRAMCoreCatalogueSpace

namespace OAI
/-! # A fixed linear budget for all public core-decoder cells -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
open ProbeStage CoreBoard ReportSockets TaggedShorterSupergroups Filter
open scoped Classical BigOperators

theorem total_stages (h d : ℕ) : (permutationFabric h d).shapes.length=18*(d-1)+1 := by
  let π := Equiv.refl (Fin (2^h))
  have layers := (advisedRoute h d π).layer_shapes
  exact (show (advisedRoute h d π).layers.length=(permutationFabric h d).shapes.length by
    simpa only [List.length_map] using congrArg List.length layers).symm.trans (AdaptiveProbe.advised_length h d π)

theorem names_le (h d : ℕ) (hd : 1≤ d) :
    Fintype.card (AllGroups h d)≤ ReportGroupROM.words h d := by
  change Fintype.card (Σ t : StageAt h d, (stageAt h d t).Group)≤ _
  rw [Fintype.card_sigma]
  calc
    _ ≤ ∑ _ : StageAt h d, ReportGroupROM.stride h d :=
      Finset.sum_le_sum fun t _ => ReportGroupROM.size t hd
    _ = ReportGroupROM.words h d := by simp [ReportGroupROM.words]

def stagesFactor (d : ℕ) := (18*(d-1)+1)*4^(rounds d+1)
def heapFactor (d : ℕ) := (3+rounds d*Native.stride d Native.copies)*4^(rounds d+1)

theorem prefix_linear (h W : ℕ) :
    superStart h W≤ (heapFactor (2^W)+1+stagesFactor (2^W))*2^h := by
  have words : ReportGroupROM.words h (2^W)=stagesFactor (2^W)*2^h := by
    rw [ReportGroupROM.words,total_stages,ReportGroupROM.stride_eq]
    simp only [stagesFactor,Nat.mul_assoc]
  have heap : Native.heapEnd h (2^W) Native.copies=heapFactor (2^W)*2^h := Native.heap_words ..
  unfold superStart groupStart
  rw [heap,words,Nat.add_mul,Nat.add_mul,Nat.one_mul]
  exact Nat.add_le_add_right (max_le (Nat.le_add_right ..) (Nat.le_add_left ..)) _

/-- One constant works for all heights and permutations. The packed directory
is selected once from the public stage format. -/
theorem affordable_directory (S : PurchaseSampler) (W k attempts : ℕ) :
    ∃ C : ℕ, ∀ h : ℕ,
      ∀ dir : Directory (reserved h W (copies k attempts)) (2^superAddress W (2*copies k attempts) h),
        dir.groups*2^superAddress W (2*copies k attempts) h ≤
          2*(((2*rounds (2^W)+1)*4^(rounds (2^W)+1)*2^h)*copies k attempts)+
            2^superAddress W (2*copies k attempts) h →
        top h W (Fintype.card (AllGroups h (2^W))) dir.groups (2^superAddress W (2*copies k attempts) h)
          (Fintype.card (Edges S h (2^W) k))≤ C*2^h := by
  let d := 2^W
  let cp := copies k attempts
  let «prefix» := heapFactor d+1+stagesFactor d
  let volume := 2*((2*rounds d+1)*4^(rounds d+1)*cp)+2^(9*d+18*(d-1)+2+2*cp)
  let edges := coreFactor S d k
  refine ⟨2*(«prefix»+1)+4*(stagesFactor d+1)+3*volume+20*(edges+1)+2,?_⟩
  intro h dir paid
  let n := 2^h
  have npos : 1≤ n := Nat.two_pow_pos _
  have budget : dir.groups*(2^superAddress W (2*cp) h)≤ volume*n := by
    have power := packed_height W (2*cp) h
    calc
      _ ≤ 2*(((2*rounds d+1)*4^(rounds d+1)*n)*cp)+2^superAddress W (2*cp) h := paid
      _ ≤ 2*(((2*rounds d+1)*4^(rounds d+1)*n)*cp)+2^(9*d+18*(d-1)+2+2*cp)*n :=
        Nat.add_le_add_left power _
      _ = volume*n := by dsimp only [volume];ring
  have groupCount : Fintype.card (AllGroups h d)≤ stagesFactor d*n := by
    have := names_le h d (Nat.two_pow_pos _)
    simpa only [ReportGroupROM.words,total_stages,ReportGroupROM.stride_eq,stagesFactor,Nat.mul_assoc,n] using this
  have rowCount : Fintype.card (Edges S h d k)≤ edges*n := rows_linear S h W k
  have prefixCount : superStart h W≤ «prefix»*n := prefix_linear h W
  have bound := top_bound h W (Fintype.card (AllGroups h d)) dir.groups
    (2^superAddress W (2*cp) h) (Fintype.card (Edges S h d k)) (volume*n) (Nat.two_pow_pos _) budget
  calc
    _ ≤ 2*(superStart h W+1)+4*(Fintype.card (AllGroups h d)+1)+3*(volume*n)+20*(Fintype.card (Edges S h d k)+1)+2 := bound
    _ ≤ 2*(«prefix»*n+n)+4*(stagesFactor d*n+n)+3*(volume*n)+20*(edges*n+n)+2*n := by omega
    _ = _ := by change _=_*n;ring

theorem affordable_all (S : PurchaseSampler) (W k attempts : ℕ) :
    ∃ C : ℕ, ∀ h : ℕ,
      ∃ dir : Directory (reserved h W (copies k attempts)) (2^superAddress W (2*copies k attempts) h),
        top h W (Fintype.card (AllGroups h (2^W))) dir.groups (2^superAddress W (2*copies k attempts) h)
          (Fintype.card (Edges S h (2^W) k))≤ C*2^h := by
  obtain ⟨C,all⟩ := affordable_directory S W k attempts
  refine ⟨C,fun h=>?_⟩
  obtain ⟨dir,paid⟩ := purchase_stages h W (copies k attempts) (2*copies k attempts) Nat.lt_two_pow_self.le
  exact ⟨dir,all h dir paid⟩

open scoped Filter in
theorem eventually_fits (S : PurchaseSampler) (W k attempts : ℕ) :
    ∀ᶠ h : ℕ in atTop,
      ∃ dir : Directory (reserved h W (copies k attempts)) (2^superAddress W (2*copies k attempts) h),
        top h W (Fintype.card (AllGroups h (2^W))) dir.groups (2^superAddress W (2*copies k attempts) h)
          (Fintype.card (Edges S h (2^W) k))<2^Native.wordBits h (2^W) Native.copies := by
  obtain ⟨C,all⟩ := affordable_all S W k attempts
  filter_upwards [Native.eventually_append_room (2^W) Native.copies C] with h fits
  obtain ⟨dir,bound⟩ := all h
  exact ⟨dir,bound.trans_lt ((Nat.le_add_left _ _).trans_lt fits)⟩

end Hierarchy.ProtocolRAM.Calendar.CoreCatalogue
end

end OAI
