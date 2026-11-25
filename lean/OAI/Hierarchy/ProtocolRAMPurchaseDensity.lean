import OAI.Hierarchy.ProtocolRAMPurchaseCapacity
import OAI.Hierarchy.ProbeMarkCounts

namespace OAI
/-! # Positive density in the decision words actually returned by the processor -/

namespace Hierarchy.ProtocolRAM.PurchaseCT
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe Filter
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {z d k : ℕ}

abbrev Tile (z d : ℕ) := Σ _ : StageAt z d, Fin (2^z)

/-- Read a signed inventory word at the caller's stock base. -/
def stockBits (base k : ℕ) (raw : Memory (wordBits z d copies)) (v : Tile z d) (a : Fin k × Bool) :=
  PurchaseInventory.stock base raw (.inr ((v.2,stageNumber v.1),a))

def strataAt (base : ℕ) (table : Bank) (k : ℕ) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (raw : Memory (wordBits z d copies)) (t : StageAt z d) (j : Fin (2*k)) :=
  PurchaseMarks.stratum (n:=2^z) phase T kind table (PurchaseInventory.bank base z (stageNumber t)) raw j

/-- A frozen inventory at any base and any public threshold-table width
has enough distinct marked tiles when the energy bound holds on its actual words. -/
theorem measured_coverage_at (base : ℕ) (table : Bank) (k : ℕ) (hk : 0<k) (phase : PhasePrice)
    (T : ℝ) (kind : ℕ) (raw : Memory (wordBits z d copies))
    (positive : 0<T) (time : 0≤phase.time) (early : phase.time≤1)
    (small : ∀ v a,stockBits base k raw v a<table.size)
    (cap : ∀ v a,rise phase.M (phase.quote kind (stockBits base k raw v a))≤1)
    (energy : (Fintype.card (Tile z d):ℝ) ≤ ∑ v, ∑ a, phase.time*
      (rise phase.M (phase.quote kind (stockBits base k raw v a))/T)^2) :
    T^2/(4*k)*((permutationFabric z d).shapes.length*(2:ℝ)^z) ≤
      ∑ t,∑ j,((strataAt base table k phase T kind raw t j).card:ℝ) := by
  let axis := PurchaseMarks.signedDirection k
  let strata := strataAt base table k phase T kind raw
  let together := fun a : Fin k × Bool => Finset.univ.sigma (fun t => strata t (axis.symm a))
  have covers (v : Tile z d) (qualifies : ∃ a,1/(4*(k:ℝ))≤phase.time*
      (rise phase.M (phase.quote kind (stockBits base k raw v a))/T)^2) : ∃ a,v∈together a := by
    obtain ⟨a,test⟩ := qualifies
    let stock := PurchaseInventory.bank base z (stageNumber v.1) (k:=k)
    let j := axis.symm a
    have read := PurchaseInventory.read base (stageNumber v.1) j v.2 raw
      ((height_extent z d).trans (extent_word z d copies).le)
    have addr : ((stock j).read raw (v.2.val:Word _)).val=stockBits base k raw v a := by
      simpa [stock,stockBits,j,axis] using read
    have hit : PurchaseMarks.tested phase T kind table stock raw (v.2.val:Word _) j=true := by
      simp only [PurchaseMarks.tested,addr,Nat.mod_eq_of_lt (small v a),PurchaseMarks.eligible,decide_eq_true_iff]
      exact test
    obtain ⟨j',found⟩ := (PurchaseMarks.exists_stratum_iff phase T kind table stock raw v.2).mpr ⟨j,hit⟩
    exact ⟨axis j',Finset.mem_sigma.mpr ⟨Finset.mem_univ _,by simpa [together,strata,strataAt,stock] using found⟩⟩
  have bound := stratum_count hk time early positive (fun v a=>phase.quote kind (stockBits base k raw v a)) cap energy together covers
  have number : ∀ a, ((together a).card:ℝ) = ∑ t,((strata t (axis.symm a)).card:ℝ) := by
    intro a; simp [together,Finset.card_sigma]
  simp_rw [number] at bound
  rw [Finset.sum_comm] at bound
  have reindex (t : StageAt z d) : (∑ a : Fin k × Bool,((strata t (axis.symm a)).card:ℝ)) =
      ∑ j, ((strata t j).card:ℝ) := axis.symm.sum_comp (fun j => ((strata t j).card:ℝ))
  simp_rw [reindex] at bound
  simpa [Tile,StageAt,Fintype.card_sigma,strata] using bound

def actualBits (k : ℕ) (raw : Memory (wordBits z d copies)) (v : Tile z d) (a : Fin k × Bool) :=
  stockBits (heapEnd z d copies) k raw v a

def markedRows (k extra depth : ℕ) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (raw : Memory (wordBits z d copies)) (t : StageAt z d) (j : Fin (2*k)) :=
  let c := config k extra depth t
  PurchaseMarks.stratum (n:=2^z) phase T kind c.threshold c.stock raw j

/-- The energy is evaluated directly on the exact quotes of global inventory words. -/
theorem measured_coverage (k extra depth : ℕ) (hk : 0<k) (phase : PhasePrice) (T : ℝ) (kind : ℕ)
    (raw : Memory (wordBits z d copies)) (positive : 0<T) (time : 0≤phase.time) (early : phase.time≤1)
    (small : ∀ v a,actualBits k raw v a<2^(z+extra))
    (cap : ∀ v a,rise phase.M (phase.quote kind (actualBits k raw v a))≤1)
    (energy : (Fintype.card (Tile z d):ℝ) ≤ ∑ v, ∑ a, phase.time*
      (rise phase.M (phase.quote kind (actualBits k raw v a))/T)^2) :
    T^2/(4*k)*((permutationFabric z d).shapes.length*(2:ℝ)^z) ≤
      ∑ t,∑ j,((markedRows k extra depth phase T kind raw t j).card:ℝ) := by
  exact measured_coverage_at (heapEnd z d copies)
    ⟨heapEnd z d copies+PurchaseInventory.footprint z (2*rounds d+1) k,z+extra⟩
    k hk phase T kind raw positive time early small cap energy

def bought (S : PurchaseSampler) (t : StageAt z d) (c : PassConfig k) (m : Memory (wordBits z d copies)) :=
  (PurchaseStage.flags (PurchaseStage.layout (embedded S t c) (sign S t c) (2^z) c.depth) m).count true

/-- The same sampler serves all input permutations and all sufficiently large
record heights. Every summand in the lower bound counts actual native decision
words from the designated signed-stage run. -/
theorem acquire (d k extra depth : ℕ) (hd : 1≤d) (hk : 0<k) (T : ℝ) (positive : 0<T) :
    ∃ S : PurchaseSampler, ∀ᶠ z : ℕ in atTop, ∀ (π : Equiv.Perm (Fin (2^z))) (raw : Memory (wordBits z d copies))
      (phase : PhasePrice) (kind : ℕ), (∀ i:Fin (2^z),raw i.val=((π i).val:Word _)) →
      0≤phase.time → phase.time≤1 → (∀ v a, actualBits k raw v a<2^(z+extra)) →
      (∀ v a,rise phase.M (phase.quote kind (actualBits k raw v a))≤1) →
      ((Fintype.card (Tile z d):ℝ) ≤ ∑ v, ∑ a, phase.time*(rise phase.M (phase.quote kind (actualBits k raw v a))/T)^2) →
      ∃ out : StageAt z d → Fin (2*k) → Memory (wordBits z d copies),
        (∀ t j,let c:=config k extra depth t; (program S t c j).Exec (initial S t c phase T kind raw)
          (out t j) (costEnvelope d S.degree depth k 1*2^z)) ∧
        T^2/(4*k)*((permutationFabric z d).shapes.length*(2:ℝ)^z)/(2*(depth+1:ℕ)) ≤
          ∑ t, ∑ j,(bought S t (config k extra depth t) (out t j):ℝ) := by
  let : Nonempty (Fin (2*k)) := ⟨⟨0,by omega⟩⟩
  have kpos : (0:ℝ)<k := by exact_mod_cast hk
  obtain ⟨S,enough⟩ := advised_purchases_linear (C:=Fin (2*k)) hd depth (β:=T^2/(4*k)) (by positivity)
  refine ⟨S,?_⟩
  filter_upwards [enough,eventual_run d k extra depth hd S] with z density cpu
  intro π raw phase kind reads time early small cap energy
  let sets := markedRows k extra depth phase T kind raw
  have many := measured_coverage k extra depth hk phase T kind raw positive time early small cap energy
  have estimate := density π sets many
  choose result runs count left using fun (t : StageAt z d) (j : Fin (2*k)) => cpu t j phase T kind π raw reads
  refine ⟨result,runs,?_⟩
  calc
    _ ≤ ∑ t, ∑ j, ((advisedPurchases S π t depth (sets t j)).1.length:ℝ) := estimate
    _ = _ := by
      apply Finset.sum_congr rfl; intro t _; apply Finset.sum_congr rfl; intro j _
      exact_mod_cast (count t j).symm

end
end Hierarchy.ProtocolRAM.PurchaseCT

end OAI
