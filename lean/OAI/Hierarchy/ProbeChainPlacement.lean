import OAI.Hierarchy.ProbeChainStrip
import OAI.Hierarchy.ProbeLiveActivation

namespace OAI
/-! # Place each H-strip's finite-test wires at their actual stage sockets -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe ChainStrip
open scoped Classical
noncomputable section

abbrev StageColumns (h d : ℕ) := Σ t : StageAt h d,
  (stageAt h d t).Group × (Fin (stageAt h d t).span ⊕ Fin (stageAt h d t).span)

variable {h d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : StageAt h d → (Fin k × Bool) → Finset (Fin (2^h)))

/-- The syntactic column of the finite spectral format is mounted exactly at its
live input or output socket. The numerical ordinals interleave inputs and outputs. -/
def stripPlace (path : LiveChains S π depth marked) : Columns depth ↪ StageColumns h d := by
  let p := advisedStage h d π path.1
  let row := liveRow S π depth marked path
  let take (i : Columns depth) : Fin (depth+1) := ⟨i.val.val/2,by have bound := i.val.isLt; dsimp [edgeCount] at bound; omega⟩
  let socket (i : Columns depth) : Fin (stageAt h d path.1).span ⊕ Fin (stageAt h d path.1).span :=
    if i.val.val%2=0 then .inl (p.input (row (take i))) else .inr (p.output (row (take i)))
  let γ := p.group (row 0)
  have chart (j : Fin (depth+1)) : p.group (row j)=γ := (live_in_ball S π depth marked path j).1
  have single : Function.Injective row := by
    intro i j eq
    have both := (liveDigit S π depth marked path.1 path.2.1).injective eq
    exact congrArg Prod.snd both
  refine ⟨fun i => ⟨path.1,γ,socket i⟩,?_⟩
  intro i j place
  have eq : socket i=socket j := congrArg Prod.snd (eq_of_heq (Sigma.mk.inj_iff.mp place).2)
  apply Subtype.ext; apply Fin.ext
  by_cases ei : i.val.val%2=0 <;> by_cases ej : j.val.val%2=0
  · have inv := Sum.inl.inj (by simpa only [socket,ite_eq_left ei,ite_eq_left ej] using eq)
    have same := single (p.input_inj (Prod.ext ((chart _).trans (chart _).symm) inv))
    have div := congrArg Fin.val same
    change i.val.val/2=j.val.val/2 at div; omega
  · simp only [socket,ite_eq_left ei,ite_eq_right ej,Sum.inl_ne_inr] at eq
  · simp only [socket,ite_eq_right ei,ite_eq_left ej,Sum.inr_ne_inl] at eq
  · have inv := Sum.inr.inj (by simpa only [socket,ite_eq_right ei,ite_eq_right ej] using eq)
    have same := single (p.output_inj (Prod.ext ((chart _).trans (chart _).symm) inv))
    have div := congrArg Fin.val same
    change i.val.val/2=j.val.val/2 at div; omega

theorem stripPlace_in (path : LiveChains S π depth marked) (j : Fin (depth+1)) :
    let p := advisedStage h d π path.1
    let row := liveRow S π depth marked path
    stripPlace S π depth marked path (inlet depth j) = ⟨path.1,p.group (row 0),.inl (p.input (row j))⟩ := by
  intro p row
  let v : Fin (depth+1) := ⟨(2*j.val)/2,by have := j.isLt; omega⟩
  change (⟨path.1,p.group (row 0),if (2*j.val)%2=0 then Sum.inl (p.input (row v)) else Sum.inr (p.output (row v))⟩ : StageColumns h d) = _
  have digit : v=j := Fin.ext (by dsimp [v]; omega)
  rw [ite_eq_left (by omega),digit]

theorem stripPlace_out (path : LiveChains S π depth marked) (j : Fin (depth+1)) :
    let p := advisedStage h d π path.1
    let row := liveRow S π depth marked path
    stripPlace S π depth marked path (outlet depth j) = ⟨path.1,p.group (row 0),.inr (p.output (row j))⟩ := by
  intro p row
  let v : Fin (depth+1) := ⟨(2*j.val+1)/2,by have := j.isLt; omega⟩
  change (⟨path.1,p.group (row 0),if (2*j.val+1)%2=0 then Sum.inl (p.input (row v)) else Sum.inr (p.output (row v))⟩ : StageColumns h d) = _
  have digit : v=j := Fin.ext (by dsimp [v]; omega)
  rw [ite_eq_right (by omega),digit]

/-- Axis/end labels go to identically named physical layers. This is the genuine
site embedding accepted by `Packet.named_histogram`, including all zero-load layers. -/
def stripSites (path : LiveChains S π depth marked) : ColumnSite (Columns depth) k ↪ ColumnSite (StageColumns h d) k :=
  (stripPlace S π depth marked path).prodMap (Function.Embedding.refl _)

/-- Read a tile's altimeter at exactly the full physical stock address, allowing prices
of different signed axes to change independently across chronological repairs. -/
def postQuote (path : LiveChains S π depth marked)
    (post : Commodity (Fin (2^h)) (permutationFabric h d).shapes.length k → ℝ) (i : Axes depth k) :=
  post (.inr ((liveRow S π depth marked path i.1,path.1),i.2))

/-- Mounting the same shape on each purchased path gives one M threshold and one ε
for all h, π, live paths, and integer stock values. This is the direct mathematical
producer of `ChainFrame` values used in `live_activation`. -/
theorem physical_chain_frames {F : Type*} [Field F] [SiteNaming (ColumnSite (Columns depth) k)] (hk : 0<k) (no : ¬HasSpectralFlat F (k+1))
    {η : ℝ} (tol : 0<η) : ∃ M₀ : ℕ, ∀ M : ℝ, 0<M → M₀≤M → ∃ ε : ℝ, 0<ε ∧
    ∀ path : LiveChains S π depth marked, ∀ post, (∀ j, 0≤postQuote S π depth marked path post j ∧ postQuote S π depth marked path post j≤M+1) →
      Probe.discrepancy F (wires depth k) (demands depth k) (prices depth k M (postQuote S π depth marked path post)) ≤ ε →
      Nonempty (ChainFrame S π depth marked path M η post) := by
  obtain ⟨N,uniform⟩ := frames (F:=F) depth k hk no tol
  refine ⟨N,?_⟩; intro M pos large
  obtain ⟨ε,ep,test⟩ := uniform M pos large
  refine ⟨ε,ep,?_⟩; intro path post box pass
  have bounds : postQuote S π depth marked path post ∈ Set.Icc (0:Axes depth k → ℝ) (fun _ => M+1) :=
    ⟨fun i => (box i).1,fun i => (box i).2⟩
  obtain ⟨zi,zo,joined,each,probe⟩ := test _ bounds pass
  exact ⟨⟨zi,zo,joined,fun i => (each (i,path.2.1)).le,probe.le⟩⟩

end
end Hierarchy.ProbeStage

end OAI
