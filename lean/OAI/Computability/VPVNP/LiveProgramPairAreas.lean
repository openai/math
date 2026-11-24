import OAI.Computability.VPVNP.LiveProgramPairAuxiliary
import OAI.Computability.VPVNP.LiveLayoutWordFit
import OAI.Computability.VPVNP.LiveProgramNominationPaths

/-! # Disjoint physical arrays for preparing the auxiliary pair counter -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Auxiliary

open BurstRAM LiveAuxiliaryHeaders PrimedInputRAM
open scoped Fin.CommRing

private def starts (s : LiveHeaderSchedule.Sizes) (header counter : ℕ) : Fin 7 → ℕ :=
  ![LiveHeaderSchedule.widthAddr header .primedLeft,LiveHeaderSchedule.leftIndexBase s header,
    LiveHeaderSchedule.rightIndexBase s header,LiveHeaderSchedule.adviceBase s header,
    LiveHeaderSchedule.exteriorBase s header .left,LiveHeaderSchedule.exteriorBase s header .right,counter]

private theorem interval (s : LiveHeaderSchedule.Sizes) (header counter N : ℕ)
    (hc : LiveHeaderSchedule.limit s header ≤ counter) (i : Fin (2^s.h)) (f : Fin 7) :
    let L := PairedChain.lengths s.h s.delta s.advice i
    header ≤ starts s header counter f ∧
      (starts s header counter f + fieldSize L N f ≤ LiveHeaderSchedule.limit s header ∨
        counter ≤ starts s header counter f ∧ starts s header counter f + fieldSize L N f ≤ counter+N) := by
  let L := PairedChain.lengths s.h s.delta s.advice i
  have h₁ : L.leftCut ≤ (s.h+1)*s.delta := L.leftFit
  have h₂ : L.rightCut ≤ (s.h+1)*s.delta := L.rightFit
  rw [LiveHeaderSchedule.limit_eq] at hc ⊢
  fin_cases f <;> simp only [starts,fieldSize,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val,
    LiveHeaderSchedule.widthAddr,LiveHeaderSchedule.exteriorBase,
    LiveHeaderSchedule.adviceBase,LiveHeaderSchedule.rightIndexBase,LiveHeaderSchedule.leftIndexBase,
    LiveHeaderSchedule.populationAddr,LiveHeaderSchedule.highAddr,LiveHeaderSchedule.indexBase,
    LiveHeaderSchedule.Sizes.capacity,Fin.reduceFinMk]
  all_goals change _ ∧ (_ ∨ _ ∧ _)
  all_goals dsimp only [L,PairedChain.lengths] at h₁ h₂ ⊢
  all_goals omega

variable (G : Group)

/-- Natural base address of the live header workspace at the group geometry. -/
abbrev headerBase := Layout.header.eval G.g
/-- Natural base address of the auxiliary descriptor table at the group geometry. -/
abbrev tableBase := (Layout.descriptor G.constants).eval G.g
/-- Natural base address of the label-counter array at the group geometry. -/
abbrev counterBase := (Layout.counter G.constants).eval G.g
/-- Natural base address of the virtual RAM shadow at the group geometry. -/
abbrev shadowBase := (Layout.shadow G.constants).eval G.g
/-- Length of the nominated histogram, one word per grammar production. -/
abbrev histLength := G.constants.grammarLabels.eval G.g

theorem geometry_order :
    Layout.stageTag.eval G.g < headerBase G ∧ headerBase G ≤ tableBase G ∧
    tableBase G+21 = counterBase G ∧ counterBase G+histLength G ≤ shadowBase G := by
  have hl : tableBase G = LiveHeaderSchedule.limit (sizes G) (headerBase G) := rfl
  refine ⟨Nat.lt_succ_self _,?_,rfl,?_⟩
  · rw [hl,LiveHeaderSchedule.limit_eq]; omega
  · simp only [shadowBase,Layout.shadow,Layout.orderMap,Layout.packedPrefix,Layout.adviceFrames,
    Layout.transitionScratch,Layout.newState,Layout.oldState,Constants.labels,eval_add,
      counterBase,histLength]
    omega

/-- Motif counters follow the grammar counters in the same live array. -/
theorem counter_end_le_shadow :
    counterBase G + G.constants.labels.eval G.g ≤ shadowBase G := by
  simp only [shadowBase,Layout.shadow,Layout.orderMap,Layout.packedPrefix,Layout.adviceFrames,
    Layout.transitionScratch,Layout.newState,Layout.oldState,eval_add,counterBase]
  omega

/-- The untruncated public addresses used by all three preparation stages. -/
theorem address_values (hs : shadowBase G < 2^G.w) :
    G.addr.val = Layout.stageTag.eval G.g ∧ (desc G).val = tableBase G ∧
      (counter G).val = counterBase G ∧ (shadow G).val = shadowBase G := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := geometry_order G
  exact ⟨Nat.mod_eq_of_lt (show Layout.stageTag.eval G.g < 2^G.w by omega),
    Nat.mod_eq_of_lt (show tableBase G < 2^G.w by omega),Nat.mod_eq_of_lt (show counterBase G < 2^G.w by omega),
    Nat.mod_eq_of_lt hs⟩

private theorem source_cast (f : Fin 7) :
    source G f = ((starts (sizes G) (headerBase G) (counterBase G) f : ℕ) : Word G.w) := by
  fin_cases f <;> rfl

private theorem offset_bound (L : PrimedInputRAM.Lengths) (N : ℕ) (j : Fin (populated L N)) :
    let f := rangeAt L N j
    j.val-rangeStart L N f.castSucc < fieldSize L N f := by
  have h := rangeAt_bounds L N j
  have endEq (f : Fin 7) : rangeStart L N f.castSucc + fieldSize L N f = rangeStart L N f.succ := by
    fin_cases f <;> simp [rangeStart,fieldSize,LiveAuxiliaryHeaders.exteriorBase]
    omega
  rw [← endEq] at h
  dsimp only; omega

/-- An occupied source lies in the header output area or in the nominated
counter array. It is above the stage tag and below the virtual shadow. -/
theorem source_interval (i : Fin (2^(sizes G).h)) (N : ℕ) (hn : N = histLength G)
    (hs : shadowBase G < 2^G.w) (j : Fin (populated (pairLengths G i) N)) :
    let a := (sourceAddress (pairLengths G i) N (source G) j).val
    headerBase G ≤ a ∧ (a < tableBase G ∨ counterBase G ≤ a ∧ a < counterBase G+N) := by
  let L := pairLengths G i
  let f := rangeAt L N j
  let offset := j.val-rangeStart L N f.castSucc
  let start := starts (sizes G) (headerBase G) (counterBase G) f
  obtain ⟨_,ht,he,hshadow⟩ := geometry_order G
  obtain ⟨hlo,hhi⟩ := interval (sizes G) (headerBase G) (counterBase G) N
    (show tableBase G ≤ counterBase G by omega) i f
  have hofs : offset < fieldSize L N f := offset_bound L N j
  change headerBase G ≤ start at hlo
  change start + fieldSize L N f ≤ tableBase G ∨ counterBase G ≤ start ∧ start + fieldSize L N f ≤ counterBase G+N at hhi
  have hfit : start+offset < 2^G.w := by omega
  have val : (sourceAddress L N (source G) j).val = start+offset := by
    change (source G f + (offset : Word G.w)).val = _
    rw [source_cast,← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt hfit]
  dsimp only
  rw [val]
  omega

/-- Address conditions for the selected auxiliary pair and histogram length. The sparse
descriptor, source, and shadow areas satisfy the copy routine’s separation conditions and
avoid the stage tag. -/
structure GeometryAreas (i : Fin (2^(sizes G).h)) (N : ℕ) : Prop where
  areas : Areas (desc G) (shadow G) (pairLengths G i) N (source G)
  tagDesc : ∀ j f, (LiveHeaderCopyDispatch.address (desc G) j f).val ≠ G.addr.val
  tagSource : ∀ j, (sourceAddress (pairLengths G i) N (source G) j).val ≠ G.addr.val
  tagShadow : G.addr.val < (shadow G).val

/-- A single bound on the occupied prefix of the virtual shadow discharges
all source, descriptor, stage-tag and destination separation conditions. -/
theorem geometry (i : Fin (2^(sizes G).h)) (N : ℕ) (hn : N = histLength G)
    (room : shadowBase G + span (pairLengths G i) N ≤ 2^G.w) : GeometryAreas G i N := by
  let L := pairLengths G i
  have spanPos : 0 < span L N := by simp [span,Header.count]
  have occupied : populated L N ≤ span L N := by
    have := L.leftFit
    have := L.rightFit
    change 3+2*L.index+L.advice+L.leftCut+L.rightCut+N ≤ 3+2*L.index+L.advice+2*L.cutCapacity+N
    omega
  have hs : shadowBase G < 2^G.w := by change shadowBase G+span L N ≤ _ at room; omega
  obtain ⟨h₀,h₁,h₂,h₃⟩ := geometry_order G
  have descVal : (desc G).val = tableBase G := Nat.mod_eq_of_lt (show tableBase G < 2^G.w by omega)
  have shadowVal : (shadow G).val = shadowBase G := Nat.mod_eq_of_lt hs
  have tagVal : G.addr.val = Layout.stageTag.eval G.g := Nat.mod_eq_of_lt (show Layout.stageTag.eval G.g < 2^G.w by omega)
  have tableFit : (desc G).val+21 ≤ 2^G.w := by omega
  have shadowFit : (shadow G).val+span L N ≤ 2^G.w := shadowVal.symm ▸ room
  have hdesc (j : Fin 7) (f : Fin 3) :
      (LiveHeaderCopyDispatch.address (desc G) j f).val = tableBase G+(3*j.val+f.val) := by
    rw [LiveAuxiliaryDescriptorInit.address_val _ tableFit, descVal]
  have src := source_interval G i N hn hs
  refine ⟨⟨tableFit,shadowFit,?_,?_,Or.inl (by omega),?_,?_⟩,?_,?_,by omega⟩
  · change populated L N < 2^G.w
    change shadowBase G+span L N ≤ 2^G.w at room
    omega
  · intro j
    obtain ⟨_, ha | ⟨ha,_⟩⟩ := src j <;> omega
  · intro j k
    change _ ≠ (shadow G).val + (sparseOffset L N k).val
    obtain ⟨_, ha | ⟨_,ha⟩⟩ := src j <;> omega
  · intro j f k
    change _ ≠ (shadow G).val + (sparseOffset L N k).val
    rw [hdesc]
    have := j.isLt; have := f.isLt; omega
  · intro j f; rw [hdesc,tagVal]; omega
  · intro j; obtain ⟨lo,_⟩ := src j; omega

/-- The fixed expression for the reserved virtual header size has no group
dependence. Only the populated subset varies with the exterior cuts. -/
def headerSpan (c : Constants) : PublicExpr :=
  3 + 2*(c.lengths.h+2) + c.lengths.advice + 2*((c.lengths.h+1)*c.lengths.delta) + c.grammarLabels

theorem headerSpan_eval (i : Fin (2^(sizes G).h)) :
    (headerSpan G.constants).eval G.g = span (pairLengths G i) (histLength G) := rfl

theorem headerSpan_sitePowers (c : Constants) : (headerSpan c).SitePowers := by
  have hh := c.lengths_h_sitePowers
  have hd := c.lengths_delta_sitePowers
  have ha := c.lengths_advice_sitePowers
  have ht := c.grammarLabels_sitePowers
  unfold headerSpan
  repeat' first | assumption | exact True.intro | constructor

/-- The threshold for disjoint word addresses is uniform over all first-half
groups, the evaluator and the actual contents of the external arrays. -/
theorem eventually_geometry (c : Constants) {B : ℕ} (hB : 1 ≤ B) {H : ℕ → ℕ} (hH : PolynomiallyBounded H) :
    ∀ᶠ n in Filter.atTop, ∀ G : Group, G.constants = c → G.g = paperGeometry B H n →
      ∀ i, GeometryAreas G i (histLength G) := by
  have h : ((Layout.shadow c) + headerSpan c).SitePowers := ⟨Layout.shadow_sitePowers c,headerSpan_sitePowers c⟩
  filter_upwards [(h.fits hB hH).2] with n hf G hc hg i
  have enough : (Layout.shadow c).eval (paperGeometry B H n) + (headerSpan c).eval (paperGeometry B H n) <
      2^(paperGeometry B H n).w := hf.1
  rw [← hc,← hg] at enough
  exact geometry G i (histLength G) rfl ((headerSpan_eval G i) ▸ enough.le)

/-- The same address fit discharges the histogram region conditions of the
preceding nomination stage. -/
theorem nominationFits (i : Fin (2^(sizes G).h))
    (room : shadowBase G + span (pairLengths G i) (histLength G) ≤ 2^G.w)
    (hb : 2*G.g.d ≤ G.w) (hf : 5*(2*G.g.d)+15 ≤ G.clockAt Stage.nominations) : Nominations.Fits G := by
  have pos : 0 < span (pairLengths G i) (histLength G) := by simp [span,Header.count]
  obtain ⟨ht,hh,hd,hc⟩ := geometry_order G
  have hs : shadowBase G < 2^G.w := by omega
  have tag : G.addr.val = Layout.stageTag.eval G.g := Nat.mod_eq_of_lt (show Layout.stageTag.eval G.g < 2^G.w by omega)
  have base : (Nominations.base G).val = counterBase G := Nat.mod_eq_of_lt (show counterBase G < 2^G.w by omega)
  refine ⟨hb,?_,hf,?_,Or.inl ?_⟩
  · change histLength G < 2^G.w; omega
  · change (Nominations.base G).val+histLength G ≤ 2^G.w; omega
  · omega

end LiveProgram.PairStages.Group.Auxiliary

end VPVNP
end Computability
end OAI
