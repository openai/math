import OAI.Computability.VPVNP.LiveProgramPairPreparation
import OAI.Computability.VPVNP.LiveProgramPairCount
import OAI.Computability.VPVNP.LivePhysicalRoutes
import OAI.Computability.VPVNP.LiveHeaderFieldFormats

/-! # The native first-half count following the physical mode router

The only stage-specific trace input in the count below concerns the
compressed pair table itself. The histogram sweep, descriptor initialization,
sparse copy and final exponent test use their verified native programs.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group
open BurstRAM BurstRAM.PrivateRAM LiveStageLink LiveExponent
open ChainAssignments CutSchedule ExponentTrace LiveHeader LiveHeaderProgram
open scoped Classical

variable {G : Group} {m : Memory G.w} {i : Fin (2^(Auxiliary.sizes G).h)}

/-- Number of exponent-test counters, including both grammar-production and motif labels. -/
abbrev labelCount (G : Group) := G.constants.labels.eval G.g
/-- Bit width of each label’s exponent field in the live header. -/
abbrev expWidth (G : Group) := G.constants.Z.eval G.g

/-- Exact-use path semantics of the separately implemented compressed pair
stage, at its literal input ABI and the actual memory produced by the copy. -/
structure PairCall {N : Indexed G Stage.nominations m (Nominations.Nom G)} {μ : Nominations.Nom G}
    {hdr : PrimedInputRAM.Header (Auxiliary.pairLengths G i) → Bool}
    (B : Auxiliary.PreparedBranch G m i hdr N μ) (X : Type*) (increment : X → Fin (labelCount G) → ℕ) where
  /-- Path index for the compressed pair program running from the memory actually produced by
  the auxiliary copy. -/
  indexed : Indexed G Stage.pair (B.copy.memory ()) X
  header (q : X) (a : ℕ) : Auxiliary.headerBase G ≤ a → a < Auxiliary.tableBase G →
    indexed.memory q a = B.copy.memory () a
  count (q : X) (a : Fin (labelCount G)) :
    (indexed.memory q (counterAddr G.exponentPub a).val).val = increment q a

private theorem format {s : LiveHeaderSchedule.Sizes} {cuts : AllCuts s.h s.delta}
    {i : Fin (2^s.h)} {t Z : ℕ} (he : s.e = t*Z) (fit : 1+t*Z ≤ s.delta)
    (mode : physicalTag cuts (halves s.h (.inl i)) = some .pair)
    (pad : Fields.ValidPadding s cuts (halves s.h (.inl i)) .pair .right) :
    pairFormat fit (liveCutEquiv s.h s.delta cuts).1 i := by
  let j := halves s.h (.inl i)
  have hi : 0 < j.succ.val := by change 0 < i.val+1; omega
  have half : j.succ.val ≤ 2^s.h := i.isLt
  have heval := ((physicalTag_pair (by omega) cuts j).mp mode).1.2 hi
    (by change i.val+1 < 2^(s.h+1); rw [pow_succ]; have := i.isLt; have := Nat.two_pow_pos s.h; omega)
  have hwidth : 0 < width (s.h+1) s.delta (i.val+1) := by
    rw [width_double s.h s.delta _ (Nat.succ_pos _) i.isLt]; omega
  have hmode : distributedBit ((liveCutEquiv s.h s.delta cuts).1 i) 0 = true := heval
  have hread := (Fields.validPadding_pair_iff (by decide : Mode.Tag.pair ≠ .unit) .right he fit hi half).mp pad
  constructor
  · change ((liveCutEquiv s.h s.delta cuts).1 i) ⟨0,hwidth⟩ = true
    simpa only [distributedBit,hwidth,↓reduceDIte] using hmode
  · exact hread

variable {cuts : AllCuts (Auxiliary.sizes G).h (Auxiliary.sizes G).delta}
  (fit : 1+labelCount G*expWidth G ≤ (Auxiliary.sizes G).delta)
  {Path : Exterior (Auxiliary.sizes G).h (Auxiliary.sizes G).delta → Fin (2^(Auxiliary.sizes G).h) →
    Nominations.Nom G → Type*}
  [∀ ξ j μ, Fintype (Path ξ j μ)]
  (inc : ∀ ξ j μ, Path ξ j μ → Fin (labelCount G) → ℕ)

/-- The live first-half bit assignment extracted from the physical cuts by the live-cut
equivalence. -/
abbrev fst (cuts : AllCuts (Auxiliary.sizes G).h (Auxiliary.sizes G).delta) :=
  (liveCutEquiv (Auxiliary.sizes G).h (Auxiliary.sizes G).delta cuts).1

/-- The exact contribution on a valid first-half branch after the actual
header and router prefix. The cap is evaluated on every physically joined
report, retaining the prefix costs. -/
theorem post_header_count {hw : 4 ≤ G.w} {advice : Bits (Auxiliary.sizes G).advice}
    (out : LiveHeaderProgram.Output (Auxiliary.sizes G) (Auxiliary.headerBase G) G.g.d hw advice cuts
      (halves (Auxiliary.sizes G).h (.inl i)) .pair m)
    (selected : physicalTag cuts (halves (Auxiliary.sizes G).h (.inl i)) = some .pair)
    (pad : Fields.ValidPadding (Auxiliary.sizes G) cuts (halves (Auxiliary.sizes G).h (.inl i)) .pair .right)
    (tag : G.tagged Stage.nominations m)
    (room : Auxiliary.shadowBase G + LiveAuxiliaryHeaders.span (Auxiliary.pairLengths G i) (Auxiliary.histLength G) ≤ 2^G.w)
    (hwidth : 2*G.g.d ≤ G.w) (hn : 5*(2*G.g.d)+15 ≤ G.clockAt Stage.nominations)
    (hi : 82 ≤ G.clockAt Stage.auxiliaryInit) (hc : 71 ≤ G.clockAt Stage.auxiliaryCopy)
    (he : 31 ≤ G.clockAt Stage.exponents) (ht : 0 < labelCount G) (hZ : 0 < expWidth G)
    (small : ∀ μ q a, inc (exteriorOf fit (fst cuts)) i μ q a + 1 < 2^G.w)
    (S H : ℕ) (pre : List (Report G.w))
    (native : let ξ := exteriorOf fit (fst cuts)
      let F := Auxiliary.nominationFits G i room hwidth hn
      let N := Nominations.indexed G F m tag
      ∀ μ, ∀ B : Auxiliary.PreparedBranch G m i (PairedChain.headers advice ξ i) N μ,
        ∃ C : PairCall B (Path ξ i μ) (inc ξ i μ), ∀ q,
          withinCaps S H (pre ++ (N.logs μ ++ ((B.init.logs ()) ++
            (B.copy.logs () ++ C.indexed.logs q))) ++
            (stageReports G.exponentPub (labelCount G) (expWidth G) (C.indexed.memory q)).map
              (linkedReport G.nextStage G.addr Stage.exponents))) :
    Nat.card (ActualPaths G.P G.clock 0 m (fun tail => withinCaps S H (pre ++ tail))) =
      pairCount fit inc (fst cuts) i := by
  let ξ := exteriorOf fit (fst cuts)
  let F := Auxiliary.nominationFits G i room hwidth hn
  let N := Nominations.indexed G F m tag
  let hdr := PairedChain.headers advice ξ i
  have sz : (Auxiliary.sizes G).e = labelCount G*expWidth G := rfl
  have good := format sz fit selected pad
  let B (μ : Nominations.Nom G) : Auxiliary.PreparedBranch G m i hdr N μ :=
    Classical.choice (Auxiliary.prepare out (by decide) sz fit room hwidth hn hi hc tag μ)
  choose C hcaps using fun μ => native μ (B μ)
  let A : Chronology G m (Nominations.Nom G) (Path ξ i) :=
    ⟨N,fun μ => (B μ).init,fun μ => (B μ).copy,fun μ => (C μ).indexed⟩
  obtain ⟨htag,hbase,hd,hcounter⟩ := Auxiliary.geometry_order G
  have hfull := Auxiliary.counter_end_le_shadow G
  have hspan : 0 < LiveAuxiliaryHeaders.span (Auxiliary.pairLengths G i) (Auxiliary.histLength G) := by
    simp [LiveAuxiliaryHeaders.span,PrimedInputRAM.Header.count]
  have hs : Auxiliary.shadowBase G < 2^G.w := by omega
  have hfit : (Layout.oldState G.constants).eval G.g ≤ 2^G.w := by
    change Auxiliary.counterBase G + G.constants.labels.eval G.g ≤ _; omega
  have hlimit : LiveHeaderSchedule.limit (Auxiliary.sizes G) (Auxiliary.headerBase G) ≤ 2^G.w := by
    change Auxiliary.tableBase G ≤ _; omega
  let ebase := LiveHeaderSchedule.exponentBase (Auxiliary.sizes G) (Auxiliary.headerBase G)
  have bounds side := LiveHeaderProgram.dest_bounds (Auxiliary.sizes G) (Auxiliary.headerBase G) side .exponents (by decide)
  have basefit (side) : ebase side < 2^G.w := by
    have h := (bounds side).2
    change ebase side + (Auxiliary.sizes G).e ≤ Auxiliary.tableBase G at h
    omega
  have hdata μ q : BufferValues G.exponentPub (counters fit (fst cuts) i.castSucc)
      (counters fit (fst cuts) i.succ) ((A.pair μ).memory q) := by
    apply out.pairBufferValues_after i (by decide) sz fit hlimit G.exponentPub
      (Nat.mod_eq_of_lt (basefit .left)) (Nat.mod_eq_of_lt (basefit .right))
    intro side j hj
    have high := (bounds side).2
    change ebase side + (Auxiliary.sizes G).e ≤ Auxiliary.tableBase G at high
    have low : Auxiliary.headerBase G ≤ ebase side := by
      cases side <;> dsimp [ebase,LiveHeaderSchedule.exponentBase,LiveHeaderSchedule.exteriorBase,
        LiveHeaderSchedule.adviceBase,LiveHeaderSchedule.rightIndexBase,LiveHeaderSchedule.leftIndexBase,
        LiveHeaderSchedule.populationAddr,LiveHeaderSchedule.highAddr,LiveHeaderSchedule.indexBase] <;> omega
    have lo : Auxiliary.headerBase G ≤ ebase side+j := by omega
    have hi' : ebase side+j < Auxiliary.tableBase G := by omega
    exact ((C μ).header q _ lo hi').trans ((B μ).headerFrame _ lo hi')

  let cap := fun tail => withinCaps S H (pre ++ tail)
  have hcap (rs) (ok : cap rs) : RAMBuckets.cost Report.probes rs ≤ S*H := by
    have bound := ok.1; rw [RAMBuckets.cost_append] at bound; omega
  have eq := A.count fit (fst cuts) i inc (ExponentStage.layout _ _ hfit ht) hZ (by omega) he
    (ExponentStage.tag_fresh _ _ hfit) hdata (fun μ q a => (C μ).count q a) small cap _ hcap
    (fun μ q => by simpa only [cap,Chronology.prefixLogs,A,List.append_assoc] using hcaps μ q)
  exact (ite_eq_left good).symm.trans eq

end LiveProgram.PairStages.Group

end VPVNP
end Computability
end OAI
