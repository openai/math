import OAI.Computability.BorderVNP.CubeTeamVertexDirectoryFrame
import OAI.Computability.BorderVNP.CubeISAOwnedStageInverse
import OAI.Computability.BorderVNP.RoutingISACallInversion

/-! # Reading the actual private choices of an arbitrary returned diagonal role

Only the singleton scatter can draw private bits. Its actual chronological event
word determines the scattered bank even if it differs from the supplied witness.
The unsigned checker reads the declaration and preserves the recovered bank,
previous vertex records and the source words of later roles.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.Owned RoutingISA.OwnedStages Physical Physical.Owned Scatter Padding.Banks
open TeamRowSources VPVNP.BurstRAM DiagonalResidueRAM

variable {w n blocks b h K s : ℕ} {l : TeamRowPrepare.Layout}
variable {A : Data n l.d blocks b h K s} {owner : Fin l.d → ℕ} {power base stop actual claimed : ℕ}
variable {rows : Sym2 (Fin l.d) → Fin (n+1) → ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {original m mt : Memory w} {r t : Bank w} {es : List (TeamRAM.Event w)}

/-- The complete return has precisely its recovered private singleton word. Its checker
proves the claimed row, retains the true bank and leaves every previous vertex address alone.
The argument uses only the decoded declaration and native readiness conditions. -/
theorem diagonal_role_recover (g : Fin l.d)
    (ready : DiagonalReady A l power g pub r m)
    (protection : OwnedStages.Protected (rowLayout A l power) n (pub 0).val (source l power n))
    (input : CheckImage (rowLayout A l power) (source l power n) n actual claimed rows m)
    (space : LocalRow.Space (rowLayout A l power) w n b h K s (readings pub 0) actual claimed)
    (labelsFit : l.d^(n+1) ≤ 2^w) (capFit : declarationCap n l.d blocks b h s < 2^w)
    (afterScratch : LocalRow.head (rowLayout A l power) n b h K s+8+h ≤ A.singleBase)
    (afterSingles : A.singleBase+l.d^(n+1)*l.d^(n+1)*(blocks*(h*b)) ≤ base)
    (checkSafe : ∀ x ∈ source l power n, LocalRow.Protected n h actual
      (LocalRow.head (rowLayout A l power) n b h K s) x)
    (run : Runs pub mac (diagonalRole n b h K s) r m es t mt) :
    let q := key (g,g)
    let D := A.single g g (l.view q) (l.crossing q)
    let E := D.withTape (ChoiceTape.extend (es.flatMap TeamRAM.Event.choices))
    TraceOK es (rowChoices E.selected E.localBits) es.length ∧
      readings t 7 = readings r 7 ∧ readings t 22 = readings r 22 ∧ readings t 23 = readings r 23 ∧
      (∀ j, subtotals itemRow (crossCount b s A.select) A.axis (Sym2.mk g g) j = rows (Sym2.mk g g) j) ∧
      (∀ x, A.BankWord x → mt x = (E.before m (singlePairTrials n l.d)).2 x) ∧
      (∀ x ∈ source l power n, mt x = m x) ∧ ∀ x ≥ base, mt x = m x := by
  intro q D E
  obtain ⟨gs,u,mu,hs,rfl,stage,checker⟩ := CellDispatch.seq_split run
  have unsigned := checker.unsigned_events (LocalRow.diagonalChecked_unsigned n b h K s)
  have quiet : TraceOK hs [] hs.length :=
    ⟨rfl,List.flatMap_eq_nil_iff.mpr fun e he => (unsigned e he).1,fun e he => (unsigned e he).2⟩
  have tape : (gs++hs).flatMap TeamRAM.Event.choices = gs.flatMap TeamRAM.Event.choices := by
    simp only [List.flatMap_append,quiet.2.1,List.append_nil]
  let L := rowLayout A l power
  let rowBits := gs.flatMap TeamRAM.Event.choices
  let recovered := D.withTape (ChoiceTape.extend rowBits)
  have identified : E = recovered := congrArg (fun bits => D.withTape (ChoiceTape.extend bits)) tape
  obtain ⟨trace,_,held,_,_,image⟩ := singleStage_recover pub mac L D (source l power n) r m
    ready.entry ready.selector ready.crossing ready.loaded ready.fit ready.prepared ready.fields.1 ready.fields.2
    ready.labels ready.bank ready.room.frameFit ready.room.keys ready.room.allocation stage
  change mu = (recovered.before m (singlePairTrials n l.d)).2 at image
  have prep : recovered.PreparedRow (source l power n) m := D.prepared_withTape _ m ready.prepared
  have keep x (hx : x ∈ source l power n) : mu x = m x :=
    (congrFun image x).trans (recovered.before_source m prep _ x hx)
  have im := input.transfer keep
  have en := ready.entry.keep held
  have checked := (LocalRow.diagonalChecked_run pub mac u mu L A.axis g b h K s actual claimed A.select rows
    (protection.loaded ready.loaded keep) im.actualAt im.claimedAt im.table space rfl labelsFit capFit
    en.zero en.one en.axis en.left en.right).sound checker
  obtain ⟨truth,ret⟩ := checked
  rw [identified]
  refine ⟨?_,ret.vertex.trans (congrArg Fin.val (held 7 (by decide))),
    ret.cursor.trans (congrArg Fin.val (held 22 (by decide))),
    ret.bound.trans (congrArg Fin.val (held 23 (by decide))),truth,?_,?_,?_⟩
  · have joined := trace.append quiet
    rw [List.append_nil] at joined
    refine ⟨rfl,joined.2.1.trans ?_,joined.2.2⟩
    congr! 1
  · intro x word
    exact (Fin.ext (ret.outside x (checker_bank_protected A power l.header actual claimed (readings pub 0)
      space afterScratch x word))).trans (congrFun image x)
  · intro x hx
    exact (Fin.ext (ret.outside x (checkSafe x hx))).trans (keep x hx)
  · intro x hx
    have above := afterSingles.trans hx
    have single : A.singleBase ≤ x := (Nat.le_add_right ..).trans above
    have low : actual+(n+1) ≤ L.bank :=
      space.beforeClaim.trans ((Nat.le_add_right ..).trans space.beforeBank)
    have head := LocalRow.bank_le_head L n b h K s
    have hi : LocalRow.head L n b h K s+8+h ≤ x := afterScratch.trans single
    have check := ret.outside x ⟨.inr (by omega),.inr hi⟩
    exact (Fin.ext check).trans ((congrFun image x).trans (recovered.final_outside m _ x (.inr above)))

/-- The physical setup and actual outer prepare supply all the operands for inverting
an arbitrary normal return, including the true grouping coordinate and public owner cursor. -/
theorem PhysicalSetup.diagonal_role_sound (P : PhysicalSetup A owner power base stop actual claimed rows pub original)
    (g : Fin l.d) (same : ∀ x ∈ source l power n, m x = original x)
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key (g,g)) (.ofWords r m))
    (run : Runs pub mac (diagonalRole n b h K s) r m es t mt) :
    let q := key (g,g)
    let D := A.single g g (l.view q) (l.crossing q)
    let E := D.withTape (ChoiceTape.extend (es.flatMap TeamRAM.Event.choices))
    TraceOK es (rowChoices E.selected E.localBits) es.length ∧
      readings t 7 = readings r 7 ∧ readings t 22 = q ∧ readings t 23 = l.d*l.d ∧
      (∀ j, subtotals itemRow (crossCount b s A.select) A.axis (Sym2.mk g g) j = rows (Sym2.mk g g) j) ∧
      (∀ x, A.BankWord x → mt x = (E.before m (singlePairTrials n l.d)).2 x) ∧
      (∀ x ∈ source l power n, mt x = m x) ∧ ∀ x ≥ base, mt x = m x := by
  have before : base ≤ stop := (Nat.le_add_right ..).trans P.capacity
  have ready := diagonal_ready P.seed P.allocation g r before same prep
  have protect : OwnedStages.Protected (rowLayout A l power) n (pub 0).val (source l power n) := by
    change OwnedStages.Protected _ _ (readings pub 0) _
    rw [P.seed.frame]
    exact frame_protected
  obtain ⟨trace,vert,cur,bound,rest⟩ := diagonal_role_recover g ready protect (P.image.transfer same) P.checker
    P.labelsFit P.capFit P.afterScratch P.allocation.orderSingles P.checkSafe run
  exact ⟨trace,vert,cur.trans prep.cursor,bound.trans prep.bound,rest⟩

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
