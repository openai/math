import OAI.Computability.BorderVNP.CubeTeamOwnedDiagonalRole
import OAI.Computability.BorderVNP.CubeISAOwnedPreparedDiagonal
import OAI.Computability.BorderVNP.CubeTeamPrivateKeysNative

/-! # The prepared equal-symbol callback in the real outer team scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open Crossing Physical Physical.Owned Scatter Padding.Banks Tally TeamRowSources
open RoutingISA RoutingISA.Owned RoutingISA.OwnedStages VPVNP.BurstRAM

variable {w n d blocks b h K s power vertexBase stop actual claimed : ℕ}
variable {A : Data n d blocks b h K s} {l : TeamRowPrepare.Layout}
variable {pub : Arg → Word w} {original m : Memory w} {rows : Sym2 (Fin d) → Fin (n+1) → ℕ}

/-- The returned native row prepare is sufficient to execute the entire diagonal
callback. Its private word is exactly the ordinary outer dispatcher's row tape,
and its cursor and loop bounds refer to that very iteration. -/
theorem diagonalRole_dispatch_framed (mac : TeamOpcode.Macros w 8) (seed : Seed A l power pub original)
    (alloc : Allocation A l power vertexBase stop w) (g : Fin d) (r : Bank w) (room : vertexBase ≤ stop)
    (same : ∀ j ∈ source l power n, m j = original j)
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key (g,g)) (.ofWords r m))
    (input : CheckImage (rowLayout A l power) (source l power n) n actual claimed rows original)
    (auth : passesLengths b s A.select (A.axis,rows))
    (space : LocalRow.Space (rowLayout A l power) w n b h K s (readings pub 0) actual claimed)
    (labelsFit : d^(n+1) ≤ 2^w) (capFit : declarationCap n d blocks b h s < 2^w)
    (afterScratch : LocalRow.head (rowLayout A l power) n b h K s+8+h ≤ A.singleBase)
    (sourceSafe : ∀ x ∈ source l power n, LocalRow.Protected n h actual (LocalRow.head (rowLayout A l power) n b h K s) x) :
    let q := key (g,g)
    let D := A.single g g (l.view q) (l.crossing q)
    let scatter := A.rowMem g g (l.view q) (l.crossing q) m
    TraceRun pub mac (diagonalRole n b h K s) r m (A.privateTapeAt l q)
      (singleStageCost D + LocalRow.diagonalTicks n b h K s blocks A.axis g) (fun t mt =>
        (readings t 7 = readings r 7 ∧ readings t 22 = q ∧ readings t 23 = l.d*l.d ∧
        (∀ j : Fin (n+1), readings mt (actual+j.val) = rows (Sym2.mk g g) j) ∧
        (∀ x, A.BankWord x → mt x = scatter x) ∧ ∀ x ∈ source l power n, mt x = m x) ∧
        LocalRow.Return h actual (LocalRow.head (rowLayout A l power) n b h K s) (readings r) (readings scatter)
          (subtotals itemRow (crossCount b s A.select) A.axis (Sym2.mk g g)) (.ofWords t mt)) := by
  intro q D scatter
  have ready := diagonal_ready seed alloc g r room same prep
  have protect : OwnedStages.Protected (rowLayout A l power) n (pub 0).val (source l power n) := by
    change OwnedStages.Protected _ _ (readings pub 0) _
    rw [seed.frame]
    exact frame_protected
  have run := diagonalRole_run A pub mac (source l power n) r m g (l.view q) (l.crossing q) power l.header
    actual claimed rows ready.entry ready.selector ready.crossing ready.loaded protect ready.fields.1 ready.fields.2
    ready.labels ready.bank ready.room (fun t _ j hj => alloc.singleDest room (D.pair t).1 (D.pair t).2 hj)
    (input.transfer same) auth space labelsFit capFit afterScratch sourceSafe
  have klt : q < d*d := (finProdFinEquiv (g,g)).isLt
  have pair : pairAt d ⟨q,klt⟩ = (g,g) := finProdFinEquiv.symm_apply_apply (g,g)
  have tape : A.privateTapeAt l q = rowChoices D.selected D.localBits := by
    rw [Data.privateTapeAt,dite_eq_left klt,pair,Data.privateRowBits,dite_eq_right (lt_irrefl g),
      dite_eq_right (lt_irrefl g)]
  rw [tape]
  apply run.mono le_rfl
  rintro t mt ⟨checked,verified,banks,src⟩
  exact ⟨⟨checked.vertex,checked.cursor.trans prep.cursor,checked.bound.trans prep.bound,verified,banks,src⟩,checked⟩

/-- The private tape, loop cursors, checked row, bank update and retained immutable inputs of the actual diagonal callback. -/
theorem diagonalRole_dispatch (mac : TeamOpcode.Macros w 8) (seed : Seed A l power pub original)
    (alloc : Allocation A l power vertexBase stop w) (g : Fin d) (r : Bank w) (room : vertexBase ≤ stop)
    (same : ∀ j ∈ source l power n, m j = original j)
    (prep : TeamRowPrepare.ReadyRow l (readings m) (key (g,g)) (.ofWords r m))
    (input : CheckImage (rowLayout A l power) (source l power n) n actual claimed rows original)
    (auth : passesLengths b s A.select (A.axis,rows))
    (space : LocalRow.Space (rowLayout A l power) w n b h K s (readings pub 0) actual claimed)
    (labelsFit : d^(n+1) ≤ 2^w) (capFit : declarationCap n d blocks b h s < 2^w)
    (afterScratch : LocalRow.head (rowLayout A l power) n b h K s+8+h ≤ A.singleBase)
    (sourceSafe : ∀ x ∈ source l power n, LocalRow.Protected n h actual (LocalRow.head (rowLayout A l power) n b h K s) x) :
    let q := key (g,g)
    let D := A.single g g (l.view q) (l.crossing q)
    let scatter := A.rowMem g g (l.view q) (l.crossing q) m
    TraceRun pub mac (diagonalRole n b h K s) r m (A.privateTapeAt l q)
      (singleStageCost D + LocalRow.diagonalTicks n b h K s blocks A.axis g) (fun t mt =>
        readings t 7 = readings r 7 ∧ readings t 22 = q ∧ readings t 23 = l.d*l.d ∧
        (∀ j : Fin (n+1), readings mt (actual+j.val) = rows (Sym2.mk g g) j) ∧
        (∀ x, A.BankWord x → mt x = scatter x) ∧ ∀ x ∈ source l power n, mt x = m x) := by
  exact (diagonalRole_dispatch_framed mac seed alloc g r room same prep input auth space labelsFit capFit
    afterScratch sourceSafe).mono le_rfl (fun _ _ out => out.1)

/-- The row checker and singleton scatter preserve every old directory word
above the singleton reservation, including words outside the immutable input set. -/
theorem diagonalRole_directory {u t : Bank w} {mt : Memory w} (g : Fin d) (sel cross : ℕ)
    (alloc : Allocation A l power vertexBase stop w)
    (space : LocalRow.Space (rowLayout A l power) w n b h K s (readings pub 0) actual claimed)
    (afterScratch : LocalRow.head (rowLayout A l power) n b h K s+8+h ≤ A.singleBase)
    (ret : LocalRow.Return h actual (LocalRow.head (rowLayout A l power) n b h K s) (readings u)
      (readings (A.rowMem g g sel cross m)) (subtotals itemRow (crossCount b s A.select) A.axis (Sym2.mk g g))
      (.ofWords t mt)) {x : ℕ} (addr : vertexBase ≤ x) : mt x = m x := by
  let D := A.single g g sel cross
  have bank : actual+(n+1) ≤ (rowLayout A l power).bank :=
    space.beforeClaim.trans ((Nat.le_add_right ..).trans space.beforeBank)
  have desc := LocalRow.bank_le_head (rowLayout A l power) n b h K s
  have beyond := alloc.orderSingles.trans addr
  have base : A.singleBase ≤ x := (Nat.le_add_right ..).trans beyond
  have keep := ret.outside x ⟨.inr (by omega),.inr (afterScratch.trans base)⟩
  have changeMem : A.rowMem g g sel cross m x = m x := by
    rw [Data.rowMem,dite_eq_right (lt_irrefl g),dite_eq_right (lt_irrefl g)]
    exact D.final_outside m _ x (.inr beyond)
  exact (Fin.ext keep).trans changeMem

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
