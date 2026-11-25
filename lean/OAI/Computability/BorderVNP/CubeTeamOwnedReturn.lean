import OAI.Computability.BorderVNP.CubeTeamOwnedRun
import OAI.Computability.BorderVNP.CubeTeamRowInverse
import OAI.Computability.BorderVNP.CubeTeamOwnedPositive

/-! # Reconstructing the native group traversal and vertex publication

The row induction starts at the vertex pointer read from field 78 and visits
the actual branches in order. Each returning branch sees the vertex cursor for
its own prefix. The final store publishes the number of those vertex triples
in field 46.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.CellDispatch VPVNP.BurstRAM TeamRowPrepare

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- The exact four portions of a returning group program, including their
chronological events and the physical memory immediately before publication. -/
structure OwnedReturnTrace (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : Layout) (n b h K s : ℕ) (r : Bank w) (original : Memory w)
    (es : List (TeamRAM.Event w)) (t : Bank w) (mt : Memory w) where
  /-- Register bank after loading the directory pointer from frame field 78. -/
  initial : Bank w
  /-- Bank at ordinal zero after calculating the square row bound. -/
  scanStart : Bank w
  /-- Bank after the final ordered pair and the terminating loop guard. -/
  afterScan : Bank w
  /-- Complete memory image at entry to the count publication routine. -/
  pre : Memory w
  /-- Actual events of the initial pointer load. -/
  startEvents : List (TeamRAM.Event w)
  /-- Actual events of the row ordinal and bound initialization. -/
  setupEvents : List (TeamRAM.Event w)
  /-- One inner role history for each row ordinal, empty for an unowned row. -/
  rows : List (List (TeamRAM.Event w))
  /-- Complete row-loop trace, including preparation, dispatch, and cursor increments. -/
  rowEvents : List (TeamRAM.Event w)
  /-- Actual events computing and storing the final count in frame field 46. -/
  finishEvents : List (TeamRAM.Event w)
  start : Runs pub mac startVertices r original startEvents initial original
  setup : Runs pub mac TeamRowPrepare.setup initial original setupEvents scanStart original
  history : ReturnedRows pub mac l (strictRole n b h K s) (diagonalRole n b h K s)
    0 scanStart original rows rowEvents afterScan pre
  finish : Runs pub mac finishVertices afterScan pre finishEvents t mt
  chronology : es = startEvents ++ ((setupEvents ++ rowEvents) ++ finishEvents)

variable {l : Layout} {n blocks b h K s : ℕ} {r : Bank w} {original : Memory w}
variable {es : List (TeamRAM.Event w)} {t : Bank w} {mt : Memory w}

/-- Replay all four pieces of the recovered history. -/
theorem OwnedReturnTrace.runs (H : OwnedReturnTrace pub mac l n b h K s r original es t mt) :
    Runs pub mac (ownedGroups n b h K s) r original es t mt := by
  rw [H.chronology]
  exact H.start.seq ((H.setup.seq H.history.runs).seq H.finish)

/-- The private tape is the chronological concatenation of just the inner
role words. All events, including the final public count store, have positive sign. -/
theorem OwnedReturnTrace.traceOK (H : OwnedReturnTrace pub mac l n b h K s r original es t mt) :
    DiagonalResidueRAM.TraceOK es (H.rows.flatMap (List.flatMap TeamRAM.Event.choices)) es.length := by
  refine ⟨rfl,?_,H.runs.positive (ownedGroups_positive ..)⟩
  have zero {c : Code} {a ma fs z mz} (run : Runs pub mac c a ma fs z mz) (u : c.unsigned = true) :
      fs.flatMap TeamRAM.Event.choices = [] :=
    List.flatMap_eq_nil_iff.mpr fun e he => (run.unsigned_events u e he).1
  apply (congrArg (List.flatMap TeamRAM.Event.choices) H.chronology).trans
  simp only [List.flatMap_append,zero H.start (by decide),zero H.setup (by decide),zero H.finish (by decide),
    List.nil_append,List.append_nil,H.history.choices]

/-- Invert every actual return of the finite owned-group program. The
induction hypothesis may describe the entire private memory image and the
immutable deck. At each owned row the callback receives the true directory
cursor and a run of the concrete branch selected by the two symbols. -/
theorem ownedGroups_return_induction (n blocks b h K s : ℕ) (l : Layout) (owner : ℕ → ℕ)
    (I : ℕ → Memory w → Prop) (base : ℕ) (fit : l.Fits w) (frame : readings pub 0 = l.frame)
    (initial : I 0 original)
    (inventory : ∀ q mu, I q mu → l.Fields (readings mu) ∧ readings mu (l.frame+78) = base ∧
      ∀ g < l.d, readings mu (l.ownerBase+g) = owner g)
    (skip : ∀ q < l.d*l.d, owner (q/l.d) ≠ l.teamID → ∀ mu, I q mu → I (q+1) mu)
    (visit : ∀ q < l.d*l.d, owner (q/l.d) = l.teamID → ∀ u mu, I q mu →
      readings u 7 = base+3*vertexPrefix l owner n blocks q →
      ReadyRow l (readings mu) q (.ofWords u mu) → ∀ ys v mv,
      Runs pub mac (if q/l.d = q%l.d then diagonalRole n b h K s else strictRole n b h K s) u mu ys v mv →
      I (q+1) mv ∧ readings v 7 = readings u 7+(if q/l.d = q%l.d then 0 else 3*strictVertices n l.d blocks) ∧
        readings v 22 = q ∧ readings v 23 = l.d*l.d)
    (run : Runs pub mac (ownedGroups n b h K s) r original es t mt) :
    let N := l.d*l.d
    let count := vertexPrefix l owner n blocks N
    ∃ H : OwnedReturnTrace pub mac l n b h K s r original es t mt,
      readings H.scanStart 7 = base ∧ I N H.pre ∧ readings t 7 = base+3*count ∧
        mt = publishVertexCount H.pre l.frame count ∧ readings mt (l.frame+46) = count := by
  let J (q : ℕ) (v : Word w) (m : Memory w) := I q m ∧ v.val = base+3*vertexPrefix l owner n blocks q
  have room : l.frame+78 < 2^w := by have := fit.frameFit; omega
  have step {q : ℕ} {a : Bank w} {ma ys v mv} (hq : q < l.d*l.d) (hj : J q (a 7) ma)
      (rd : ReadyRow l (readings ma) q (.ofWords a ma))
      (actual : Visit pub mac l (strictRole n b h K s) (diagonalRole n b h K s) q a ma ys v mv) :
      Next l J q v mv := by
    have gd : q/l.d < l.d := (pairAt l.d ⟨q,hq⟩).1.isLt
    have word := (inventory q ma hj.1).2.2 _ gd
    cases actual with
    | skip miss =>
      have other : owner (q/l.d) ≠ l.teamID := word ▸ miss
      refine ⟨⟨skip q hq other ma hj.1,?_⟩,rd.cursor,rd.bound⟩
      simpa only [vertexPrefix,Finset.sum_range_succ,other,false_and,ite_false,Nat.add_zero] using hj.2
    | offDiagonal owned different role =>
      have own : owner (q/l.d) = l.teamID := word ▸ owned
      have hc := visit q hq own a ma hj.1 hj.2 rd _ _ _ (by simpa only [ite_eq_right different] using role)
      refine ⟨⟨hc.1,?_⟩,hc.2.2⟩
      change readings _ 7 = _
      have cursor : readings a 7 = _ := hj.2
      simp [hc.2.1,cursor,vertexPrefix,Finset.sum_range_succ,own,different,Nat.mul_add,Nat.add_assoc]
    | onDiagonal owned equal role =>
      have own : owner (q/l.d) = l.teamID := word ▸ owned
      have hc := visit q hq own a ma hj.1 hj.2 rd _ _ _ (by simpa only [ite_eq_left equal] using role)
      refine ⟨⟨hc.1,?_⟩,hc.2.2⟩
      change readings _ 7 = _
      have cursor : readings a 7 = _ := hj.2
      simp only [hc.2.1,cursor,vertexPrefix,Finset.sum_range_succ,equal,ne_self_iff_false,and_false,ite_false,
        ite_true,Nat.add_zero]
  obtain ⟨startEvents,init,mi,tail,rfl,start,rest⟩ := seq_split run
  obtain ⟨_,_,beginning,sameMem⟩ := startVertices_return frame room (inventory 0 original initial).2.1 start
  subst mi
  obtain ⟨scanEvents,afterScan,pre,finishEvents,rfl,scanRun,finishRun⟩ := seq_split rest
  have atZero : J 0 (init 7) original := ⟨initial,by simpa [vertexPrefix,readings] using beginning⟩
  obtain ⟨setupEvents,a,rows,rowEvents,rfl,setupRun,history,hj,_,_⟩ := scan_decode_indexed J fit frame
    (fun h => (inventory _ _ h.1).1) step atZero scanRun
  have countAt : readings afterScan 7 = _ := hj.2
  obtain ⟨_,_,same,published⟩ := finishVertices_return frame room (inventory _ pre hj.1).2.1 countAt finishRun
  have fits : vertexPrefix l owner n blocks (l.d*l.d) < 2^w := by
    have : readings afterScan 7 < 2^w := (afterScan 7).isLt
    omega
  refine ⟨⟨init,a,afterScan,pre,startEvents,setupEvents,rows,rowEvents,finishEvents,
    start,setupRun,history,finishRun,rfl⟩,(congrArg Fin.val (setupRun.keepsReg setup_keeps)).trans beginning,
    hj.1,same.trans countAt,published,?_⟩
  rw [published,publishVertexCount_here _ _ _ fits]

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
