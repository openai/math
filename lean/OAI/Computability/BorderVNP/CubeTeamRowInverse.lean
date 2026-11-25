import OAI.Computability.BorderVNP.CubeTeamRowDispatch
import OAI.Computability.BorderVNP.RoutingISACallInversion

/-! # Inverting the ordered symbol-row dispatch

A returned execution gives one inner history per ordered pair, in increasing
cursor order. An unowned pair has empty inner history. Every entry records the
prepared state, the branch that ran, and the state passed to the next row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA RoutingISA.CellDispatch VPVNP.BurstRAM DiagonalResidueRAM TeamRowPrepare

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

/-- Inner execution selected by the owner table and the two decoded symbols. -/
inductive Visit (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (l : Layout)
    (strict diagonal : Code) (q : ℕ) (s : Bank w) (m : Memory w) :
    List (TeamRAM.Event w) → Bank w → Memory w → Prop where
  | skip (miss : readings m (l.ownerBase+q/l.d) ≠ l.teamID) : Visit pub mac l strict diagonal q s m [] s m
  | offDiagonal {es t mt} (owned : readings m (l.ownerBase+q/l.d) = l.teamID)
      (different : q/l.d ≠ q%l.d) (run : Runs pub mac strict s m es t mt) :
      Visit pub mac l strict diagonal q s m es t mt
  | onDiagonal {es t mt} (owned : readings m (l.ownerBase+q/l.d) = l.teamID)
      (equal : q/l.d = q%l.d) (run : Runs pub mac diagonal s m es t mt) :
      Visit pub mac l strict diagonal q s m es t mt

/-- Exact sequence of physical rows, indexed by its intermediate states and trace.
The two dispatch ticks are the owner and diagonal tests for an owned row, or
the owner test and fall-through instruction for an unowned row. -/
inductive ReturnedRows (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (l : Layout) (strict diagonal : Code) :
    ℕ → Bank w → Memory w → List (List (TeamRAM.Event w)) → List (TeamRAM.Event w) →
    Bank w → Memory w → Prop where
  | done {s m} (cursor : readings s 22 = l.d*l.d) (bound : readings s 23 = l.d*l.d) :
      ReturnedRows pub mac l strict diagonal (l.d*l.d) s m [] [tick w] s m
  | row {q s m ps ys a bs b mt c rs gs t mz}
      (inRange : q < l.d*l.d) (prep : Runs pub mac prepare s m ps a m)
      (ready : ReadyRow l (readings m) q (.ofWords a m))
      (visit : Visit pub mac l strict diagonal q a m ys b mt)
      (bump : Runs pub mac advance b mt bs c mt)
      (tail : ReturnedRows pub mac l strict diagonal (q+1) c mt rs gs t mz) :
      ReturnedRows pub mac l strict diagonal q s m (ys::rs)
        (tick w :: ((ps ++ ((tick w :: tick w :: ys) ++ bs)) ++ gs)) t mz

/-- Number of rows remaining in the chronological history. -/
theorem ReturnedRows.length {l : Layout} {strict diagonal : Code} {q s m rows es t mt}
    (h : ReturnedRows pub mac l strict diagonal q s m rows es t mt) :
    q + rows.length = l.d*l.d := by
  induction h with
  | done => simp
  | row _ _ _ _ _ _ ih => simp only [List.length_cons]; omega

private theorem unsignedTrace {c : Code} {s m es t mt}
    (run : Runs pub mac c s m es t mt) (hu : c.unsigned = true) : TraceOK es [] es.length := by
  have p := run.unsigned_events hu
  exact ⟨rfl,List.flatMap_eq_nil_iff.mpr (fun e he => (p e he).1),fun e he => (p e he).2⟩

/-- Administrative instructions consume no private words. Only the recovered
inner executions contribute to the chronological choice tape. -/
theorem ReturnedRows.choices {l : Layout} {strict diagonal : Code} {q s m rows es t mt}
    (h : ReturnedRows pub mac l strict diagonal q s m rows es t mt) :
    es.flatMap TeamRAM.Event.choices = rows.flatMap (List.flatMap TeamRAM.Event.choices) := by
  induction h with
  | done => simp [tick]
  | row _ prep _ _ bump _ ih =>
    simp [tick,(unsignedTrace prep (by decide)).2.1,(unsignedTrace bump (by decide)).2.1,ih]

/-- All signs are positive exactly when they are positive on every recovered
inner execution. -/
theorem ReturnedRows.signs_iff {l : Layout} {strict diagonal : Code} {q s m rows es t mt}
    (h : ReturnedRows pub mac l strict diagonal q s m rows es t mt) :
    (∀ e ∈ es, e.sign = .plus) ↔ ∀ ys ∈ rows, ∀ e ∈ ys, e.sign = .plus := by
  induction h with
  | done => simp [tick]
  | row _ prep _ _ bump _ ih =>
    simp only [List.mem_cons,List.mem_append,or_imp,forall_and,tick] at *
    grind [unsignedTrace prep (by decide),unsignedTrace bump (by decide),TraceOK]

private theorem ofBounded {c : Code} {s m es t mt budget P} (det : c.deterministic = true)
    (good : BoundedRun pub mac c s m budget P) (run : Runs pub mac c s m es t mt) :
    P (.ofWords t mt) := by
  obtain ⟨_,_,_,first,_,post⟩ := good
  obtain ⟨rfl,rfl,rfl⟩ := first.unique_of_deterministic det run
  exact post

private theorem prepare_decode {l : Layout} {s m es t mt q}
    (fit : l.Fits w) (frame : readings pub 0 = l.frame) (fields : l.Fields (readings m))
    (more : q < l.d*l.d) (cur : readings s 22 = q) (bound : readings s 23 = l.d*l.d)
    (run : Runs pub mac prepare s m es t mt) :
    mt = m ∧ ReadyRow l (readings m) q (.ofWords t mt) := by
  have ready := ofBounded (by decide) (run_prepare pub mac l s m q fit frame fields more cur bound) run
  exact ⟨funext fun j => Fin.ext (congrFun ready.mem j),ready⟩

private theorem owner_guard {l : Layout} {s : Bank w} {m : Memory w} {q}
    (ready : ReadyRow l (readings m) q (.ofWords s m)) :
    s 46 = s 47 ↔ readings m (l.ownerBase+q/l.d) = l.teamID := by
  rw [Fin.ext_iff,show (s 46).val = _ from ready.owner,show (s 47).val = _ from ready.team]

private theorem symbols_guard {l : Layout} {s : Bank w} {m : Memory w} {q}
    (ready : ReadyRow l (readings m) q (.ofWords s m)) : s 48 = s 49 ↔ q/l.d = q%l.d := by
  rw [Fin.ext_iff,show (s 48).val = _ from ready.left,show (s 49).val = _ from ready.right]

private theorem select_decode {l : Layout} {strict diagonal : Code} {s m q es t mt}
    (ready : ReadyRow l (readings m) q (.ofWords s m))
    (run : Runs pub mac (select strict diagonal) s m es t mt) :
    ∃ ys, es = tick w :: tick w :: ys ∧ Visit pub mac l strict diagonal q s m ys t mt := by
  obtain ⟨fs,rfl,h⟩ := eq_split run
  have owner := owner_guard ready
  have symbols := symbols_guard ready
  by_cases owned : readings m (l.ownerBase+q/l.d) = l.teamID
  · rw [ite_eq_left (owner.mpr owned)] at h
    obtain ⟨ys,rfl,hr⟩ := eq_split h
    by_cases same : q/l.d = q%l.d
    · rw [ite_eq_left (symbols.mpr same)] at hr
      exact ⟨ys,rfl,.onDiagonal owned same hr⟩
    · rw [ite_eq_right (symbols.not.mpr same)] at hr
      exact ⟨ys,rfl,.offDiagonal owned same hr⟩
  · rw [ite_eq_right (owner.not.mpr owned)] at h
    have nop : Runs pub mac .nop s m [tick w] s m := Runs.localStep m rfl rfl
    obtain ⟨rfl,rfl,rfl⟩ := nop.unique_of_deterministic rfl h
    exact ⟨[],rfl,.skip owned⟩

private theorem advance_decode {q : ℕ} {s m es t mt} (cur : readings s 22 = q)
    (fit : q+1 < 2^w) (run : Runs pub mac advance s m es t mt) :
    readings t 22 = q+1 ∧ t 23 = s 23 ∧ mt = m := by
  let a : Bank w := Function.update s 59 1
  let b : Bank w := Function.update a 22 (a 22 + a 59)
  have r : Runs pub mac advance s m ([tick w] ++ [tick w]) b m :=
    (Runs.localStep (c := .constant 59 1) m rfl rfl).seq (Runs.localStep (c := .binary .add 22 22 59) m rfl rfl)
  obtain ⟨rfl,rfl,rfl⟩ := r.unique_of_deterministic (by decide) run
  have one : (1 : Word w).val = 1 := word_val w 1 (by omega)
  have cap : (s 22).val + (1 : Word w).val < 2^w := by simpa only [← cur,one,readings] using fit
  have hw : 0 < w := by by_contra! he; have hw := Nat.eq_zero_of_le_zero he; subst w; simp at fit
  simp (config := {decide := true}) [b,a,readings,Fin.val_add_eq_of_add_lt cap,hw,←cur]

/-- A reachable input memory supplies the public frame, and a row's actual
branch preserves reachability. The two protected outer registers are checked
directly on each inserted program. -/
structure ScanFrame (l : Layout) (strict diagonal : Code) (reachable : Memory w → Prop)
    (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) : Prop where
  fields : ∀ m, reachable m → l.Fields (readings m)
  strictCursor : strict.keeps 22 = true
  strictBound : strict.keeps 23 = true
  diagonalCursor : diagonal.keeps 22 = true
  diagonalBound : diagonal.keeps 23 = true
  visit : ∀ {q s m es t mt}, q < l.d*l.d → reachable m →
    ReadyRow l (readings m) q (.ofWords s m) → Visit pub mac l strict diagonal q s m es t mt → reachable mt

private theorem visit_regs {l : Layout} {strict diagonal : Code} {reachable : Memory w → Prop}
    (F : ScanFrame l strict diagonal reachable pub mac) {s m q es t mt}
    (ready : ReadyRow l (readings m) q (.ofWords s m)) (visit : Visit pub mac l strict diagonal q s m es t mt) :
    readings t 22 = q ∧ readings t 23 = l.d*l.d := by
  cases visit with
  | skip => exact ⟨ready.cursor,ready.bound⟩
  | offDiagonal _ _ run =>
    exact ⟨(congrArg Fin.val (run.keepsReg F.strictCursor)).trans ready.cursor,
      (congrArg Fin.val (run.keepsReg F.strictBound)).trans ready.bound⟩
  | onDiagonal _ _ run =>
    exact ⟨(congrArg Fin.val (run.keepsReg F.diagonalCursor)).trans ready.cursor,
      (congrArg Fin.val (run.keepsReg F.diagonalBound)).trans ready.bound⟩

private theorem loop_decode_indexed {l : Layout} {strict diagonal : Code}
    (I : ℕ → Word w → Memory w → Prop) (fit : l.Fits w) (frame : readings pub 0 = l.frame)
    (fields : ∀ {q v m}, I q v m → l.Fields (readings m))
    (step : ∀ {q a ma ys b mb}, q < l.d*l.d → I q (a 7) ma →
      ReadyRow l (readings ma) q (.ofWords a ma) → Visit pub mac l strict diagonal q a ma ys b mb → Next l I q b mb)
    {k q : ℕ} {s m es t mt} (hlen : q+k = l.d*l.d) (hm : I q (s 7) m)
    (cur : readings s 22 = q) (bound : readings s 23 = l.d*l.d)
    (run : Runs pub mac (.whileLt 22 23 (body strict diagonal)) s m es t mt) :
    ∃ rows, ReturnedRows pub mac l strict diagonal q s m rows es t mt ∧
      I (l.d*l.d) (t 7) mt ∧ readings t 22 = l.d*l.d ∧ readings t 23 = l.d*l.d := by
  induction k generalizing q s m es with
  | zero =>
    simp only [Nat.add_zero] at hlen
    obtain ⟨rfl,rfl,rfl⟩ := while_last run (by change ¬readings s 22 < readings s 23; omega)
    subst q
    exact ⟨[],.done cur bound,hm,cur,bound⟩
  | succ k ih =>
    have more : q < l.d*l.d := by omega
    obtain ⟨gs,u,mu,fs,rfl,row,tail⟩ := while_next run (by change readings s 22 < readings s 23; omega)
    obtain ⟨ps,a,ma,ys,rfl,prep,finish⟩ := seq_split row
    obtain ⟨rfl,ready⟩ := prepare_decode fit frame (fields hm) more cur bound prep
    obtain ⟨ys,b,mb,bs,rfl,dispatch,bump⟩ := seq_split finish
    obtain ⟨inner,rfl,visit⟩ := select_decode ready dispatch
    obtain ⟨next,cursor,limit⟩ := step more (prep.keepsReg prepare_keeps ▸ hm) ready visit
    obtain ⟨inc,stable,rfl⟩ := advance_decode cursor ((Nat.succ_le_of_lt more).trans_lt fit.square) bump
    obtain ⟨rs,ht,hm',hc,hb⟩ := ih (by omega) (bump.keepsReg (k := 7) (by decide) ▸ next) inc
      ((congrArg Fin.val stable).trans limit) tail
    exact ⟨inner::rs,.row more prep ready visit bump ht,hm',hc,hb⟩

/-- Invert the complete scan while following a prefix invariant on the actual
row ordinal, vertex cursor, and memory. Only the currently visited row needs
to preserve the invariant, and its two outer register values are verified on
that return. -/
theorem scan_decode_indexed {l : Layout} {strict diagonal : Code}
    (I : ℕ → Word w → Memory w → Prop) (fit : l.Fits w) (frame : readings pub 0 = l.frame)
    (fields : ∀ {q v m}, I q v m → l.Fields (readings m))
    (step : ∀ {q a ma ys b mb}, q < l.d*l.d → I q (a 7) ma →
      ReadyRow l (readings ma) q (.ofWords a ma) → Visit pub mac l strict diagonal q a ma ys b mb → Next l I q b mb)
    {s m es t mt} (hm : I 0 (s 7) m) (run : Runs pub mac (scan strict diagonal) s m es t mt) :
    ∃ init a rows rest, es = init ++ rest ∧ Runs pub mac TeamRowPrepare.setup s m init a m ∧
      ReturnedRows pub mac l strict diagonal 0 a m rows rest t mt ∧
      I (l.d*l.d) (t 7) mt ∧ readings t 22 = l.d*l.d ∧ readings t 23 = l.d*l.d := by
  obtain ⟨init,a,ma,rest,rfl,start,loop⟩ := seq_split run
  obtain ⟨cur,bound,mem⟩ := ofBounded (by decide) (run_setup pub mac l s m fit frame (fields hm)) start
  have same : ma = m := funext fun j => Fin.ext (congrFun mem j)
  subst ma
  obtain ⟨rows,hr,hf,hc,hb⟩ := loop_decode_indexed I fit frame fields step (Nat.zero_add _)
    (start.keepsReg setup_keeps ▸ hm) cur bound loop
  exact ⟨init,a,rows,rest,rfl,start,hr,hf,hc,hb⟩

/-- Inversion with a memory-only invariant and protected outer registers. -/
theorem scan_decode {l : Layout} {strict diagonal : Code} {reachable : Memory w → Prop}
    (F : ScanFrame l strict diagonal reachable pub mac) (fit : l.Fits w) (frame : readings pub 0 = l.frame)
    {s m es t mt} (hm : reachable m) (run : Runs pub mac (scan strict diagonal) s m es t mt) :
    ∃ init a rows rest, es = init ++ rest ∧ Runs pub mac TeamRowPrepare.setup s m init a m ∧
      ReturnedRows pub mac l strict diagonal 0 a m rows rest t mt ∧
      reachable mt ∧ readings t 22 = l.d*l.d ∧ readings t 23 = l.d*l.d :=
  scan_decode_indexed (fun _ _ m => reachable m) fit frame (fun h => F.fields _ h)
    (fun hq h ready visit => ⟨F.visit hq h ready visit,visit_regs F ready visit⟩) hm run

private theorem Visit.run {l : Layout} {strict diagonal : Code} {q s m es t mt}
    (h : Visit pub mac l strict diagonal q s m es t mt) (ready : ReadyRow l (readings m) q (.ofWords s m)) :
    Runs pub mac (select strict diagonal) s m (tick w :: tick w :: es) t mt := by
  apply Runs.ifEq
  cases h with
  | skip miss =>
    rw [ite_eq_right ((owner_guard ready).not.mpr miss)]
    exact Runs.localStep _ rfl rfl
  | offDiagonal owned different run =>
    rw [ite_eq_left ((owner_guard ready).mpr owned)]
    apply Runs.ifEq
    simpa only [ite_eq_right ((symbols_guard ready).not.mpr different)] using run
  | onDiagonal owned equal run =>
    rw [ite_eq_left ((owner_guard ready).mpr owned)]
    apply Runs.ifEq
    simpa only [ite_eq_left ((symbols_guard ready).mpr equal)] using run

/-- Replay the recovered history, with its exact native events and return state. -/
theorem ReturnedRows.runs {l : Layout} {strict diagonal : Code} {q s m rows es t mt}
    (h : ReturnedRows pub mac l strict diagonal q s m rows es t mt) :
    Runs pub mac (.whileLt 22 23 (body strict diagonal)) s m es t mt := by
  induction h with
  | done cur bound =>
    apply Runs.whileDone
    change ¬ readings _ 22 < readings _ 23
    rw [cur,bound]
    exact Nat.lt_irrefl _
  | row inRange prep ready visit bump _ ih =>
    have cur := (congrArg Fin.val (prep.keepsReg (k := 22) (by decide))).symm.trans ready.cursor
    have bound := (congrArg Fin.val (prep.keepsReg (k := 23) (by decide))).symm.trans ready.bound
    refine Runs.whileStep ?_ (prep.seq ((visit.run ready).seq bump)) ih
    change readings _ 22 < readings _ 23
    simpa only [readings,cur,bound] using inRange

/-- Exact event histories of the native team scan are exactly the histories
formed by its fixed setup and the ordered, owner-checked row executions. -/
theorem scan_iff_returnedRows {l : Layout} {strict diagonal : Code} {reachable : Memory w → Prop}
    (F : ScanFrame l strict diagonal reachable pub mac) (fit : l.Fits w) (frame : readings pub 0 = l.frame)
    {s m es t mt} (hm : reachable m) :
    Runs pub mac (scan strict diagonal) s m es t mt ↔
      ∃ init a rows rest, es = init ++ rest ∧ Runs pub mac TeamRowPrepare.setup s m init a m ∧
        ReturnedRows pub mac l strict diagonal 0 a m rows rest t mt := by
  constructor
  · intro run
    obtain ⟨init,a,rows,rest,eqn,start,hr,_,_,_⟩ := scan_decode F fit frame hm run
    exact ⟨init,a,rows,rest,eqn,start,hr⟩
  · rintro ⟨_,_,_,_,rfl,start,hr⟩
    exact start.seq hr.runs

/-- A semantic history obtained from the returning roles. Its state boundaries
are the vertex-directory cursor and the entire shared memory, including every
scatter image. -/
inductive DecodedRows (step : ℕ → Word w → Memory w → List Bool → Word w → Memory w → Prop)
    (count : ℕ) : ℕ → Word w → Memory w → List (List Bool) → Word w → Memory w → Prop where
  | done {v m} : DecodedRows step count count v m [] v m
  | row {q v m bs u mu rows z mz} (decoded : step q v m bs u mu)
      (tail : DecodedRows step count (q+1) u mu rows z mz) :
      DecodedRows step count q v m (bs::rows) z mz

private theorem decode_history {l : Layout} {strict diagonal : Code} {q s m rows es t mt}
    (h : ReturnedRows pub mac l strict diagonal q s m rows es t mt)
    (I : ℕ → Word w → Memory w → Prop)
    (step : ℕ → Word w → Memory w → List Bool → Word w → Memory w → Prop)
    (decode : ∀ {k a ma ys b mb}, k < l.d*l.d → I k (a 7) ma →
      ReadyRow l (readings ma) k (.ofWords a ma) →
      Visit pub mac l strict diagonal k a ma ys b mb →
      step k (a 7) ma (ys.flatMap TeamRAM.Event.choices) (b 7) mb ∧ I (k+1) (b 7) mb ∧
        ∀ e ∈ ys, e.sign = .plus)
    (start : I q (s 7) m) :
    DecodedRows step (l.d*l.d) q (s 7) m (rows.map (List.flatMap TeamRAM.Event.choices)) (t 7) mt ∧
      I (l.d*l.d) (t 7) mt ∧ ∀ ys ∈ rows, ∀ e ∈ ys, e.sign = .plus := by
  induction h with
  | done => exact ⟨.done,start,by simp⟩
  | row inRange prep ready visit bump _ ih =>
    have prepared := prep.keepsReg prepare_keeps
    have advanced := bump.keepsReg (k := 7) (by decide)
    obtain ⟨sem,post,sgn⟩ := decode inRange (prepared ▸ start) ready visit
    obtain ⟨rest,done,sgns⟩ := ih (advanced ▸ post)
    refine ⟨.row (prepared ▸ sem) (advanced ▸ rest),done,?_⟩
    simpa only [List.forall_mem_cons] using And.intro sgn sgns

/-- Branch-specific semantic inversions compose along an actual returned scan.
Its recovered private words concatenate in order, all signs are positive, and
the semantic final state retains the returned vertex cursor and complete memory. -/
theorem scan_interpret {l : Layout} {strict diagonal : Code} {reachable : Memory w → Prop}
    (F : ScanFrame l strict diagonal reachable pub mac) (fit : l.Fits w) (frame : readings pub 0 = l.frame)
    (I : ℕ → Word w → Memory w → Prop)
    (step : ℕ → Word w → Memory w → List Bool → Word w → Memory w → Prop)
    (decode : ∀ {q a ma ys b mb}, q < l.d*l.d → I q (a 7) ma →
      ReadyRow l (readings ma) q (.ofWords a ma) →
      Visit pub mac l strict diagonal q a ma ys b mb →
      step q (a 7) ma (ys.flatMap TeamRAM.Event.choices) (b 7) mb ∧ I (q+1) (b 7) mb ∧
        ∀ e ∈ ys, e.sign = .plus)
    {s m es t mt} (hm : reachable m) (hi : I 0 (s 7) m)
    (run : Runs pub mac (scan strict diagonal) s m es t mt) :
    ∃ words : List (List Bool), words.length = l.d*l.d ∧
      DecodedRows step (l.d*l.d) 0 (s 7) m words (t 7) mt ∧
      TraceOK es words.flatten es.length ∧ I (l.d*l.d) (t 7) mt := by
  obtain ⟨init,a,rows,rest,rfl,first,hr,_,_,_⟩ := scan_decode F fit frame hm run
  have keep := first.keepsReg setup_keeps
  obtain ⟨sem,done,sgns⟩ := decode_history hr I step decode (keep ▸ hi)
  have startTrace := unsignedTrace first (by decide)
  have restTrace : TraceOK rest (rows.flatMap (List.flatMap TeamRAM.Event.choices)) rest.length :=
    ⟨rfl,hr.choices,hr.signs_iff.mpr sgns⟩
  refine ⟨_,by simpa using hr.length,keep ▸ sem,?_,done⟩
  simpa only [List.nil_append,List.length_append,← List.flatMap_def] using startTrace.append restTrace

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
