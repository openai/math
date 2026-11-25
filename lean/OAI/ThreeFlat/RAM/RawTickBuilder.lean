import OAI.ThreeFlat.RAM.TickLinkMemory
import OAI.ThreeFlat.RAM.CachedBlockCompose
import OAI.ThreeFlat.RAM.CachedProcedureRun
import OAI.ThreeFlat.RAM.OrdinalOpLoopNatural
import OAI.ThreeFlat.RAM.NativeOpRows
import OAI.ThreeFlat.RawTickLinks

namespace OAI
/-! # Native predecessor-link construction from eleven-word input cell records -/

namespace ThreeFlat.RAM.RawTickBuilder

open Computability.VPVNP.BurstRAM TickLinkRows RawTick Collapse.TickLinkScan BitLayout
open scoped Fin.CommRing
variable {F : Type*} {w p : ℕ} (N : BitNetwork F p)

def plan (raw last prev dst : ℕ) : Plan :=
  ⟨N.cells,RawTick.sources N.internal p,raw,last,prev,dst⟩

abbrev loaded (code : FieldCode F w) (base : ℕ) (m : Memory w) : Prop :=
  ∀ (i : Fin N.cells) (j : Fin 11), m (base+11*i.val+j.val) = record N code i j

theorem sources_loaded (code : FieldCode F w) (raw last prev dst : ℕ) (m : Memory w)
    (h : loaded N code raw m) : Loaded (plan N raw last prev dst) (RawTick.source N) m := by
  intro i hi
  change i<3*N.cells at hi
  let row : Fin N.cells := ⟨i/3,(Nat.div_lt_iff_lt_mul (by decide : 0<3)).mpr (by omega)⟩
  let col : Fin 3 := ⟨i%3,Nat.mod_lt _ (by decide)⟩
  let j : Fin 11 := ⟨col.val,by have := col.isLt; omega⟩
  have id : ordinal N (row,col)=i := by rw [ordinal_val]; dsimp [row,col]; omega
  have eq : record N code row j = (RawTick.source N (ordinal N (row,col)) : Word w) := by
    rw [source_at,sourceIndex_val]
    simp only [record,j,col.isLt,↓reduceDIte]
    rfl
  rw [id] at eq
  change m (raw+(11*(i/3)+i%3)) = _
  rw [← Nat.add_assoc]
  exact (h row j).trans eq

variable (raw lastBase prevBase dst : ℕ)
local notation "P" => plan N raw lastBase prevBase dst
local notation "S" => RawTick.sources N.internal p
local notation "K" => RawTick.sockets N.cells

/-- All indexed layout reads are valid in the returned memory. The input cell records
and every unrelated word remain accessible at their original addresses. -/
structure Result (m o : Memory w) : Prop where
  prevNat : ∀ i < (P).sockets, o (prevBase+i) = (prev S (RawTick.source N) i : Word w)
  lastNat : ∀ s < S, o (lastBase+s) = (last S (RawTick.source N) (P).sockets s : Word w)
  prevRead : ∀ (s : N.Source) (j : Fin (N.arity s)), o (prevBase+occurrence N s j) =
    ((edgeIndex N (.inl ⟨s,j.castSucc⟩)).val : Word w)
  lastRead : ∀ (s : N.Source), o (lastBase+(sourceIndex s).val) =
    ((edgeIndex N (.inl ⟨s,Fin.last (N.arity s)⟩)).val : Word w)
  dstRead : ∀ (s : N.Source) (j : Fin (N.arity s+1)), o (dst+(edgeIndex N (.inl ⟨s,j⟩)).val) =
    ((siteIndex N (N.copyDst (.inl ⟨s,j⟩))).val : Word w)
  outside : ∀ x, ¬(P).written x → o x=m x

theorem result {m o : Memory w} (h : TickLinkRows.Correct P (RawTick.source N) m o (P).sockets (P).sources) :
    Result N raw lastBase prevBase dst m o := by
  have k : (P).sockets=K := Nat.mul_comm ..
  refine ⟨h.prevAt,h.lastAt,?_,?_,?_,h.outside⟩
  · intro s j
    have inRange := occurrence_lt N s j
    rw [← k] at inRange
    exact (h.prevAt _ inRange).trans (congrArg (fun n : ℕ => (n : Word w)) (prev_occurrence N s j))
  · intro s
    have a := h.lastAt _ (sourceIndex s).isLt
    rw [k] at a
    exact a.trans (congrArg (fun n : ℕ => (n : Word w)) (last_source N s))
  · intro s j
    induction j using Fin.lastCases with
    | cast j =>
      have a := h.middleAt _ (show occurrence N s j<(P).sockets by rw [k]; exact occurrence_lt N s j)
      change o (dst + prev S (source N) (occurrence N s j)) =
        (middleSite N.cells S (occurrence N s j) : Word w) at a
      rw [prev_occurrence] at a
      refine a.trans (congrArg (fun n : ℕ => (n : Word w)) ?_)
      change middleSite N.cells S (occurrence N s j) =
        (siteIndex N (.inr ⟨s,j.castSucc.succ⟩)).val
      rw [site_middle]
      unfold middleSite occurrence
      omega
    | last =>
      have a := h.tailAt _ (sourceIndex s).isLt
      change o (dst + last S (source N) (P).sockets (sourceIndex s).val) =
        (tailSite N.cells S (P).sockets (sourceIndex s).val : Word w) at a
      rw [k,last_source] at a
      refine a.trans (congrArg (fun n : ℕ => (n : Word w)) ?_)
      change tailSite N.cells S K _ = (siteIndex N (.inr ⟨s,(Fin.last (N.arity s)).succ⟩)).val
      rw [site_tail]
      unfold tailSite
      omega

theorem build (code : FieldCode F w) (fit : (P).Fits w) : (builder w P).Spec (loaded N code raw)
    (Result N raw lastBase prevBase dst) (9+17*S+26*K) := by
  have k : (P).sockets=K := Nat.mul_comm ..
  intro pcs regs pubs M pc reg pub exit hi hd c m start hm
  obtain ⟨t,ht,out,mem,adv,done,good⟩ := builder_correct P (source N) fit
    (fun i hi => source_lt N i (k ▸ hi)) M pc reg pub exit hi hd c m start
    (sources_loaded N code raw lastBase prevBase dst m hm)
  change t ≤ 9+17*S+26*(P).sockets at ht
  rw [k] at ht
  exact ⟨t,ht,out,mem,adv,done,result N raw lastBase prevBase dst good⟩

end ThreeFlat.RAM.RawTickBuilder

namespace ThreeFlat.RAM.RawTickBuilder.Live

open Computability.VPVNP.BurstRAM PrivateRAM TickLinkRows PhysicalProcedure ContinuationLink CachedBlock
open scoped Fin.CommRing
variable {w pins labels regs slots : ℕ} {F : Type*} [Semiring F]

private def emptyPlan : Plan := ⟨0,0,0,0,0,0⟩

/-- All three loops share the same nine header locations. -/
def locations (loc : Fin 9 → Word w) : Fin 27 → Word w :=
  fun j => Fin.addCases (m := 18) (n := 9) (motive := fun _ => Word w)
    (fun i => Fin.addCases (m := 9) (n := 9) (motive := fun _ => Word w) loc loc i) loc j

private theorem phase_natural (w : ℕ) (P : Plan) (ph : Phase) :
    CachedBlock.Natural (procedure w P ph).block :=
  OrdinalOpLoop.block_natural w ph.ops 0 1 ph.limit

private theorem seq_natural {a b : Procedure w} (ha : Natural a.block) (hb : Natural b.block) :
    Natural (a.seq b).block :=
  Natural.seq (Natural.reindex ha (Fin.castAddEmb b.registers) (Fin.castAdd b.slots))
    (Natural.reindex hb (Fin.natAddEmb a.registers) (Fin.natAdd a.slots))

private theorem builder_natural (w : ℕ) (P : Plan) : Natural (builder w P).block :=
  seq_natural (seq_natural (phase_natural w P .init) (phase_natural w P .socket))
    (phase_natural w P .tail)

private theorem locations_read (P : Plan) (loc : Fin 9 → Word w) (m : Memory w)
    (input : ∀ j, m (loc j).val = P.data w j) (j : Fin 27) :
    m (locations loc j).val = (builder w P).publicData j := by
  change m (locations loc j).val = locations (P.data w) j
  refine Fin.addCases (m := 18) (n := 9) ?_ ?_ j
  · intro i
    refine Fin.addCases (m := 9) (n := 9) ?_ ?_ i <;> intro t <;>
      simpa only [locations, Fin.addCases_left, Fin.addCases_right] using input t
  · intro i
    simpa only [locations, Fin.addCases_right] using input i

/-- Fixed instructions for constructing predecessor, last-trunk and destination
arrays. Only the ordinary header values depend on the current network. -/
def block (loc : Fin 9 → Word w) : Block w 103 51 0 :=
  CachedBlock.lower (locations loc) (builder w emptyPlan).block

/-- The fixed ROM's operands are the only component supplied by the current plan. -/
private def mounted (w : ℕ) (P : Plan) : Procedure w :=
  ⟨49, 24, 27, (builder w emptyPlan).block, locations (P.data w)⟩

private theorem mounted_eq (w : ℕ) (P : Plan) : mounted w P = builder w P := rfl

omit [Semiring F] in
theorem run_advance (N : BitNetwork F pins) (raw lastBase prevBase dst : ℕ) (field : FieldCode F w)
    (fit : (plan N raw lastBase prevBase dst).Fits w) (loc : Fin 9 → Word w)
    (M : Machine w labels regs slots) (pc reg) (pub : Fin 0 → Fin slots) (exit : Fin labels)
    (rom : (block loc).Installed M pc reg pub exit) (c : Config w labels regs) (m : Memory w)
    (entry : c.pc=pc (block loc).first)
    (inputs : ∀ j, m (loc j).val=(plan N raw lastBase prevBase dst).data w j)
    (records : loaded N field raw m) :
    ∃ time≤54+(9+17*RawTick.sources N.internal pins+26*RawTick.sockets N.cells),
      ∃ z : Config w labels regs, ∃ out : Memory w,
        z.pc=exit ∧ Result N raw lastBase prevBase dst m out ∧
        advance M.program time c m=some (z,out) := by
  let P := plan N raw lastBase prevBase dst
  have spec : (mounted w P).Spec (loaded N field raw) (Result N raw lastBase prevBase dst)
      (9+17*RawTick.sources N.internal pins+26*RawTick.sockets N.cells) := by
    rw [mounted_eq]
    exact build N raw lastBase prevBase dst field fit
  exact CachedBlock.advance_procedure (mounted w P) spec (builder_natural w emptyPlan)
    (locations loc) M pc reg pub exit rom c m entry (locations_read P loc m inputs) records

theorem run (N : BitNetwork F pins) (raw lastBase prevBase dst : ℕ) (field : FieldCode F w)
    (fit : (plan N raw lastBase prevBase dst).Fits w) (loc : Fin 9 → Word w)
    (M : Machine w labels regs slots) (pc reg) (pub : Fin 0 → Fin slots) (exit : Fin labels)
    (rom : (block loc).Installed M pc reg pub exit) (c : Config w labels regs) (m : Memory w)
    (entry : c.pc=pc (block loc).first)
    (inputs : ∀ j, m (loc j).val=(plan N raw lastBase prevBase dst).data w j)
    (records : loaded N field raw m) :
    ∃ time≤54+(9+17*RawTick.sources N.internal pins+26*RawTick.sockets N.cells),
      ∃ z : Config w labels regs, ∃ out : Memory w,
        z.pc=exit ∧ Result N raw lastBase prevBase dst m out ∧
        ∀ fuel, mass field M.program (fuel+time) c m=mass field M.program fuel z out := by
  obtain ⟨t,ht,z,out,done,result,trace⟩ := run_advance N raw lastBase prevBase dst field fit loc M pc reg pub exit
    rom c m entry inputs records
  exact ⟨t,ht,z,out,done,result,fun fuel => mass_of_advance field M.program trace fuel⟩

end ThreeFlat.RAM.RawTickBuilder.Live

namespace ThreeFlat.RAM.RawTickBuilder.Live.Header

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM ContinuationLink
open scoped Fin.CommRing
variable {w n labels regs slots : ℕ} {F : Type*}

/-- Counts and allocator outputs stored by the current paired-network assembly. -/
def primitives (N : BitNetwork F (2*n)) (raw lastBase prevBase dst : ℕ) : Fin 7 → Word w :=
  ![(N.cells : Word w), N.internal, n, raw, lastBase, prevBase, dst]

def inputs (pub : Fin 19 → Word w) (m : Memory w) (i : Fin 7) : Word w :=
  m (pub (i.castAdd 12)).val

def targets (pub : Fin 19 → Word w) (j : Fin 12) : Word w := pub (Fin.natAdd 7 j)

private def values (x : Fin 7 → Word w) : Fin 12 → Word w :=
  let sources := (x 2+x 2+x 1)+2
  let sockets := 3*x 0
  ![sources,sockets,x 3,x 4,x 5,x 6,x 0+sources,x 0+sources+sockets,3*3+2,
    sources+sockets,(sources+sockets)+sockets,((x 0+sources+sockets)+sources)+x 2]

/-- Link ABI in slots zero through eight, then the trunk count, copy-edge count
and owner-plus-copy-site count used by endpoint publication and rank allocation. -/
def fields (N : BitNetwork F (2*n)) (raw lastBase prevBase dst w : ℕ) : Fin 12 → Word w :=
  fun j => Fin.addCases (m:=9) (n:=3) (motive:=fun _ => Word w)
    ((plan N raw lastBase prevBase dst).data w)
    ![((RawTick.sources N.internal (2*n)+RawTick.sockets N.cells : ℕ) : Word w),
      (RawTick.edges N.cells N.internal (2*n) : Word w),
      ((n+RawTick.sites N.cells N.internal (2*n) : ℕ) : Word w)] j

@[simp] theorem fields_link (N : BitNetwork F (2*n)) (raw lastBase prevBase dst w : ℕ) (i : Fin 9) :
    fields N raw lastBase prevBase dst w (i.castAdd 3)=(plan N raw lastBase prevBase dst).data w i :=
  Fin.addCases_left ..

private theorem values_eq (N : BitNetwork F (2*n)) (raw lastBase prevBase dst : ℕ) :
    values (primitives N raw lastBase prevBase dst : Fin 7 → Word w) =
      fields N raw lastBase prevBase dst w := by
  funext j
  refine Fin.addCases (m:=9) (n:=3) (motive:=fun i =>
    values (primitives N raw lastBase prevBase dst : Fin 7 → Word w) i =
      fields N raw lastBase prevBase dst w i) (fun i => ?_) (fun i => ?_) j <;>
    simp only [fields,Fin.addCases_left,Fin.addCases_right] <;> fin_cases i <;>
    simp [values,primitives,plan,TickLinkRows.Plan.data,TickLinkRows.Plan.sockets,
      RawTick.sources,RawTick.sockets,RawTick.edges,RawTick.sites] <;> ring

/-- Twelve ordinary cells shared by the link, endpoint and rank builders. -/
def written (loc : Fin 12 → Word w) (vals : Fin 12 → Word w) (m : Memory w) : Memory w :=
  ([0,1,2,3,4,5,6,7,8,9,10,11] : List (Fin 12)).foldl (fun o i => writeMemory o (loc i) (vals i)) m

theorem read (loc : Fin 12 → Word w) (vals : Fin 12 → Word w) (m : Memory w)
    (distinct : Function.Injective loc) (i : Fin 12) :
    written loc vals m (loc i).val=vals i := by
  have eq (j k : Fin 12) : (loc j).val=(loc k).val ↔ j=k :=
    ⟨fun e => distinct (Fin.ext e), fun e => congrArg (fun i => (loc i).val) e⟩
  fin_cases i <;> simp (config := {decide := true}) [written,writeMemory,eq]

theorem frame (loc : Fin 12 → Word w) (vals : Fin 12 → Word w) (m : Memory w) (a : ℕ)
    (away : ∀ i, a ≠ (loc i).val) : written loc vals m a=m a := by
  simp [written,writeMemory,away]

/-- Fetch all seven primitive operands before storing the derived header words.
The constant stride eleven is assembled from the instruction literals. -/
def ops (R : Fin 14 ↪ Fin regs) (φ : Fin 19 → Fin slots) : List (Op regs slots) :=
  [.publicWord (R 0) (φ 0), .read (R 0) (R 0),
   .publicWord (R 1) (φ 1), .read (R 1) (R 1),
   .publicWord (R 2) (φ 2), .read (R 2) (R 2),
   .publicWord (R 3) (φ 3), .read (R 3) (R 3),
   .publicWord (R 4) (φ 4), .read (R 4) (R 4),
   .publicWord (R 5) (φ 5), .read (R 5) (R 5),
   .publicWord (R 6) (φ 6), .read (R 6) (R 6),
   .binary .add (R 7) (R 2) (R 2), .binary .add (R 7) (R 7) (R 1),
   .constant (R 12) 2, .binary .add (R 7) (R 7) (R 12),
   .constant (R 11) 3, .binary .mul (R 8) (R 11) (R 0),
   .binary .add (R 9) (R 0) (R 7), .binary .add (R 10) (R 9) (R 8),
   .binary .mul (R 11) (R 11) (R 11), .binary .add (R 11) (R 11) (R 12),
   .binary .add (R 12) (R 7) (R 8), .binary .add (R 1) (R 12) (R 8),
   .binary .add (R 0) (R 10) (R 7), .binary .add (R 0) (R 0) (R 2),
   .publicWord (R 13) (φ 7), .write (R 13) (R 7),
   .publicWord (R 13) (φ 8), .write (R 13) (R 8),
   .publicWord (R 13) (φ 9), .write (R 13) (R 3),
   .publicWord (R 13) (φ 10), .write (R 13) (R 4),
   .publicWord (R 13) (φ 11), .write (R 13) (R 5),
   .publicWord (R 13) (φ 12), .write (R 13) (R 6),
   .publicWord (R 13) (φ 13), .write (R 13) (R 9),
   .publicWord (R 13) (φ 14), .write (R 13) (R 10),
   .publicWord (R 13) (φ 15), .write (R 13) (R 11),
   .publicWord (R 13) (φ 16), .write (R 13) (R 12),
   .publicWord (R 13) (φ 17), .write (R 13) (R 1),
   .publicWord (R 13) (φ 18), .write (R 13) (R 0)]

def block (w : ℕ) : Block w 52 14 19 where
  first := 0
  emit pc R φ exit := NativeRows.opRows w (ops R φ) (Fin.lastCases exit pc) exit

private theorem contains_straight (M : Machine w labels regs slots) (xs : List (Op regs slots))
    (pc : Fin xs.length ↪ Fin labels) (exit : Fin labels) (nonempty : 0 < xs.length)
    (rows : ∀ i, M.code (pc i) = NativeRows.opRows w xs
      (fun j => Fin.lastCases (motive:=fun _ => Fin labels) exit pc j) exit i) :
    Contains M exit (pc ⟨0, nonempty⟩) xs exit := by
  let loc : Fin (xs.length+1) → Fin labels := fun j =>
    Fin.lastCases (motive:=fun _ => Fin labels) exit pc j
  have linked := NativeRows.contains_opRows M exit xs loc (fun i => by
    simpa only [loc, Fin.lastCases_castSucc] using rows i)
  change Contains M exit (loc ((⟨0, nonempty⟩ : Fin xs.length).castSucc))
    xs (loc (Fin.last xs.length)) at linked
  simpa only [loc, Fin.lastCases_castSucc, Fin.lastCases_last] using linked

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1600000 in
theorem run (N : BitNetwork F (2*n)) (raw lastBase prevBase dst : ℕ)
    (M : Machine w labels regs slots) (pc : Fin 52 ↪ Fin labels) (R : Fin 14 ↪ Fin regs)
    (φ : Fin 19 → Fin slots) (exit : Fin labels) (rom : (block w).Installed M pc R φ exit)
    (c : Config w labels regs) (m : Memory w) (entry : c.pc=pc 0)
    (src : ∀ i, inputs (M.publicData ∘ φ) m i=primitives N raw lastBase prevBase dst i) :
    ∃ z : Config w labels regs, advance M.program 52 c m=some (z,
      written (targets (M.publicData ∘ φ)) (fields N raw lastBase prevBase dst w) m) ∧
      z.pc=exit ∧ z.persistent=c.persistent ∧ z.privateMem=c.privateMem ∧
      ∀ j, (∀ i, j ≠ R i) → z.reg j=c.reg j := by
  have linked := contains_straight M (ops R φ) pc exit (show 0 < 52 by decide) rom
  obtain ⟨es,rs,o,exec⟩ : ∃ es rs o,
      trace M.publicData c.persistent (ops R φ) c.reg m=some (es,rs,o) := ⟨_,_,_,rfl⟩
  have same : o=written (targets (M.publicData ∘ φ)) (values (inputs (M.publicData ∘ φ) m)) m := by
    have h := congrArg (Option.map (fun z : List (Event w) × Regs w regs × Memory w => z.2.2)) exec
    simpa (config := {decide := true}) [ops,trace,Op.effect,Function.update_apply,R.injective.eq_iff,
      written,targets,values,inputs,Function.comp_apply,
      show ∀ a b : Word w, BinaryOp.add.eval a b=a+b from fun _ _ => rfl,
      show ∀ a b : Word w, BinaryOp.mul.eval a b=a*b from fun _ _ => rfl] using h.symm
  rw [show inputs (M.publicData ∘ φ) m=primitives N raw lastBase prevBase dst from funext src,
    values_eq] at same
  have step := HistoryBucketEmitter.advance_trace linked c.persistent c.reg rs c.privateMem m o es exec
  rw [same] at step
  refine ⟨⟨exit,c.persistent,rs,c.privateMem⟩,?_,rfl,rfl,rfl,?_⟩
  · cases c
    change _=pc 0 at entry
    subst_vars
    exact step
  · intro j away
    have h := congrArg (Option.map (fun z : List (Event w) × Regs w regs × Memory w => z.2.1 j)) exec
    simpa (config := {decide := true}) [ops,trace,Op.effect,Function.update_apply,away] using h.symm

end ThreeFlat.RAM.RawTickBuilder.Live.Header

namespace ThreeFlat.RAM.RawTickBuilder.Live

open Computability.VPVNP.BurstRAM PrivateRAM ContinuationLink
open scoped Fin.CommRing
variable {w n labels regs slots : ℕ} {F : Type*} [Semiring F]

private def headerRegs : Fin 14 ↪ Fin 51 := Fin.castLEEmb (by decide)

/-- The ordinary header writer falls through to the cached three-phase builder. -/
def prepared (loc : Fin 12 → Word w) : Block w 155 51 19 :=
  ((Header.block w).reindex headerRegs id).seq
    ((block (loc ∘ Fin.castAdd 3)).reindex (Function.Embedding.refl _) Fin.elim0)

omit [Semiring F] in
/-- Execute from the seven primitive cells and the real eleven-word cell
records. The result exposes the twelve header words in the final memory as
well as all three link arrays and an explicit frame for other addresses. -/
theorem run_prepared_advance (N : BitNetwork F (2*n)) (raw lastBase prevBase dst : ℕ) (field : FieldCode F w)
    (fit : (plan N raw lastBase prevBase dst).Fits w) (loc : Fin 12 → Word w)
    (distinct : Function.Injective loc) (M : Machine w labels regs slots)
    (pc : Fin 155 ↪ Fin labels) (reg : Fin 51 ↪ Fin regs) (φ : Fin 19 → Fin slots) (exit : Fin labels)
    (rom : (prepared loc).Installed M pc reg φ exit) (c : Config w labels regs) (m : Memory w)
    (entry : c.pc=pc (prepared loc).first)
    (publicCells : Header.targets (M.publicData ∘ φ)=loc)
    (src : ∀ i, Header.inputs (M.publicData ∘ φ) m i=Header.primitives N raw lastBase prevBase dst i)
    (records : loaded N field raw m)
    (rawSafe : ∀ (i : Fin N.cells) (j : Fin 11) (t : Fin 12), raw+11*i.val+j.val ≠ (loc t).val)
    (headerSafe : ∀ t, ¬ (plan N raw lastBase prevBase dst).written (loc t).val) :
    let vals := Header.fields N raw lastBase prevBase dst w
    let start := Header.written loc vals m
    ∃ time≤106+(9+17*RawTick.sources N.internal (2*n)+26*RawTick.sockets N.cells),
      ∃ z : Config w labels regs, ∃ out : Memory w, z.pc=exit ∧
        Result N raw lastBase prevBase dst start out ∧
        (∀ i, out (loc i).val=vals i) ∧
        (∀ a, ¬ (plan N raw lastBase prevBase dst).written a → (∀ i, a≠(loc i).val) → out a=m a) ∧
        advance M.program time c m=some (z,out) := by
  let vals := Header.fields N raw lastBase prevBase dst w
  let start := Header.written loc vals m
  obtain ⟨a,b⟩ := (Block.seq_installed ((Header.block w).reindex headerRegs id)
    ((block (loc ∘ Fin.castAdd 3)).reindex (Function.Embedding.refl _) Fin.elim0)
    M pc reg φ exit).mp rom
  obtain ⟨s,boot,next,_,_,_⟩ := Header.run N raw lastBase prevBase dst M ((Fin.castAddEmb 103).trans pc)
    (headerRegs.trans reg) φ (pc (Fin.natAdd 52 (block (loc ∘ Fin.castAdd 3)).first)) a c m entry src
  rw [publicCells] at boot
  have held (i : Fin 9) : start ((loc ∘ Fin.castAdd 3) i).val=(plan N raw lastBase prevBase dst).data w i :=
    (Header.read loc vals m distinct (i.castAdd 3)).trans (Header.fields_link ..)
  have still : loaded N field raw start :=
    fun i j => (Header.frame loc vals m _ (rawSafe i j)).trans (records i j)
  obtain ⟨t,ht,z,out,done,result,act⟩ := run_advance N raw lastBase prevBase dst field fit
    (loc ∘ Fin.castAdd 3) M ((Fin.natAddEmb 52).trans pc) reg (φ ∘ Fin.elim0) exit b s start next held still
  refine ⟨52+t,by omega,z,out,done,result,?_,?_,?_⟩
  · intro i
    exact (result.outside _ (headerSafe i)).trans (Header.read loc vals m distinct i)
  · intro a low elsewhere
    exact (result.outside a low).trans (Header.frame loc vals m a elsewhere)
  · exact advance_trans boot act

theorem run_prepared (N : BitNetwork F (2*n)) (raw lastBase prevBase dst : ℕ) (field : FieldCode F w)
    (fit : (plan N raw lastBase prevBase dst).Fits w) (loc : Fin 12 → Word w)
    (distinct : Function.Injective loc) (M : Machine w labels regs slots)
    (pc : Fin 155 ↪ Fin labels) (reg : Fin 51 ↪ Fin regs) (φ : Fin 19 → Fin slots) (exit : Fin labels)
    (rom : (prepared loc).Installed M pc reg φ exit) (c : Config w labels regs) (m : Memory w)
    (entry : c.pc=pc (prepared loc).first)
    (publicCells : Header.targets (M.publicData ∘ φ)=loc)
    (src : ∀ i, Header.inputs (M.publicData ∘ φ) m i=Header.primitives N raw lastBase prevBase dst i)
    (records : loaded N field raw m)
    (rawSafe : ∀ (i : Fin N.cells) (j : Fin 11) (t : Fin 12), raw+11*i.val+j.val ≠ (loc t).val)
    (headerSafe : ∀ t, ¬ (plan N raw lastBase prevBase dst).written (loc t).val) :
    let vals := Header.fields N raw lastBase prevBase dst w
    let start := Header.written loc vals m
    ∃ time≤106+(9+17*RawTick.sources N.internal (2*n)+26*RawTick.sockets N.cells),
      ∃ z : Config w labels regs, ∃ out : Memory w, z.pc=exit ∧
        Result N raw lastBase prevBase dst start out ∧
        (∀ i, out (loc i).val=vals i) ∧
        (∀ a, ¬ (plan N raw lastBase prevBase dst).written a → (∀ i, a≠(loc i).val) → out a=m a) ∧
        ∀ fuel, mass field M.program (fuel+time) c m=mass field M.program fuel z out := by
  obtain ⟨t,ht,z,out,done,result,reads,frame,trace⟩ := run_prepared_advance N raw lastBase prevBase dst field fit loc
    distinct M pc reg φ exit rom c m entry publicCells src records rawSafe headerSafe
  exact ⟨t,ht,z,out,done,result,reads,frame,fun fuel => mass_of_advance field M.program trace fuel⟩

end ThreeFlat.RAM.RawTickBuilder.Live

namespace ThreeFlat.RAM.RawTickBuilder.Live.Header

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.PrimedStackRAM ContinuationLink
open scoped Fin.CommRing
variable {w n labels regs slots : ℕ} {F : Type*}

private def stopOps (R : Fin 5 ↪ Fin regs) (φ : Fin 5 → Fin slots) : List (Op regs slots) :=
  [.publicWord (R 0) (φ 0), .read (R 0) (R 0),
   .publicWord (R 1) (φ 1), .read (R 1) (R 1),
   .publicWord (R 2) (φ 2), .read (R 2) (R 2),
   .constant (R 3) 3, .binary .add (R 4) (R 3) (R 3),
   .binary .mul (R 0) (R 4) (R 0), .binary .add (R 2) (R 2) (R 2),
   .binary .add (R 1) (R 1) (R 2), .binary .add (R 1) (R 1) (R 2),
   .constant (R 3) 2, .binary .add (R 1) (R 1) (R 3),
   .binary .add (R 1) (R 1) (R 0), .binary .mul (R 1) (R 1) (R 4),
   .publicWord (R 0) (φ 3), .binary .add (R 1) (R 0) (R 1),
   .publicWord (R 0) (φ 4), .write (R 0) (R 1)]

/-- Establish the endpoint publisher's tape stop directly from the live
cell, hidden-source and owner counts before entering the link builder. -/
def endpointStop (w : ℕ) : Block w 20 5 5 where
  first := 0
  emit pc R φ exit := NativeRows.opRows w (stopOps R φ) (Fin.lastCases exit pc) exit

set_option maxRecDepth 4096 in
theorem run_endpointStop (N : BitNetwork F (2*n)) (tape : ℕ)
    (M : Machine w labels regs slots) (pc : Fin 20 ↪ Fin labels) (R : Fin 5 ↪ Fin regs)
    (φ : Fin 5 → Fin slots) (exit : Fin labels) (rom : (endpointStop w).Installed M pc R φ exit)
    (c : Config w labels regs) (m : Memory w) (entry : c.pc=pc 0)
    (cells : m (M.publicData (φ 0)).val=(N.cells : Word w))
    (internal : m (M.publicData (φ 1)).val=(N.internal : Word w))
    (owners : m (M.publicData (φ 2)).val=(n : Word w))
    (tapeWord : M.publicData (φ 3)=(tape : Word w)) :
    ∃ z : Config w labels regs, advance M.program 20 c m=some (z,writeMemory m (M.publicData (φ 4))
      ((tape+6*(RawTick.edges N.cells N.internal (2*n)+2*n) : ℕ) : Word w)) ∧
      z.pc=exit ∧ z.persistent=c.persistent ∧ z.privateMem=c.privateMem ∧
      ∀ j, (∀ i, j ≠ R i) → z.reg j=c.reg j := by
  have linked := contains_straight M (stopOps R φ) pc exit (show 0 < 20 by decide) rom
  obtain ⟨es,rs,o,exec⟩ : ∃ es rs o,
      trace M.publicData c.persistent (stopOps R φ) c.reg m=some (es,rs,o) := ⟨_,_,_,rfl⟩
  have arith : (tape : Word w)+(((N.internal : Word w)+((n : Word w)+n)+((n : Word w)+n)+2+(3+3)*(N.cells : Word w))*(3+3)) =
      ((tape+6*(RawTick.edges N.cells N.internal (2*n)+2*n) : ℕ) : Word w) := by
    simp only [RawTick.edges,RawTick.sockets,RawTick.sources,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat]
    ring
  have same : o=writeMemory m (M.publicData (φ 4))
      ((tape+6*(RawTick.edges N.cells N.internal (2*n)+2*n) : ℕ) : Word w) := by
    have h := congrArg (Option.map (fun z : List (Event w) × Regs w regs × Memory w => z.2.2)) exec
    rw [← arith]
    simpa (config := {decide := true}) [stopOps,trace,Op.effect,R.injective.eq_iff,Function.update_apply,
      show ∀ a b : Word w, BinaryOp.add.eval a b=a+b from fun _ _ => rfl,
      show ∀ a b : Word w, BinaryOp.mul.eval a b=a*b from fun _ _ => rfl,
      cells,internal,owners,tapeWord] using h.symm
  have step := HistoryBucketEmitter.advance_trace linked c.persistent c.reg rs c.privateMem m o es exec
  rw [same] at step
  refine ⟨⟨exit,c.persistent,rs,c.privateMem⟩,?_,rfl,rfl,rfl,?_⟩
  · cases c
    change _=pc 0 at entry
    subst_vars
    exact step
  · intro j away
    have h := congrArg (Option.map (fun z : List (Event w) × Regs w regs × Memory w => z.2.1 j)) exec
    simpa (config := {decide := true}) [stopOps,trace,Op.effect,Function.update_apply,away] using h.symm

end ThreeFlat.RAM.RawTickBuilder.Live.Header

end OAI
