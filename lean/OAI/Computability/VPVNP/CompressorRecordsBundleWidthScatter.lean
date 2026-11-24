import OAI.Computability.VPVNP.CompressorRecordsPortRankScan
import OAI.Computability.VPVNP.CompressorRecordsBundleLists

/-!
# Sorting the old widths by absolute bundle and rank

One burst call per old outgoing port reads its bucket, its rank, and its width.
It copies the width directly into that rank of the corresponding bundle row.
Each row is visited in old-port scan order but is stored in sorted key order.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleWidthScatter

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM Compression Compression.PackingData BundleLists

variable {w : ℕ}

/-- The scatter worker reads one old port's bucket, rank, and width, stores the width in the
ranked bundle row, and advances the cursor. -/
def visit : List (Op 7 5) :=
  [.stateWord 0, .publicWord 1 0, .binary .add 1 1 0, .read 2 1,
   .publicWord 1 1, .binary .add 1 1 0, .read 3 1,
   .publicWord 1 2, .binary .add 1 1 0, .read 4 1,
   .publicWord 1 3, .binary .mul 2 2 1, .publicWord 1 4, .binary .add 2 1 2,
   .binary .add 2 2 3, .write 2 4, .constant 1 1, .binary .add 0 0 1]

/-- Address of the current old port in one of the three input columns for bucket, rank, and
width. -/
def source (p : Fin 5 → Word w) (t : Fin 3) (i : Word w) : Word w :=
  p (t.castAdd 2)+i

/-- Address of the width's destination, determined by the port's bucket, the public row stride,
and its rank. -/
def outAddress (p : Fin 5 → Word w) (m : Memory w) (i : Word w) : Word w :=
  p 4 + m (source p 0 i).val * p 3 + m (source p 1 i).val

/-- Read the width of the current old port from the third input column. -/
def width (p : Fin 5 → Word w) (m : Memory w) (i : Word w) : Word w := m (source p 2 i).val

/-- The ticks, three input reads, and single width write made by one scatter visit. -/
def events (p : Fin 5 → Word w) (m : Memory w) (i : Word w) : List (Event w) :=
  let read (t : Fin 3) := Event.read (source p t i) (m (source p t i).val)
  [.tick,.tick,.tick,read 0,.tick,.tick,read 1,.tick,.tick,read 2,
   .tick,.tick,.tick,.tick,.tick,.write (outAddress p m i) (width p m i),.tick,.tick]

theorem native (p : Fin 5 → Word w) (m : Memory w) (i : Word w) :
    let M := (template visit 0).instantiate w p
    execute M.program 19 (M.program.start i) m [] = some ⟨events p m i,some (i+1)⟩ := by
  change execute ((template visit 0).instantiate w p).program (1+visit.length)
    ⟨_,i,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _
  rw [execute_template, run_eq_trace]
  rfl

/-- Represent a natural scan index as a machine word of the scatter worker's width. -/
abbrev word (j : ℕ) : Word w := Fin.ofNat _ j

/-- Exactly the occupied width cells of the scanned prefix have been written. -/
structure Filled (p : Fin 5 → Word w) (initial m : Memory w) (k : ℕ)
    (payload : Word w → Word w → Word w := fun _ x ↦ x) : Prop where
  readback : ∀ j < k, m (outAddress p initial (word j)).val = payload (word j) (width p initial (word j))
  frame : ∀ a, (∀ j < k, a ≠ (outAddress p initial (word j)).val) → m a = initial a

/-- The input cells are disjoint from all scatter destinations, and distinct live ports have
distinct destinations. -/
structure Regions (p : Fin 5 → Word w) (initial : Memory w) (A : ℕ) : Prop where
  apart : ∀ t j, j < A → ∀ l < A, (source p t (word j)).val ≠ (outAddress p initial (word l)).val
  unique : ∀ j < A, ∀ l < A, outAddress p initial (word j) = outAddress p initial (word l) → j = l

private theorem filled_step {p : Fin 5 → Word w} {initial m : Memory w} {k A : ℕ}
    {payload : Word w → Word w → Word w} (reg : Regions p initial A)
    (prior : Filled p initial m k payload) (hk : k < A) :
    Filled p initial (writeMemory m (outAddress p m (word k))
      (payload (word k) (width p m (word k)))) (k+1) payload := by
  have read (t : Fin 3) : m (source p t (word k)).val = initial (source p t (word k)).val :=
    prior.frame _ (fun j hj ↦ reg.apart t k hk j (hj.trans hk))
  have ha : outAddress p m (word k) = outAddress p initial (word k) := by simp only [outAddress, read]
  have hw : width p m (word k) = width p initial (word k) := read 2
  rw [ha,hw]
  constructor
  · intro j hj
    by_cases he : j = k
    · simp [he,writeMemory]
    · have hne : (outAddress p initial (word j)).val ≠ (outAddress p initial (word k)).val :=
        fun h ↦ he (reg.unique j (by omega) k hk (Fin.ext h))
      simpa only [writeMemory, ite_eq_right hne] using prior.readback j (by omega)
  · intro a outside
    rw [writeMemory, ite_eq_right (outside k (by omega))]
    exact prior.frame _ (fun j hj ↦ outside j (by omega))

/-- Scatter a word computed from the port index and the third input column.
All workers using this layout share the same address, frame and cost proof. -/
theorem scatter_values {C : Type*} (program : Program w C) (fuel ticks : ℕ)
    (p : Fin 5 → Word w) (initial : Memory w) (A : ℕ) (reg : Regions p initial A)
    (payload : Word w → Word w → Word w)
    (worker : ∀ (mem : Memory w) (i : Word w), ∃ es,
      execute program fuel (program.start i) mem [] = some ⟨es,some (i+1)⟩ ∧
      after mem es = writeMemory mem (outAddress p mem i) (payload i (width p mem i)) ∧
      es.length = ticks ∧ countProbes es = 4) :
    ∃ rs, runSegment program fuel (some 0) initial (List.replicate A []) = some rs ∧
      endState (some 0) rs = some (word A) ∧ Filled p initial (after initial (eventLog rs)) A payload ∧
      rs.length = A ∧ (∀ r ∈ rs, r.events.length = ticks ∧ r.probes = 4) ∧ RAMBuckets.cost Report.probes rs = 5*A := by
  have aux (n k : ℕ) (m : Memory w) (prior : Filled p initial m k payload) (hk : k+n ≤ A) :
      ∃ rs, runSegment program fuel (some (word k)) m (List.replicate n []) = some rs ∧
        endState (some (word k)) rs = some (word (k+n)) ∧ Filled p initial (after m (eventLog rs)) (k+n) payload ∧
        rs.length = n ∧ (∀ r ∈ rs, r.events.length = ticks ∧ r.probes = 4) ∧ RAMBuckets.cost Report.probes rs = 5*n := by
    induction n generalizing k m with
    | zero => exact ⟨[],rfl,rfl,prior,rfl,by simp,rfl⟩
    | succ n ih =>
      obtain ⟨es,he,hm,hl,hp⟩ := worker m (word k)
      let r : Report w := ⟨es,some (word k+1)⟩
      have hn : word (w := w) k+1 = word (k+1) := by
        apply Fin.ext
        simp [word, Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]
      have eqn : (k+1)+n = k+(n+1) := by omega
      have next : Filled p initial (after m es) (k+1) payload := hm ▸ filled_step reg prior (by omega)
      obtain ⟨rs,hr,hs,hf,hlen,hw,hc⟩ := ih (k+1) (after m es) next (by omega)
      refine ⟨r::rs, ?_, ?_, ?_, by simp [hlen], ?_, ?_⟩
      · rw [List.replicate_succ, runSegment, he, hn]
        simpa only [r, hn, Option.map_some] using congrArg (Option.map (r :: ·)) hr
      · change endState (some (word k+1)) rs = _
        rw [hn,hs,eqn]
      · change Filled p initial ((es ++ eventLog rs).foldl BurstRAM.update m) _ payload
        rw [List.foldl_append, ← eqn]; exact hf
      · intro s h
        rcases List.mem_cons.mp h with rfl | h
        · exact ⟨hl,hp⟩
        · exact hw s h
      · rw [RAMBuckets.cost, show r.probes = 4 from hp, hc, Nat.mul_succ]; omega
  simpa only [word, Fin.ofNat_zero, Nat.zero_add] using aux A 0 initial ⟨by simp, fun _ _ ↦ rfl⟩ (by omega)

/-- Complete native scatter, with a frame also covering holes inside the rectangle. -/
theorem run (p : Fin 5 → Word w) (initial : Memory w) (A : ℕ) (reg : Regions p initial A) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 19 (some 0) initial (List.replicate A []) = some rs ∧
      endState (some 0) rs = some (word A) ∧ Filled p initial (after initial (eventLog rs)) A ∧
      rs.length = A ∧ (∀ r ∈ rs, r.events.length = 18 ∧ r.probes = 4) ∧ RAMBuckets.cost Report.probes rs = 5*A := by
  apply scatter_values _ _ _ p initial A reg (fun _ x ↦ x)
  exact fun m i ↦ ⟨events p m i,native p m i,rfl,rfl,rfl⟩

variable {V H Tag L : Type} {d c n A : ℕ}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c) (cd : P.BundleNumbering) (dd : P.ThickNumbering)

/-- Each old arc belongs to exactly one of the two finite fibers, numbered by
the piece order for CD and the concatenation order for DD. -/
def fiberNumber : (b : Bucket V Tag L d) → {a // bucketOf P a = b} ≃ Fin (rowLength (c := c) b)
  | .inl b => (thickEquiv P b).trans (dd b)
  | .inr b => (motifEquiv P b).trans (cd b)

/-- The arc's position in its assigned bucket under the supplied ordering of CD motifs or thick
wires. -/
def rankOf (a : Arc V H Tag L d c) : ℕ :=
  (fiberNumber P cd dd (bucketOf P a) ⟨a,rfl⟩).val

private theorem rank_at {a : Arc V H Tag L d c} {b} (ha : bucketOf P a = b) :
    rankOf P cd dd a = (fiberNumber P cd dd b ⟨a,ha⟩).val := by subst b; rfl

theorem rank_thick {b : Port V Tag L d} (x : P.ThickFiber b) :
    rankOf P cd dd x.1.1 = (dd b x).val := by
  rw [rank_at P cd dd ((bucketOf_thick P x.1).trans (congrArg Sum.inl x.2))]
  rfl

theorem rank_motif {b : Port V Tag L d} (x : P.MotifFiber b) :
    rankOf P cd dd x.1.1 = (cd b x).val := by
  rw [rank_at P cd dd ((bucketOf_motif P x.1).trans (congrArg Sum.inr x.2))]
  rfl

private theorem arc_eq_of_rank {a a' : Arc V H Tag L d c}
    (h : bucketOf P a = bucketOf P a') (r : rankOf P cd dd a = rankOf P cd dd a') : a = a' := by
  rw [rank_at P cd dd h, rank_at P cd dd (a := a') rfl] at r
  exact congrArg Subtype.val ((fiberNumber P cd dd _).injective (Fin.ext r))

variable (arcs : Arc V H Tag L d c ≃ Fin A) (site : Site V Tag L ≃ Fin n)

/-- Absolute old-port identifier, shared by the width, rank, and owner columns. -/
abbrev arcWord (a : Arc V H Tag L d c) : Word w := word (arcs a).val

/-- Contents of the three columns consumed by the width scatter. -/
structure RankedInput (p : Fin 5 → Word w) (m : Memory w) (old : Arc V H Tag L d c → ℕ) : Prop where
  owners : ∀ a, m (source p 0 (arcWord arcs a)).val = word (bucketIndex site (bucketOf P a)).val
  ranks : ∀ a, m (source p 1 (arcWord arcs a)).val = word (rankOf P cd dd a)
  widths : ∀ a, (m (source p 2 (arcWord arcs a)).val).val = old a

/-- Both sets of rows share a stride. The three input arrays can occupy any
intervals disjoint from the output rectangle. -/
structure Layout (p : Fin 5 → Word w) (A n d c : ℕ) : Prop where
  slots : pieceCount d c ≤ (p 3).val
  bucketsFit : n*d+n*d ≤ 2^w
  sourceFits : ∀ t : Fin 3, (p (t.castAdd 2)).val+A ≤ 2^w
  rectangle : (p 4).val+(n*d+n*d)*(p 3).val ≤ 2^w
  apart : ∀ t : Fin 3, (p (t.castAdd 2)).val+A ≤ (p 4).val ∨
    (p 4).val+(n*d+n*d)*(p 3).val ≤ (p (t.castAdd 2)).val

private theorem slot_lt {p : Fin 5 → Word w} (layout : Layout p A n d c)
    (a : Arc V H Tag L d c) : rankOf P cd dd a < (p 3).val := by
  apply (fiberNumber P cd dd _ ⟨a,rfl⟩).isLt.trans_le
  apply le_trans _ layout.slots
  cases bucketOf P a with
  | inl b => change 2^c*d/4 ≤ 3*(2^c*d)/4; omega
  | inr b => rfl

private def offset (site : Site V Tag L ≃ Fin n) (stride : ℕ) (a : Arc V H Tag L d c) : ℕ :=
  (bucketIndex site (bucketOf P a)).val * stride + rankOf P cd dd a

private theorem offset_lt {p : Fin 5 → Word w} (layout : Layout p A n d c)
    (a : Arc V H Tag L d c) : offset P cd dd site (p 3).val a < (n*d+n*d)*(p 3).val := by
  have hb := Nat.mul_le_mul_right (p 3).val (bucketIndex site (bucketOf P a)).isLt
  rw [Nat.succ_mul] at hb
  have hs := slot_lt P cd dd layout a
  dsimp [offset]
  omega

theorem output_eq {p : Fin 5 → Word w} {initial : Memory w} {old : Arc V H Tag L d c → ℕ}
    (layout : Layout p A n d c) (h : RankedInput P cd dd arcs site p initial old)
    (a : Arc V H Tag L d c) : (outAddress p initial (arcWord arcs a)).val =
      (p 4).val + offset P cd dd site (p 3).val a := by
  rw [outAddress,h.owners,h.ranks]
  have hs := slot_lt P cd dd layout a
  have fit := layout.rectangle
  have bound := offset_lt P cd dd site layout a
  dsimp [offset] at bound ⊢
  rw [Fin.val_add, Fin.val_add, Fin.val_mul, Fin.val_natCast, Fin.val_natCast,
    Nat.mod_eq_of_lt ((bucketIndex site _).isLt.trans_le layout.bucketsFit),
    Nat.mod_eq_of_lt (hs.trans (p 3).isLt), Nat.mod_add_mod, Nat.mod_eq_of_lt (show (bucketIndex site (bucketOf P a)).val * (p 3).val < 2^w by omega), Nat.mod_eq_of_lt (by omega)]
  omega

private theorem offset_inj {p : Fin 5 → Word w} (layout : Layout p A n d c) :
    Function.Injective (offset P cd dd site (p 3).val) := by
  intro a a' he
  have h := slot_lt P cd dd layout a
  have h' := slot_lt P cd dd layout a'
  unfold offset at he
  have hr := congrArg (· % (p 3).val) he
  rw [Nat.mul_add_mod_of_lt h,Nat.mul_add_mod_of_lt h'] at hr
  rw [hr, Nat.add_right_cancel_iff] at he
  have hq := Nat.eq_of_mul_eq_mul_right (Nat.zero_lt_of_lt h) he
  exact arc_eq_of_rank P cd dd ((bucketIndex site).injective (Fin.ext hq)) hr

theorem regions_of_layout {p : Fin 5 → Word w} {initial : Memory w} {old : Arc V H Tag L d c → ℕ}
    (layout : Layout p A n d c) (h : RankedInput P cd dd arcs site p initial old) : Regions p initial A := by
  have eqv (j : ℕ) (hj : j < A) :
      (outAddress p initial (word j)).val = (p 4).val + offset P cd dd site (p 3).val (arcs.symm ⟨j,hj⟩) := by
    simpa [arcWord] using output_eq P cd dd arcs site layout h (arcs.symm ⟨j,hj⟩)
  constructor
  · intro t j hj l hl
    have ht := layout.sourceFits t
    have hr := offset_lt P cd dd site layout (arcs.symm ⟨l,hl⟩)
    rw [eqv l hl, source, Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]
    rcases layout.apart t with hs | hs <;> omega
  · intro j hj l hl e
    have he := congrArg Fin.val e
    rw [eqv j hj, eqv l hl, Nat.add_left_cancel_iff] at he
    have ha := offset_inj P cd dd site layout he
    exact congrArg Fin.val (arcs.symm.injective ha)

/-- First width word of a chosen absolute bundle. -/
def rowBase (p : Fin 5 → Word w) (site : Site V Tag L ≃ Fin n) (b : Bucket V Tag L d) : Word w :=
  p 4 + word (bucketIndex site b).val * p 3

omit [AddCommGroup Tag] [AddCommGroup L] in
theorem rowBase_val {p : Fin 5 → Word w} (layout : Layout p A n d c)
    (b : Bucket V Tag L d) :
    (rowBase p site b).val = (p 4).val + (bucketIndex site b).val*(p 3).val := by
  have he := Nat.mul_le_mul_right (p 3).val (bucketIndex site b).isLt
  rw [Nat.succ_mul] at he
  have hf := layout.rectangle
  rw [rowBase, Fin.val_add, Fin.val_mul, Fin.val_ofNat, Nat.mod_eq_of_lt ((bucketIndex site b).isLt.trans_le
    layout.bucketsFit), Nat.add_mod_mod]
  apply Nat.mod_eq_of_lt
  by_cases hz : (p 3).val = 0
  · simp [hz]
  · omega

/-- Scattering directly from the absolute-port rank and width columns yields
the sorted concatenation at both bundle ends and the CD piece widths in their
own order. The scan consumes exactly five calls-plus-probes units per old port. -/
theorem graph_run (p : Fin 5 → Word w) (initial : Memory w) (old : Arc V H Tag L d c → ℕ)
    (layout : Layout p A n d c) (h : RankedInput P cd dd arcs site p initial old) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 19 (some 0) initial (List.replicate A []) = some rs ∧
      endState (some 0) rs = some (word A) ∧ Filled p initial (after initial (eventLog rs)) A ∧
      rs.length = A ∧ (∀ r ∈ rs, r.events.length = 18 ∧ r.probes = 4) ∧ RAMBuckets.cost Report.probes rs = 5*A ∧
      (∀ b i, (after initial (eventLog rs) ((rowBase p site (.inl b)).val+i.val)).val =
        old ((dd b).symm i).1.1) ∧
      (∀ b i, (after initial (eventLog rs) ((rowBase p site (.inr b)).val+i.val)).val =
        old ((cd b).symm i).1.1) := by
  obtain ⟨rs,hr,hc,hf,hl,hw,cost⟩ := run p initial A (regions_of_layout P cd dd arcs site layout h)
  have atArc (a : Arc V H Tag L d c) :
      (after initial (eventLog rs) ((rowBase p site (bucketOf P a)).val + rankOf P cd dd a)).val = old a := by
    have he := output_eq P cd dd arcs site layout h a
    rw [rowBase_val site layout]
    rw [show (p 4).val + (bucketIndex site (bucketOf P a)).val*(p 3).val + rankOf P cd dd a =
        (outAddress p initial (arcWord arcs a)).val by rw [he]; exact Nat.add_assoc ..]
    rw [hf.readback (arcs a).val (arcs a).isLt]
    exact h.widths a
  refine ⟨rs,hr,hc,hf,hl,hw,cost,?_,?_⟩
  · intro b i
    let x := (dd b).symm i
    have he := atArc x.1.1
    rw [bucketOf_thick P x.1, x.2, rank_thick P cd dd x] at he
    simpa only [x, Equiv.apply_symm_apply] using he
  · intro b i
    let x := (cd b).symm i
    have he := atArc x.1.1
    rw [bucketOf_motif P x.1, x.2, rank_motif P cd dd x] at he
    simpa only [x, Equiv.apply_symm_apply] using he

end CompressorRecords.BundleWidthScatter

end VPVNP
end Computability
end OAI
