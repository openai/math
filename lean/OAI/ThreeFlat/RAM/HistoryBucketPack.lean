import OAI.ThreeFlat.RAM.HistoryRowLoop
import OAI.ThreeFlat.Diagonal.HistoryBucketRows

namespace OAI
/-! # The compact native bucket pass writes canonical packed group intervals -/

namespace ThreeFlat.RAM.HistoryRowLoop.BucketRegisters

open Computability.VPVNP.BurstRAM Diagonal.HistoryContraction
open scoped Fin.CommRing

variable {w s d : ℕ}

private def writeAt (m : Memory w) (addr : ℕ) (value : ℕ) : Memory w := Function.update m addr (value : Word w)

private def put (m : Memory w) (dest counters : ℕ) (r : BucketRow (Fin d)) : Memory w :=
  let a := writeAt m (counters+r.group.val) (r.offset+(r.hi-r.lo))
  let b := writeAt a dest r.group.val
  let c := writeAt b (dest+1) r.lo
  let e := writeAt c (dest+2) r.hi
  writeAt e (dest+3) r.offset

private theorem put_frame (m : Memory w) (dest counters : ℕ) (r : BucketRow (Fin d)) {i : ℕ}
    (a : i ≠ counters+r.group.val) (b : i < dest ∨ dest+4 ≤ i) : put m dest counters r i = m i := by
  have b0 : i ≠ dest := by omega
  have b1 : i ≠ dest+1 := by omega
  have b2 : i ≠ dest+2 := by omega
  have b3 : i ≠ dest+3 := by omega
  simp [put,writeAt,Function.update,a,b0,b1,b2,b3]

private def image (m : Memory w) (counters dest : ℕ) : List (BucketRow (Fin d)) → Memory w
  | [] => m
  | r::rs => image (put m dest counters r) counters (dest+4) rs

/-- A snapshot of the 3-word source records. The destination is an independent
4-word row tape. The first input field addresses the word at `4*site`. -/
private def input (m : Memory w) (atRow : ℕ) : List (Bucket (Fin s)) → Prop
  | [] => True
  | b::bs => m atRow = (4*b.site.val : ℕ) ∧ m (atRow+1) = b.lo ∧ m (atRow+2) = b.hi ∧ input m (atRow+3) bs

private theorem input_frame (a stop : ℕ) (m m' : Memory w) (bs : List (Bucket (Fin s)))
    (range : a+3*bs.length ≤ stop) (eq : ∀ q, q<stop → m' q=m q) (old : input m a bs) : input m' a bs := by
  induction bs generalizing a with
  | nil => trivial
  | cons b bs ih =>
    simp only [List.length_cons,Nat.mul_succ] at range
    exact ⟨(eq _ (by omega)).trans old.1,(eq _ (by omega)).trans old.2.1,(eq _ (by omega)).trans old.2.2.1,
      ih _ (by omega) old.2.2.2⟩

private theorem store_at (m : Memory w) {addr value : ℕ} (fit : addr<2^w) :
    writeMemory m (addr : Word w) (value : Word w) = writeAt m addr value := by
  funext i
  by_cases hi : i=addr
  · subst i
    simp [writeMemory,writeAt,Fin.val_cast_of_lt fit]
  · simp [writeMemory,writeAt,Fin.val_cast_of_lt fit,hi]

private theorem word_succ (a : ℕ) : (a : Word w)+1=((a+1 : ℕ) : Word w) := by
  simp only [Nat.cast_add,Nat.cast_one]

private theorem one (m : Memory w) (src groups counters dest : ℕ) (group : Fin s → Fin d)
    (acc : Fin d → ℕ) (b : Bucket (Fin s)) (room : dest+4 ≤ 2^w)
    (src_room : src+3 ≤ 2^w) (group_room : groups+4*s ≤ 2^w) (counter_room : counters+d ≤ 2^w)
    (order : b.lo ≤ b.hi) (ready : input m src [b])
    (readG : ∀ i : Fin s, m (groups+4*i.val) = (group i).val)
    (readA : ∀ i : Fin d, m (counters+i.val) = acc i) :
    HistoryBucketEmitter.afterRow m src groups counters dest = put m dest counters (BucketRows.row group acc b) := by
  have iLt := b.site.isLt
  have gLt := (group b.site).isLt
  have gRead : m ((groups : Word w)+m (src : Word w).val).val=((group b.site).val : Word w) := by
    rw [Fin.val_cast_of_lt (show src<2^w by omega),ready.1,←Nat.cast_add,
      Fin.val_cast_of_lt (show groups+4*b.site.val<2^w by omega),readG]
  have cRead : m (((counters+(group b.site).val : ℕ) : Word w)).val=(acc (group b.site) : Word w) := by
    rw [Fin.val_cast_of_lt (show counters+(group b.site).val<2^w by omega),readA]
  have uRead : m (((src+1 : ℕ) : Word w)).val=(b.lo : Word w) := by
    rw [Fin.val_cast_of_lt (show src+1<2^w by omega)]
    exact ready.2.1
  have vRead : m (((src+2 : ℕ) : Word w)).val=(b.hi : Word w) := by
    rw [Fin.val_cast_of_lt (show src+2<2^w by omega)]
    exact ready.2.2.1
  simp only [HistoryBucketEmitter.afterRow,gRead,word_succ,uRead,vRead,
    ←Nat.cast_add,cRead,←Nat.cast_sub order]
  rw [store_at _ (addr:=counters+(group b.site).val) (by omega),
    store_at _ (addr:=dest) (by omega),store_at _ (addr:=dest+1) (by omega),
    store_at _ (addr:=dest+2) (by omega),store_at _ (addr:=dest+3) (by omega)]
  rfl

private theorem input_window (src : ℕ) (m m' : Memory w) (bs : List (Bucket (Fin s)))
    (eq : ∀ q, src≤q → q<src+3*bs.length → m' q=m q) (ready : input m src bs) : input m' src bs := by
  induction bs generalizing src with
  | nil => trivial
  | cons b bs ih =>
    simp only [List.length_cons,Nat.mul_succ] at eq
    exact ⟨(eq _ (by omega) (by omega)).trans ready.1,(eq _ (by omega) (by omega)).trans ready.2.1,
      (eq _ (by omega) (by omega)).trans ready.2.2.1,ih (src+3) (fun q h k => eq q (by omega) (by omega)) ready.2.2.2⟩


private theorem update_counts (m : Memory w) (dest counters : ℕ) (group : Fin s → Fin d)
    (acc : Fin d → ℕ) (b : Bucket (Fin s)) (apart : counters+d≤dest ∨ dest+4≤counters)
    (readA : ∀ i : Fin d,m (counters+i.val)=(acc i : Word w)) (i : Fin d) :
    put m dest counters (BucketRows.row group acc b) (counters+i.val)=(BucketRows.bump group acc b i : Word w) := by
  let row := BucketRows.row group acc b
  let m' := put m dest counters row
  change m' (counters+i.val)=_
  have hi := i.isLt
  by_cases same : i=group b.site
  · subst i
    have g := (group b.site).isLt
    have miss (j : ℕ) (hj : j<4) : counters+(group b.site).val ≠ dest+j := by omega
    have miss0 : counters+(group b.site).val ≠ dest := by omega
    simp [m',put,row,BucketRows.row,writeAt,BucketRows.bump,Bucket.size,Function.update,miss0,miss 1 (by decide),miss 2 (by decide),miss 3 (by decide)]
  · have different : counters+i.val ≠ counters+row.group.val := by
      intro eq; apply same; apply Fin.ext; simpa [row,BucketRows.row] using eq
    rw [show m' (counters+i.val) = m (counters+i.val) from put_frame _ _ _ _ different (by omega),readA]
    simp [BucketRows.bump,Function.update,same]

/-- Repeated copying gives the same packed rows as `BucketRows.pack`. The
size constraints only separate actual memory regions and prevent wraparound. -/
theorem packed_walk_separated (m : Memory w) (src groups counters dest : ℕ) (stop : Word w) (group : Fin s → Fin d)
    (acc : Fin d → ℕ) (bs : List (Bucket (Fin s))) (room : dest + 4*bs.length < 2^w)
    (src_room : src+3*bs.length < 2^w) (group_room : groups+4*s ≤ 2^w) (counter_room : counters+d ≤ 2^w)
    (sC : src+3*bs.length≤counters ∨ counters+d≤ src) (sD : src+3*bs.length≤dest ∨ dest+4*bs.length≤ src)
    (gC : groups+4*s≤counters ∨ counters+d≤groups) (gD : groups+4*s≤dest ∨ dest+4*bs.length≤groups)
    (cD : counters+d≤dest ∨ dest+4*bs.length≤counters)
    (order : ∀ b ∈ bs, b.lo ≤ b.hi) (ready : input m src bs)
    (readG : ∀ i : Fin s, m (groups+4*i.val) = (group i).val)
    (readA : ∀ i : Fin d, m (counters+i.val) = acc i) :
    walk next update bs.length ⟨src,groups,counters,dest,stop⟩ m = image m counters dest (BucketRows.pack group acc bs) := by
  induction bs generalizing m src dest acc with
  | nil => rfl
  | cons b bs ih =>
    simp only [List.length_cons,Nat.mul_succ] at room src_room sC sD gD cD
    let row := BucketRows.row group acc b
    let m' := put m dest counters row
    have changeRow : update ⟨src,groups,counters,dest,stop⟩ m=m' := one m src groups counters dest group acc b (by omega)
      (by omega) group_room counter_room (order b (by simp)) ⟨ready.1,ready.2.1,ready.2.2.1,trivial⟩ readG readA
    have countBound := row.group.isLt
    have todo := input_window (src+3) m m' bs (fun q lo hi => put_frame _ _ _ _ (by omega) (by omega)) ready.2.2.2
    have readG' (i : Fin s) : m' (groups+4*i.val) = (group i).val :=
      (put_frame m dest counters row (by have := i.isLt; omega) (by have := i.isLt; omega)).trans (readG i)
    have readA' (i : Fin d) : m' (counters+i.val) = BucketRows.bump group acc b i :=
      update_counts m dest counters group acc b (by omega) readA i
    simp only [List.length_cons,walk,BucketRows.pack,image,changeRow]
    simp only [next,word_succ]
    apply ih m' (src+3) (dest+4) (BucketRows.bump group acc b)
    all_goals first | exact todo | exact readG' | exact readA' | exact fun x hx => order x (by simp [hx]) | omega


/-- Repeated copying gives the same packed rows as `BucketRows.pack`. The
size constraints only separate actual memory regions and prevent wraparound. -/
theorem packed_walk (m : Memory w) (src groups counters dest : ℕ) (stop : Word w) (group : Fin s → Fin d)
    (acc : Fin d → ℕ) (bs : List (Bucket (Fin s))) (room : dest + 4*bs.length < 2^w)
    (src_end : src+3*bs.length ≤ counters) (groups_end : groups+4*s ≤ counters) (counters_end : counters+d ≤ dest)
    (order : ∀ b ∈ bs, b.lo ≤ b.hi) (ready : input m src bs)
    (readG : ∀ i : Fin s, m (groups+4*i.val) = (group i).val)
    (readA : ∀ i : Fin d, m (counters+i.val) = acc i) :
    walk next update bs.length ⟨src,groups,counters,dest,stop⟩ m = image m counters dest (BucketRows.pack group acc bs) := by
  exact packed_walk_separated m src groups counters dest stop group acc bs room (by omega) (by omega) (by omega)
    (Or.inl src_end) (Or.inl (by omega)) (Or.inl groups_end) (Or.inl (by omega)) (Or.inl counters_end) order ready readG readA

/-- The public three-column input interface for a finite row family. -/
theorem input_ofFn {n : ℕ} (m : Memory w) (src : ℕ) (b : Fin n → Bucket (Fin s))
    (atRow : ∀ i, m (src+3*i.val) = ((4*(b i).site.val : ℕ) : Word w) ∧
      m (src+3*i.val+1) = ((b i).lo : Word w) ∧ m (src+3*i.val+2) = ((b i).hi : Word w)) :
    input m src (List.ofFn b) := by
  induction n generalizing src with
  | zero => simp [input]
  | succ n ih =>
    rw [List.ofFn_succ]
    have head := atRow 0
    simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at head
    refine ⟨head.1, head.2.1, head.2.2, ih (src+3) (fun i => b i.succ) ?_⟩
    intro i
    have addr : src+3+3*i.val=src+3*i.succ.val := by simp only [Fin.val_succ]; omega
    rw [addr]
    exact atRow i.succ

/-- The order of the four stored words is group, interval start, interval end,
and number of earlier bits assigned to the same group. -/
def rowColumn (row : BucketRow (Fin d)) : Fin 4 → ℕ :=
  ![row.group.val,row.lo,row.hi,row.offset]

private theorem put_row (m : Memory w) (dest counters : ℕ) (row : BucketRow (Fin d)) (j : Fin 4) :
    put m dest counters row (dest+j.val) = (rowColumn row j : Word w) := by
  fin_cases j <;> simp [put,writeAt,Function.update,rowColumn]

private theorem image_frame (m : Memory w) (counters dest : ℕ) (rs : List (BucketRow (Fin d)))
    (a : ℕ) (outC : a<counters ∨ counters+d≤a) (outD : a<dest ∨ dest+4*rs.length≤a) :
    image m counters dest rs a = m a := by
  induction rs generalizing m dest with
  | nil => rfl
  | cons row rs ih =>
    simp only [List.length_cons] at outD
    rw [image,ih _ (dest+4) (by omega)]
    exact put_frame m dest counters row (by have := row.group.isLt; omega) (by omega)

private theorem image_rows {n : ℕ} (m : Memory w) (counters dest : ℕ) (rs : Fin n → BucketRow (Fin d))
    (sep : counters+d≤dest ∨ dest+4*n≤counters) (i : Fin n) (j : Fin 4) :
    image m counters dest (List.ofFn rs) (dest+4*i.val+j.val)=(rowColumn (rs i) j : Word w) := by
  induction n generalizing m dest with
  | zero => exact i.elim0
  | succ n ih =>
    rw [List.ofFn_succ,image]
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero]
      rw [image_frame _ counters (dest+4) _ _ (by have := j.isLt; omega) (Or.inl (by have := j.isLt; omega))]
      exact put_row m dest counters _ j
    · have atNext : dest+4*i.succ.val+j.val=(dest+4)+4*i.val+j.val := by simp only [Fin.val_succ]; omega
      rw [atNext]
      exact ih _ (dest+4) (fun i => rs i.succ) (by omega) i

/-- Readback and write footprint for the concrete native scan. Any consumer
may identify the computed bucket rows by a theorem about `BucketRows.pack`. -/
private theorem final_counts (group : Fin s → Fin d) (bs : List (Bucket (Fin s)))
    (acc : Fin d→ℕ) (m : Memory w) (src dest : ℕ) (apart : src+d≤dest ∨ dest+4*bs.length≤ src)
    (counts : ∀ i : Fin d,m (src+i.val)=(acc i:Word w)) (g : Fin d) :
    image m src dest (BucketRows.pack group acc bs) (src+g.val)=
      ((bs.foldl (BucketRows.bump group) acc g:ℕ):Word w) := by
  induction bs generalizing m dest acc with
  | nil => exact counts g
  | cons b bs ih =>
    simp only [BucketRows.pack,image,List.foldl_cons]
    have bound := apart
    simp only [List.length_cons,Nat.mul_succ] at bound
    apply ih <;> first | omega | exact update_counts m dest src group acc b (by omega) counts

theorem walk_counts_separated {n : ℕ} (m : Memory w) (src groups counters dest : ℕ) (stop : Word w)
    (group : Fin s → Fin d) (acc : Fin d → ℕ) (b : Fin n → Bucket (Fin s))
    (room : dest+4*n<2^w) (sfit : src+3*n<2^w) (gfit : groups+4*s≤2^w) (cfit : counters+d≤2^w)
    (sC : src+3*n≤counters ∨ counters+d≤ src) (sD : src+3*n≤dest ∨ dest+4*n≤ src)
    (gC : groups+4*s≤counters ∨ counters+d≤groups) (gD : groups+4*s≤dest ∨ dest+4*n≤groups)
    (cD : counters+d≤dest ∨ dest+4*n≤counters) (order : ∀ i, (b i).lo≤(b i).hi)
    (atRow : ∀ i, m (src+3*i.val) = ((4*(b i).site.val : ℕ) : Word w) ∧
      m (src+3*i.val+1) = ((b i).lo : Word w) ∧ m (src+3*i.val+2) = ((b i).hi : Word w))
    (readG : ∀ i : Fin s,m (groups+4*i.val)=(group i).val)
    (readA : ∀ i : Fin d,m (counters+i.val)=acc i) (g : Fin d) :
    walk next update n (⟨src,groups,counters,dest,stop⟩ : BucketRegisters w) m (counters+g.val)=
      ((acc g+BucketRows.count group (List.ofFn b) g:ℕ):Word w) := by
  let bs := List.ofFn b
  have len : bs.length=n := List.length_ofFn
  have ord (x) (hx : x ∈ bs) : x.lo≤x.hi := by
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact order i
  have actual := packed_walk_separated m src groups counters dest stop group acc bs
    (by rwa [len]) (by rwa [len]) gfit cfit (by rwa [len]) (by rwa [len]) gC (by rwa [len]) (by rwa [len])
    ord (input_ofFn m src b atRow) readG readA
  rw [len] at actual
  rw [actual,final_counts group bs acc m counters dest (by rwa [len]) readA g,BucketRows.fold_count]

theorem walk_rows_separated {n : ℕ} (m : Memory w) (src groups counters dest : ℕ) (stop : Word w)
    (group : Fin s → Fin d) (acc : Fin d → ℕ) (b : Fin n → Bucket (Fin s)) (rows : Fin n → BucketRow (Fin d))
    (packed : BucketRows.pack group acc (List.ofFn b)=List.ofFn rows)
    (room : dest+4*n<2^w) (sfit : src+3*n<2^w)
    (gfit : groups+4*s≤2^w) (cfit : counters+d≤2^w)
    (sC : src+3*n≤counters ∨ counters+d≤ src) (sD : src+3*n≤dest ∨ dest+4*n≤ src)
    (gC : groups+4*s≤counters ∨ counters+d≤groups) (gD : groups+4*s≤dest ∨ dest+4*n≤groups)
    (cD : counters+d≤dest ∨ dest+4*n≤counters) (order : ∀ i, (b i).lo≤(b i).hi)
    (atRow : ∀ i, m (src+3*i.val) = ((4*(b i).site.val : ℕ) : Word w) ∧
      m (src+3*i.val+1) = ((b i).lo : Word w) ∧ m (src+3*i.val+2) = ((b i).hi : Word w))
    (readG : ∀ i : Fin s, m (groups+4*i.val) = (group i).val)
    (readA : ∀ i : Fin d, m (counters+i.val) = acc i) :
    let output := walk next update n (⟨src,groups,counters,dest,stop⟩ : BucketRegisters w) m
    (∀ i : Fin n, ∀ j : Fin 4, output (dest+4*i.val+j.val)=(rowColumn (rows i) j : Word w)) ∧
    ∀ a, (a<counters ∨ counters+d≤a) → (a<dest ∨ dest+4*n≤a) → output a=m a := by
  dsimp only
  have ord : ∀ x ∈ List.ofFn b, x.lo≤x.hi := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact order i
  have eq := packed_walk_separated m src groups counters dest stop group acc (List.ofFn b)
    (by simpa using room) (by simpa using sfit) gfit cfit (by simpa using sC) (by simpa using sD)
    gC (by simpa using gD) (by simpa using cD) ord
    (input_ofFn m src b atRow) readG readA
  rw [List.length_ofFn,packed] at eq
  rw [eq]
  exact ⟨image_rows m counters dest rows cD,
    fun a hc hd => image_frame m counters dest (List.ofFn rows) a hc (by simpa using hd)⟩

/-- Readback and write footprint for the concrete native scan. Any consumer
may identify the computed bucket rows by a theorem about `BucketRows.pack`. -/
theorem walk_rows {n : ℕ} (m : Memory w) (src groups counters dest : ℕ) (stop : Word w)
    (group : Fin s → Fin d) (acc : Fin d → ℕ) (b : Fin n → Bucket (Fin s)) (rows : Fin n → BucketRow (Fin d))
    (packed : BucketRows.pack group acc (List.ofFn b)=List.ofFn rows)
    (room : dest+4*n<2^w) (src_end : src+3*n≤counters) (groups_end : groups+4*s≤counters)
    (counters_end : counters+d≤dest) (order : ∀ i, (b i).lo≤(b i).hi)
    (atRow : ∀ i, m (src+3*i.val) = ((4*(b i).site.val : ℕ) : Word w) ∧
      m (src+3*i.val+1) = ((b i).lo : Word w) ∧ m (src+3*i.val+2) = ((b i).hi : Word w))
    (readG : ∀ i : Fin s, m (groups+4*i.val) = (group i).val)
    (readA : ∀ i : Fin d, m (counters+i.val) = acc i) :
    let output := walk next update n (⟨src,groups,counters,dest,stop⟩ : BucketRegisters w) m
    (∀ i : Fin n, ∀ j : Fin 4, output (dest+4*i.val+j.val)=(rowColumn (rows i) j : Word w)) ∧
    ∀ a, (a<counters ∨ counters+d≤a) → (a<dest ∨ dest+4*n≤a) → output a=m a := by
  exact walk_rows_separated m src groups counters dest stop group acc b rows packed room
    (by omega) (by omega) (by omega) (Or.inl src_end) (Or.inl (by omega)) (Or.inl groups_end)
    (Or.inl (by omega)) (Or.inl counters_end) order atRow readG readA

end ThreeFlat.RAM.HistoryRowLoop.BucketRegisters

end OAI
