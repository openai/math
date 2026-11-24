import OAI.Computability.VPVNP.CompressorRecordsShrinkRAM
import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMBuckets

/-!
# Native scan of the shrinking placement rows

The four input columns are looked up in the original greedy and incidence
directories. Their addresses can vary with the decoded base and arc. Every
visited old position receives four private-to-that-position output cells.
The only restriction on input placement is disjointness from the output
cells, so the scan can use directories produced by earlier passes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- The physical address read from each of the color, offset, mate and
displacement columns when visiting row `i`. -/
def readAddr (p : Fin 14 → Word w) (c : Fin 4) (i : Word w) : ℕ :=
  let f := decode p i
  ![(p 6+f.base).val, (p 7+f.base).val, (p 8+baseArc p f).val, (p 9+baseArc p f).val] c

/-- The four output columns start at public words 10 through 13. -/
def outAddr (p : Fin 14 → Word w) (t : Fin 4) (i : Word w) : ℕ :=
  (p (t.natAdd 10) + i).val

/-- Numerical order of output columns, in the order in which they are written. -/
def Outputs.field {α : Type} (out : Outputs α) (t : Fin 4) : α :=
  ![out.owner, out.thick, out.assigned, out.target] t

/-- The scan needs distinct output cells and persistent access to the old
columns. Different input lookups may freely share an address. -/
structure Regions (p : Fin 14 → Word w) (N : ℕ) : Prop where
  fits : N ≤ 2 ^ w
  unique : ∀ (t u : Fin 4) (i j : Word w), i.val < N → j.val < N →
    (outAddr p t i = outAddr p u j ↔ t = u ∧ i = j)
  inputs : ∀ (c t : Fin 4) (i j : Word w), i.val < N → j.val < N →
    readAddr p c i ≠ outAddr p t j

/-- Four consecutive output regions of capacity `N`. The old directory may
be anywhere outside the reserved output interval, on either side of it. -/
theorem Regions.packed (p : Fin 14 → Word w) {base N : ℕ}
    (fit : base + 4*N ≤ 2 ^ w) (cols : ∀ t : Fin 4, (p (t.natAdd 10)).val = base+t.val*N)
    (old : ∀ (c : Fin 4) (i : Word w), i.val < N →
      readAddr p c i < base ∨ base+4*N ≤ readAddr p c i) : Regions p N := by
  have within (t : Fin 4) (i : Word w) (hi : i.val < N) : t.val*N + i.val < 4*N := by
    have h := Nat.mul_le_mul_right N t.isLt
    rw [Nat.succ_mul] at h
    omega
  have addr (t : Fin 4) (i : Word w) (hi : i.val < N) :
      outAddr p t i = base + (t.val*N+i.val) := by
    have h := within t i hi
    rw [outAddr, Fin.val_add, cols, Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨by omega, ?_, ?_⟩
  · intro t u i j hi hj
    rw [addr t i hi, addr u j hj, Nat.add_left_cancel_iff]
    constructor
    · intro h
      have he : i = j := Fin.ext ((Nat.mul_add_mod_of_lt hi (a := t.val)).symm.trans
        ((congrArg (· % N) h).trans (Nat.mul_add_mod_of_lt hj)))
      subst j
      exact ⟨Fin.ext (Nat.eq_of_mul_eq_mul_right (by omega) (Nat.add_right_cancel h)), rfl⟩
    · rintro ⟨rfl, rfl⟩
      rfl
  · intro c t i j hi hj
    have hold := old c i hi
    have ht := within t j hj
    rw [addr t j hj]
    omega

private theorem div_le (x y : Word w) : (div x y).val ≤ x.val / y.val := Nat.mod_le _ _

private theorem mod_le (x y : Word w) : (mod x y).val ≤ x.val % y.val := Nat.mod_le _ _

private theorem read_offsets_le (p : Fin 14 → Word w) (i : Word w) :
    (decode p i).base.val ≤ i.val ∧ (baseArc p (decode p i)).val ≤ i.val := by
  let v := div i (p 1 * p 0)
  let q := div v (p 2)
  let f := decode p i
  have hv : v.val ≤ i.val := (div_le ..).trans (Nat.div_le_self ..)
  have hb : f.base.val ≤ q.val := (div_le ..).trans (Nat.div_le_self ..)
  have hq : q.val ≤ v.val / (p 2).val := div_le ..
  refine ⟨hb.trans (hq.trans ((Nat.div_le_self ..).trans hv)), ?_⟩
  calc
    (baseArc p f).val ≤ f.base.val * (p 2).val + f.slot.val := by
      rw [baseArc, Fin.val_add, Fin.val_mul]
      exact (Nat.mod_le ..).trans (Nat.add_le_add_right (Nat.mod_le ..) _)
    _ ≤ (v.val / (p 2).val) * (p 2).val + v.val % (p 2).val :=
      Nat.add_le_add (Nat.mul_le_mul_right _ (hb.trans hq)) (mod_le ..)
    _ = v.val := Nat.div_add_mod' ..
    _ ≤ i.val := hv

/-- Old directory columns may have any starts below the four new arrays.
Even without a positive radix assumption, each decoded input index is at
most the visiting row index. -/
theorem Regions.packedAfterInputs (p : Fin 14 → Word w) {base N : ℕ}
    (fit : base + 4*N ≤ 2 ^ w) (cols : ∀ t : Fin 4, (p (t.natAdd 10)).val = base+t.val*N)
    (old : ∀ c : Fin 4, (p ⟨6+c.val, by have := c.isLt; omega⟩).val + N ≤ base) : Regions p N := by
  apply Regions.packed p fit cols
  intro c i hi
  left
  obtain ⟨hb, ha⟩ := read_offsets_le p i
  have addr (j : Fin 14) (hj : (p j).val+N ≤ base) (off : Word w) (ho : off.val ≤ i.val) :
      (p j+off).val < base :=
    (Nat.mod_le ..).trans_lt (show (p j).val+off.val < base by omega)
  fin_cases c
  · exact addr _ (old 0) _ hb
  · exact addr _ (old 1) _ hb
  · exact addr _ (old 2) _ ha
  · exact addr _ (old 3) _ ha

/-- Eight consecutive arrays of equal capacity, with the four input columns
first and the four newly written columns last. -/
theorem Regions.packedEight (p : Fin 14 → Word w) {start N : ℕ}
    (fit : start + 8*N ≤ 2^w)
    (cols : ∀ t : Fin 8, (p (t.natAdd 6)).val = start+t.val*N) : Regions p N := by
  apply Regions.packedAfterInputs p (base := start+4*N) (by omega)
  · intro t
    have ht := cols (t.natAdd 4)
    have he : (t.natAdd 4).natAdd 6 = t.natAdd 10 := Fin.ext (by change 6+(4+t.val) = 10+t.val; omega)
    rw [he] at ht
    change (p (t.natAdd 10)).val = start+(4+t.val)*N at ht
    rw [Nat.add_mul] at ht
    omega
  · intro c
    have hc := cols (c.castAdd 4)
    change (p ⟨6+c.val, _⟩).val = start+c.val*N at hc
    have h := Nat.mul_le_mul_right N c.isLt
    rw [Nat.succ_mul] at h
    omega

private theorem store_other (p : Fin 14 → Word w) (m : Memory w) (i : Word w)
    (out : Outputs (Word w)) (addr : ℕ) (h : ∀ t : Fin 4, addr ≠ outAddr p t i) :
    store p m i out addr = m addr := by
  have h₀ : addr ≠ (p 10 + i).val := h 0
  have h₁ : addr ≠ (p 11 + i).val := h 1
  have h₂ : addr ≠ (p 12 + i).val := h 2
  have h₃ : addr ≠ (p 13 + i).val := h 3
  simp only [store, writeMemory, ite_eq_right h₀, ite_eq_right h₁, ite_eq_right h₂, ite_eq_right h₃]

private theorem store_field {p : Fin 14 → Word w} {N : ℕ} (reg : Regions p N)
    (m : Memory w) (i : Word w) (hi : i.val < N) (out : Outputs (Word w)) (t : Fin 4) :
    store p m i out (outAddr p t i) = out.field t := by
  have eqv (u : Fin 4) : (outAddr p t i = outAddr p u i) ↔ t = u := by
    simp only [reg.unique t u i i hi hi, and_true]
  change (if outAddr p t i = outAddr p 3 i then out.target
    else if outAddr p t i = outAddr p 2 i then out.assigned
    else if outAddr p t i = outAddr p 1 i then out.thick
    else if outAddr p t i = outAddr p 0 i then out.owner else m (outAddr p t i)) = out.field t
  simp only [eqv]
  fin_cases t <;> rfl

private theorem events_same {p : Fin 14 → Word w} {m snapshot : Memory w} (i : Word w)
    (agree : ∀ c : Fin 4, m (readAddr p c i) = snapshot (readAddr p c i)) :
    events p m i = events p snapshot i := by
  let f := decode p i
  have hcols : readColumns p m f = readColumns p snapshot f :=
    Prod.ext (agree 0) (Prod.ext (agree 1) (Prod.ext (agree 2) (agree 3)))
  dsimp only [f] at hcols
  simp only [events, outputs, hcols]

/-- The report sequence in increasing old-position order. Every lookup is
expressed directly in the initial external memory. -/
def scanReports (p : Fin 14 → Word w) (snapshot : Memory w) (k : ℕ) : ℕ → List (Report w)
  | 0 => []
  | n+1 => ⟨events p snapshot (Fin.ofNat _ k), some (Fin.ofNat _ (k+1))⟩ ::
      scanReports p snapshot (k+1) n

private theorem after_snapshot (p : Fin 14 → Word w) (snapshot m : Memory w) (i : Word w) :
    after m (events p snapshot i) = store p m i (outputs p snapshot i) := rfl

private theorem after_succ (p : Fin 14 → Word w) (snapshot m : Memory w) (k n : ℕ) :
    after m (eventLog (scanReports p snapshot k (n+1))) =
      after (store p m (Fin.ofNat _ k) (outputs p snapshot (Fin.ofNat _ k)))
        (eventLog (scanReports p snapshot (k+1) n)) := by
  simp only [scanReports, eventLog, List.flatMap_cons, after, List.foldl_append]
  rfl

private theorem scan_native_aux {p : Fin 14 → Word w} {N : ℕ} (reg : Regions p N)
    (snapshot : Memory w) (k n : ℕ) (m : Memory w) (bound : k+n ≤ N)
    (agree : ∀ c i, i.val < N → m (readAddr p c i) = snapshot (readAddr p c i)) :
    let M := (template visit 0).instantiate w p
    runSegment M.program 65 (some (Fin.ofNat _ k)) m (List.replicate n []) =
      some (scanReports p snapshot k n) := by
  induction n generalizing k m with
  | zero => rfl
  | succ n ih =>
    let i := Fin.ofNat (2^w) k
    have hv : i.val = k := Nat.mod_eq_of_lt (by have := reg.fits; omega)
    have hi : i.val < N := by omega
    have hn : i+1 = Fin.ofNat (2^w) (k+1) := by
      apply Fin.ext
      simp [i, Fin.val_add, Nat.mod_add_mod, Nat.add_mod_mod]
    have he := events_same i (fun c ↦ agree c i hi)
    have hnext := ih (k+1) (store p m i (outputs p snapshot i)) (by omega)
      (fun c j hj ↦ (store_other _ _ _ _ _ (fun t ↦ reg.inputs c t j i hj hi)).trans (agree c j hj))
    dsimp only
    rw [List.replicate_succ, runSegment, visit_native p m i, he, hn]
    simp only [after_snapshot, hnext, Option.map_some, scanReports, i]

/-- The complete native segment, with no change to the four input columns. -/
theorem scan_native (p : Fin 14 → Word w) (N k n : ℕ) (m : Memory w) (reg : Regions p N)
    (bound : k+n ≤ N) :
    let M := (template visit 0).instantiate w p
    runSegment M.program 65 (some (Fin.ofNat _ k)) m (List.replicate n []) =
      some (scanReports p m k n) :=
  scan_native_aux reg m k n m bound (fun _ _ _ ↦ rfl)

private theorem scan_preserve {p : Fin 14 → Word w} {N : ℕ} (reg : Regions p N)
    (snapshot m : Memory w) (k n addr : ℕ) (bound : k+n ≤ N)
    (outside : ∀ (t : Fin 4) (i : Word w), k ≤ i.val → i.val < k+n → addr ≠ outAddr p t i) :
    after m (eventLog (scanReports p snapshot k n)) addr = m addr := by
  induction n generalizing k m with
  | zero => rfl
  | succ n ih =>
    let i := Fin.ofNat (2^w) k
    have hv : i.val = k := Nat.mod_eq_of_lt (by have := reg.fits; omega)
    rw [after_succ, ih _ (k+1) (by omega) (fun t j hj hlt ↦ outside t j (by omega) (by omega))]
    exact store_other _ _ _ _ _ (fun t ↦ outside t i (by omega) (by omega))

private theorem scan_field {p : Fin 14 → Word w} {N : ℕ} (reg : Regions p N)
    (snapshot m : Memory w) (k n : ℕ) (bound : k+n ≤ N)
    (t : Fin 4) (i : Word w) (hi : k ≤ i.val) (hi' : i.val < k+n) :
    after m (eventLog (scanReports p snapshot k n)) (outAddr p t i) = (outputs p snapshot i).field t := by
  induction n generalizing k m with
  | zero => omega
  | succ n ih =>
    rw [after_succ]
    rcases eq_or_lt_of_le hi with he | he
    · have hv : Fin.ofNat (2^w) k = i := Fin.ext (by simp [he])
      rw [hv]
      rw [scan_preserve reg snapshot _ _ _ _ (by omega)]
      · exact store_field reg _ i (by omega) _ t
      · intro u j hj hlt h
        have hij := ((reg.unique t u i j (by omega) (by omega)).mp h).2
        subst j
        omega
    · exact ih _ _ (by omega) (by omega) (by omega)

/-- The returned registers, external work and complete memory contents of a
shrinking scan, including the untouched portion of each output column. -/
structure ScanResult (p : Fin 14 → Word w) (N k n : ℕ) (m : Memory w) (rs : List (Report w)) : Prop where
  endCursor : endState (some (Fin.ofNat _ k)) rs = some (Fin.ofNat _ (k+n))
  calls : rs.length = n
  work : ∀ r ∈ rs, r.events.length = 64 ∧ countProbes r.events = 8
  cost : RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) rs = 9*n
  readback : ∀ (t : Fin 4) (i : Word w), k ≤ i.val → i.val < k+n →
    after m (eventLog rs) (outAddr p t i) = (outputs p m i).field t
  preserve : ∀ addr, (∀ (t : Fin 4) (i : Word w), k ≤ i.val → i.val < k+n → addr ≠ outAddr p t i) →
    after m (eventLog rs) addr = m addr
  inputs : ∀ (c : Fin 4) (i : Word w), i.val < N →
    after m (eventLog rs) (readAddr p c i) = m (readAddr p c i)

private theorem scan_accounting (p : Fin 14 → Word w) (m : Memory w) (k n : ℕ) :
    let rs := scanReports p m k n
    endState (some (Fin.ofNat _ k)) rs = some (Fin.ofNat _ (k+n)) ∧ rs.length = n ∧
      (∀ r ∈ rs, r.events.length = 64 ∧ countProbes r.events = 8) ∧
      RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) rs = 9*n := by
  induction n generalizing k with
  | zero => exact ⟨rfl, rfl, by simp [scanReports], rfl⟩
  | succ n ih =>
    obtain ⟨hend,hlen,hwork,hcost⟩ := ih (k+1)
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [scanReports, endState, hend]
      congr 2
      omega
    · simp only [scanReports, List.length_cons, hlen]
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | h
      · exact visit_work p m _
      · exact hwork r h
    · rw [scanReports, RAMBuckets.cost, (visit_work p m _).2, hcost, Nat.mul_succ]
      omega

/-- Execute the whole interval from its initial memory. Every one of the
four output columns agrees with the graph placement computed from the four
original input values. -/
theorem scan_run (p : Fin 14 → Word w) (N k n : ℕ) (m : Memory w) (regions : Regions p N)
    (bound : k+n ≤ N) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program 65 (some (Fin.ofNat _ k)) m (List.replicate n []) = some rs ∧
      ScanResult p N k n m rs := by
  obtain ⟨he,hl,hw,hc⟩ := scan_accounting p m k n
  refine ⟨scanReports p m k n, scan_native p N k n m regions bound, he, hl, hw, hc,
    scan_field regions m m k n bound, fun addr ↦ scan_preserve regions m m k n addr bound, ?_⟩
  intro c i hi
  apply scan_preserve regions m m k n _ bound
  exact fun t j _ hlt ↦ regions.inputs c t i j hi (hlt.trans_le bound)

end CompressorRecords.ShrinkRAM

end VPVNP
end Computability
end OAI
