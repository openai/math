import OAI.Computability.VPVNP.CompressorRecordsBundleRAM
import OAI.Computability.VPVNP.RAMChain
import OAI.Computability.VPVNP.RAMBuckets

/-!
# Native scan classifying each old outgoing port

The old port's mate selects two of the six input addresses. During the scan
these addresses and their contents agree with their values in the initial
memory. Each old port receives a bucket and a sorting key in separate output
columns. A complete scan costs nine units per old port, including the call.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleRAM

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM

variable {w : ℕ}

/-- The bucket and the sorting key, respectively, in the original port order. -/
def outAddr (p : Fin 11 → Word w) (t : Fin 2) (i : Word w) : ℕ :=
  (p (t.natAdd 9) + i).val

/-- Select the bucket word or the sort-key word produced by classifying an old outgoing port. -/
def field (p : Fin 11 → Word w) (m : Memory w) (i : Word w) : Fin 2 → Word w :=
  ![bucket p m i, key p m i]

/-- The six initial input addresses can overlap freely. Every output cell
has a unique port and column, disjoint from those input addresses. -/
structure Regions (p : Fin 11 → Word w) (snapshot : Memory w) (N : ℕ) : Prop where
  fits : N ≤ 2 ^ w
  unique : ∀ (t u : Fin 2) (i j : Word w), i.val < N → j.val < N →
    (outAddr p t i = outAddr p u j ↔ t = u ∧ i = j)
  inputs : ∀ (c : Fin 6) (t : Fin 2) (i j : Word w), i.val < N → j.val < N →
    (readAddress p snapshot i c).val ≠ outAddr p t j

/-- Two consecutive output regions of capacity `N`. Old columns on either
side of the interval can be shared with other passes. -/
theorem Regions.packed (p : Fin 11 → Word w) (snapshot : Memory w) {base N : ℕ}
    (fit : base + 2*N ≤ 2 ^ w) (cols : ∀ t : Fin 2, (p (t.natAdd 9)).val = base+t.val*N)
    (old : ∀ (c : Fin 6) (i : Word w), i.val < N →
      (readAddress p snapshot i c).val < base ∨ base+2*N ≤ (readAddress p snapshot i c).val) :
    Regions p snapshot N := by
  have within (t : Fin 2) (i : Word w) (hi : i.val < N) : t.val*N + i.val < 2*N := by
    have h := Nat.mul_le_mul_right N t.isLt
    rw [Nat.succ_mul] at h
    omega
  have addr (t : Fin 2) (i : Word w) (hi : i.val < N) :
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

private def store (p : Fin 11 → Word w) (snapshot m : Memory w) (i : Word w) : Memory w :=
  writeMemory (writeMemory m (p 9+i) (bucket p snapshot i)) (p 10+i) (key p snapshot i)

private theorem store_other (p : Fin 11 → Word w) (snapshot m : Memory w) (i : Word w)
    (addr : ℕ) (h : ∀ t : Fin 2, addr ≠ outAddr p t i) :
    store p snapshot m i addr = m addr := by
  have h₀ : addr ≠ (p 9+i).val := h 0
  have h₁ : addr ≠ (p 10+i).val := h 1
  simp [store, writeMemory, h₀, h₁]

private theorem store_field {p : Fin 11 → Word w} {snapshot : Memory w} {N : ℕ}
    (reg : Regions p snapshot N) (m : Memory w) (i : Word w) (hi : i.val < N) (t : Fin 2) :
    store p snapshot m i (outAddr p t i) = field p snapshot i t := by
  have eqv (u : Fin 2) : (outAddr p t i = outAddr p u i) ↔ t = u := by
    simp only [reg.unique t u i i hi hi, and_true]
  change (if outAddr p t i = outAddr p 1 i then key p snapshot i
    else if outAddr p t i = outAddr p 0 i then bucket p snapshot i else _) = _
  simp only [eqv]
  fin_cases t <;> rfl

/-- The mate read alone determines the choice of input addresses. -/
theorem readAddress_eq {p : Fin 11 → Word w} {snapshot m : Memory w} (i : Word w)
    (h : m (readAddress p snapshot i 0).val = snapshot (readAddress p snapshot i 0).val) :
    readAddress p m i = readAddress p snapshot i := by
  change m (p 5+i).val = snapshot (p 5+i).val at h
  simp only [readAddress, targetSite, h]

private theorem events_same {p : Fin 11 → Word w} {m snapshot : Memory w} (i : Word w)
    (agree : ∀ c : Fin 6, m (readAddress p snapshot i c).val = snapshot (readAddress p snapshot i c).val) :
    events p m i = events p snapshot i := by
  have ha := readAddress_eq i (agree 0)
  have hv : readValue p m i = readValue p snapshot i := by
    funext t
    simpa [readValue, ha] using agree t
  simp only [events, bucket, key, ha, hv]

/-- The report sequence in increasing old-position order. Every lookup is
expressed directly in the initial external memory. -/
def scanReports (p : Fin 11 → Word w) (snapshot : Memory w) (k : ℕ) : ℕ → List (Report w)
  | 0 => []
  | n+1 => ⟨events p snapshot (Fin.ofNat _ k), some (Fin.ofNat _ (k+1))⟩ ::
      scanReports p snapshot (k+1) n

private theorem after_snapshot (p : Fin 11 → Word w) (snapshot m : Memory w) (i : Word w) :
    after m (events p snapshot i) = store p snapshot m i := rfl

private theorem after_succ (p : Fin 11 → Word w) (snapshot m : Memory w) (k n : ℕ) :
    after m (eventLog (scanReports p snapshot k (n+1))) =
      after (store p snapshot m (Fin.ofNat _ k))
        (eventLog (scanReports p snapshot (k+1) n)) := by
  simp only [scanReports, eventLog, List.flatMap_cons, after, List.foldl_append]
  rfl

private theorem scan_native_aux {p : Fin 11 → Word w} {N : ℕ} (snapshot : Memory w)
    (reg : Regions p snapshot N) (k n : ℕ) (m : Memory w) (bound : k+n ≤ N)
    (agree : ∀ c i, i.val < N → m (readAddress p snapshot i c).val = snapshot (readAddress p snapshot i c).val) :
    let M := (template visit 0).instantiate w p
    runSegment M.program (1+visit.length) (some (Fin.ofNat _ k)) m (List.replicate n []) =
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
    have hnext := ih (k+1) (store p snapshot m i) (by omega)
      (fun c j hj ↦ (store_other _ _ _ _ _ (fun t ↦ reg.inputs c t j i hj hi)).trans (agree c j hj))
    dsimp only
    rw [List.replicate_succ, runSegment, visit_native p m i, he, hn]
    simp only [after_snapshot, hnext, Option.map_some, scanReports, i]

/-- The complete native segment, with no change to the six input addresses. -/
theorem scan_native (p : Fin 11 → Word w) (N k n : ℕ) (m : Memory w) (reg : Regions p m N)
    (bound : k+n ≤ N) :
    let M := (template visit 0).instantiate w p
    runSegment M.program (1+visit.length) (some (Fin.ofNat _ k)) m (List.replicate n []) =
      some (scanReports p m k n) :=
  scan_native_aux m reg k n m bound (fun _ _ _ ↦ rfl)

private theorem scan_preserve {p : Fin 11 → Word w} {N : ℕ} {snapshot : Memory w}
    (reg : Regions p snapshot N) (m : Memory w) (k n addr : ℕ) (bound : k+n ≤ N)
    (outside : ∀ (t : Fin 2) (i : Word w), k ≤ i.val → i.val < k+n → addr ≠ outAddr p t i) :
    after m (eventLog (scanReports p snapshot k n)) addr = m addr := by
  induction n generalizing k m with
  | zero => rfl
  | succ n ih =>
    let i := Fin.ofNat (2^w) k
    have hv : i.val = k := Nat.mod_eq_of_lt (by have := reg.fits; omega)
    rw [after_succ, ih _ (k+1) (by omega) (fun t j hj hlt ↦ outside t j (by omega) (by omega))]
    exact store_other _ _ _ _ _ (fun t ↦ outside t i (by omega) (by omega))

private theorem scan_field {p : Fin 11 → Word w} {N : ℕ} {snapshot : Memory w}
    (reg : Regions p snapshot N) (m : Memory w) (k n : ℕ) (bound : k+n ≤ N)
    (t : Fin 2) (i : Word w) (hi : k ≤ i.val) (hi' : i.val < k+n) :
    after m (eventLog (scanReports p snapshot k n)) (outAddr p t i) = field p snapshot i t := by
  induction n generalizing k m with
  | zero => omega
  | succ n ih =>
    rw [after_succ]
    rcases eq_or_lt_of_le hi with he | he
    · have hv : Fin.ofNat (2^w) k = i := Fin.ext (by simp [he])
      rw [hv]
      rw [scan_preserve reg _ _ _ _ (by omega)]
      · exact store_field reg _ i (by omega) t
      · intro u j hj hlt h
        have hij := ((reg.unique t u i j (by omega) (by omega)).mp h).2
        subst j
        omega
    · exact ih _ _ (by omega) (by omega) (by omega)

/-- The returned registers, external work and complete memory contents of a
bundle scan, including the untouched portion of each output column. -/
structure ScanResult (p : Fin 11 → Word w) (N k n : ℕ) (m : Memory w) (rs : List (Report w)) : Prop where
  endCursor : endState (some (Fin.ofNat _ k)) rs = some (Fin.ofNat _ (k+n))
  calls : rs.length = n
  work : ∀ r ∈ rs, r.events.length = visit.length ∧ countProbes r.events = 8
  cost : RAMBuckets.cost (fun r : Report w ↦ countProbes r.events) rs = 9*n
  readback : ∀ (t : Fin 2) (i : Word w), k ≤ i.val → i.val < k+n →
    after m (eventLog rs) (outAddr p t i) = field p m i t
  preserve : ∀ addr, (∀ (t : Fin 2) (i : Word w), k ≤ i.val → i.val < k+n → addr ≠ outAddr p t i) →
    after m (eventLog rs) addr = m addr
  inputs : ∀ (c : Fin 6) (i : Word w), i.val < N →
    after m (eventLog rs) (readAddress p m i c).val = m (readAddress p m i c).val

private theorem scan_accounting (p : Fin 11 → Word w) (m : Memory w) (k n : ℕ) :
    let rs := scanReports p m k n
    endState (some (Fin.ofNat _ k)) rs = some (Fin.ofNat _ (k+n)) ∧ rs.length = n ∧
      (∀ r ∈ rs, r.events.length = visit.length ∧ countProbes r.events = 8) ∧
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
      · exact events_work p m _
      · exact hwork r h
    · rw [scanReports, RAMBuckets.cost, (events_work p m _).2, hcost, Nat.mul_succ]
      omega

/-- Execute the whole interval from its initial memory. Every one of the
two output columns agrees with the classification computed from the six
original input values. -/
theorem scan_run (p : Fin 11 → Word w) (N k n : ℕ) (m : Memory w) (regions : Regions p m N)
    (bound : k+n ≤ N) :
    let M := (template visit 0).instantiate w p
    ∃ rs, runSegment M.program (1+visit.length) (some (Fin.ofNat _ k)) m (List.replicate n []) = some rs ∧
      ScanResult p N k n m rs := by
  obtain ⟨he,hl,hw,hc⟩ := scan_accounting p m k n
  refine ⟨scanReports p m k n, scan_native p N k n m regions bound, he, hl, hw, hc,
    scan_field regions m k n bound, fun addr ↦ scan_preserve regions m k n addr bound, ?_⟩
  intro c i hi
  apply scan_preserve regions m k n _ bound
  exact fun t j _ hlt ↦ regions.inputs c t i j hi (hlt.trans_le bound)

/-- Following a stored mate after the scan selects the same destination
cells as following it before the scan. -/
theorem ScanResult.readAddress_stable {p : Fin 11 → Word w} {N k n : ℕ} {m : Memory w} {rs}
    (r : ScanResult p N k n m rs) (i : Word w) (hi : i.val < N) :
    readAddress p (after m (eventLog rs)) i = readAddress p m i :=
  readAddress_eq i (r.inputs 0 i hi)

end CompressorRecords.BundleRAM

end VPVNP
end Computability
end OAI
