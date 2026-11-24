import OAI.Computability.VPVNP.CompressorRecordsBundleLists
import OAI.Computability.VPVNP.CompressorRecordsSchedule
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# Physical immediate-preimage rows of a degree refresh

The promoted port keeps its old site ordinal. One reset call per site
writes its owner, the singleton list length and the old identifier in
the corresponding child row. The resulting tables feed the same traversal
reader as the shrinking placement tables. The scan initializes each live
cell explicitly, irrespective of its initial contents.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshPlacement

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM
open scoped Fin.CommRing

variable {w : ℕ}

/-- Three public array bases, each with a unit stride. -/
def code : List (Op 4 3) :=
  [.stateWord 0,.constant 1 1,
   .publicWord 2 0,.binary .add 2 2 0,.write 2 0,
   .publicWord 2 1,.binary .add 2 2 0,.write 2 1,
   .publicWord 2 2,.binary .add 2 2 0,.write 2 0,
   .binary .add 0 0 1]

/-- Scheduled worker that writes one promoted site's owner, singleton preimage length and child
identifier from its cursor. -/
def worker : Schedule.Pass := ⟨_,_,_,template code 0⟩

/-- Select the three destination heads from operand positions one, three and five of the
refresh placement packet. -/
def bank (p : Fin 6 → Word w) : Fin 3 → Word w := ![p 1,p 3,p 5]

/-- Word address of one site's entry in the selected owner, length or child array. -/
def cell (p : Fin 6 → Word w) (c : Fin 3) (i : Word w) : Word w := bank p c + i

/-- Value written for this site. The owner and sole child receive its ordinal, and the preimage
length receives one. -/
def value (c : Fin 3) (i : Word w) := if c = 1 then 1 else i

/-- Exact private ticks and three external writes that install the singleton preimage row at
cursor i. -/
def events (p : Fin 6 → Word w) (i : Word w) : List (Event w) :=
  [.tick,.tick,.tick,.tick,.write (cell p 0 i) i,.tick,.tick,.write (cell p 1 i) 1,
   .tick,.tick,.write (cell p 2 i) i,.tick]

/-- The placement worker's write trace and its returned successor cursor i+1. -/
def report (p : Fin 6 → Word w) (i : Word w) : Report w := ⟨events p i,some (i+1)⟩

theorem native (p : Fin 6 → Word w) (m : Memory w) (i : Word w) :
    let M := worker.table.instantiate w (bank p)
    execute M.program 13 (M.program.start i) m [] = some (report p i) := by
  let M := (template code 0).instantiate w (bank p)
  change execute M.program (1+code.length) ⟨M.entry,i,fun _ => 0,fun _ => 0⟩ m [] = _
  rw [execute_template,run_eq_trace]
  simp (config := {decide := true}) [code,trace,Op.effect,BinaryOp.eval,report,events,cell,bank,Function.update]

/-- Consecutive placement reports for the indicated number of sites, starting at cursor k. -/
def log (p : Fin 6 → Word w) (k : ℕ) : ℕ → List (Report w)
  | 0 => []
  | n+1 => report p (Fin.ofNat _ k) :: log p (k+1) n

theorem run (p : Fin 6 → Word w) (k n : ℕ) (m : Memory w) :
    runSegment (worker.table.instantiate w (bank p)).program 13 (some (Fin.ofNat _ k)) m
      (List.replicate n []) = some (log p k n) := by
  induction n generalizing k m with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ,runSegment,native]
    change (runSegment _ _ (some ((Fin.ofNat (2^w) k)+1)) _ _).map _ = _
    rw [show ((Fin.ofNat (2^w) k)+1) = Fin.ofNat _ (k+1) from by apply Fin.ext; simp [Fin.val_add]]
    rw [ih]; rfl

theorem cost (p : Fin 6 → Word w) (k n : ℕ) :
    (log p k n).length = n ∧ RAMBuckets.cost Report.probes (log p k n) = 4*n ∧
      ∀ r ∈ log p k n, r.events.length+1 = 13 ∧ r.probes = 3 := by
  induction n generalizing k with
  | zero => simp [log,RAMBuckets.cost]
  | succ n ih =>
    obtain ⟨h₁,h₂,h₃⟩ := ih (k+1)
    refine ⟨by rw [log,List.length_cons,h₁],?_,?_⟩
    · change 1+3+RAMBuckets.cost Report.probes (log p (k+1) n) = _
      rw [h₂,Nat.mul_succ]; omega
    · intro r hr
      rcases List.mem_cons.mp hr with rfl | h
      · exact ⟨rfl,rfl⟩
      · exact h₃ _ h

private theorem bounds {p : Fin 6 → Word w} {N : ℕ} (reg : RowRegions p)
    (h₀ : (p 0).val = N) (h₂ : (p 2).val = N) (h₄ : (p 4).val = 1) (c : Fin 3) :
    (bank p c).val+N ≤ 2^w := by
  obtain ⟨hc,hr,hf⟩ := reg
  rw [h₀] at hc; rw [h₂] at hr; rw [h₂,h₄,Nat.mul_one] at hf
  fin_cases c
  · change (p 1).val+N ≤ _; omega
  · change (p 3).val+N ≤ _; omega
  · change (p 5).val+N ≤ _; omega

private theorem cell_val {p : Fin 6 → Word w} {N : ℕ} (reg : RowRegions p)
    (h₀ : (p 0).val = N) (h₂ : (p 2).val = N) (h₄ : (p 4).val = 1)
    (c : Fin 3) (i : ℕ) (hi : i<N) :
    (cell p c (Fin.ofNat _ i)).val = (bank p c).val+i := by
  have h := bounds reg h₀ h₂ h₄ c
  rw [cell,Fin.val_add,Fin.val_ofNat,Nat.mod_eq_of_lt (by omega : i < 2^w),Nat.mod_eq_of_lt (by omega)]

private theorem unique {p : Fin 6 → Word w} {N : ℕ} (reg : RowRegions p)
    (h₀ : (p 0).val = N) (h₂ : (p 2).val = N) (h₄ : (p 4).val = 1)
    {c d : Fin 3} {i j : ℕ} (hi : i<N) (hj : j<N) :
    (cell p c (Fin.ofNat _ i)).val = (cell p d (Fin.ofNat _ j)).val ↔ c=d ∧ i=j := by
  rw [cell_val reg h₀ h₂ h₄ _ _ hi,cell_val reg h₀ h₂ h₄ _ _ hj]
  have hbase := reg.ownersBeforeCounts
  have hcount := reg.countsBeforeRows
  rw [h₀] at hbase; rw [h₂] at hcount
  fin_cases c <;> fin_cases d <;> simp [bank] <;> omega

private theorem saved (p : Fin 6 → Word w) (m : Memory w) (i : Word w) (j : ℕ)
    (h : ∀ c, j ≠ (cell p c i).val) : after m (events p i) j = m j := by
  simp [after,events,update,writeMemory,h]

private theorem written {p : Fin 6 → Word w} {N : ℕ} (reg : RowRegions p)
    (h₀ : (p 0).val = N) (h₂ : (p 2).val = N) (h₄ : (p 4).val = 1)
    (m : Memory w) (i : ℕ) (hi : i<N) (c : Fin 3) :
    after m (events p (Fin.ofNat _ i)) (cell p c (Fin.ofNat _ i)).val = value c (Fin.ofNat _ i) := by
  have heq (a b : Fin 3) : (cell p a (Fin.ofNat _ i)).val = (cell p b (Fin.ofNat _ i)).val ↔ a=b := by
    rw [unique reg h₀ h₂ h₄ hi hi]; simp
  have heq' (a b : Fin 3) : (cell p a (i : Word w)).val = (cell p b (i : Word w)).val ↔ a=b := heq a b
  fin_cases c <;> simp (config := {decide := true}) [after,events,update,writeMemory,value,heq']

private theorem scan_fields {p : Fin 6 → Word w} {N : ℕ} (reg : RowRegions p)
    (h₀ : (p 0).val = N) (h₂ : (p 2).val = N) (h₄ : (p 4).val = 1) (m : Memory w)
    (k n : ℕ) (hk : k+n ≤ N) :
    let out := after m (eventLog (log p k n))
    (∀ i, k ≤ i → i < k+n → ∀ c, out (cell p c (Fin.ofNat _ i)).val = value c (Fin.ofNat _ i)) ∧
    (∀ addr, (∀ i, k ≤ i → i < k+n → ∀ c, addr ≠ (cell p c (Fin.ofNat _ i)).val) → out addr = m addr) := by
  induction n generalizing k m with
  | zero => exact ⟨fun i h h' => by omega,fun _ _ ↦ rfl⟩
  | succ n ih =>
    let mid := after m (events p (Fin.ofNat _ k))
    have hs := ih mid (k+1) (by omega)
    intro out
    change (∀ i, _ → _ → ∀ c, after mid (eventLog (log p (k+1) n)) _ = _) ∧
      ∀ addr, _ → after mid (eventLog (log p (k+1) n)) addr = _
    constructor
    · intro i hi hj c
      rcases eq_or_lt_of_le hi with rfl | hgt
      · rw [hs.2]
        · exact written reg h₀ h₂ h₄ m _ (by omega) c
        · intro j hj₁ hj₂ d he
          have same := (unique reg h₀ h₂ h₄ (by omega) (by omega)).mp he
          omega
      · exact hs.1 i hgt (by omega) c
    · intro addr ha
      rw [hs.2 addr (fun i hi hj c ↦ ha i (by omega) (by omega) c)]
      exact saved p m _ _ (ha k le_rfl (by omega))

private theorem preimage_singleton {N : ℕ} (hN : N ≤ 2^w) (v : Word w) (hv : v.val<N) :
    preimagePrefix id v N = [v] := by
  have mem (x : Word w) : x ∈ preimagePrefix id v N ↔ x=v := by
    rw [BundleLists.mem_preimagePrefix_iff _ _ _ _ hN]
    exact ⟨And.right,fun e ↦ ⟨e ▸ hv,e⟩⟩
  have pair := BundleLists.preimagePrefix_pairwise id v N hN
  cases h : preimagePrefix id v N with
  | nil => have hm := (mem v).2 rfl; simp [h] at hm
  | cons x xs =>
    have hx := (mem x).1 (by simp [h]); subst x
    cases xs with
    | nil => rfl
    | cons y ys =>
      have hy := (mem y).1 (by simp [h]); subst y
      rw [h,List.pairwise_cons] at pair
      exact (lt_irrefl _ (pair.1 v (by simp))).elim

/-- The post-memory has the complete ordered list at each new identifier,
and every address outside the three placement arrays keeps its old value. -/
theorem collected {p : Fin 6 → Word w} {N : ℕ} (reg : RowRegions p)
    (h₀ : (p 0).val = N) (h₂ : (p 2).val = N) (h₄ : (p 4).val = 1) (m : Memory w) :
    let out := after m (eventLog (log p 0 N))
    PreimagesAt p id out N ∧
    ∀ addr, (∀ i < N, ∀ c, addr ≠ (cell p c (Fin.ofNat _ i)).val) → out addr = m addr := by
  intro out
  obtain ⟨fields,keep⟩ := scan_fields reg h₀ h₂ h₄ m 0 N (by omega)
  simp only [Nat.zero_add] at fields keep
  refine ⟨⟨?_,?_⟩,fun addr h ↦ keep addr (fun i _ hi ↦ h i hi)⟩
  · intro i hi
    have h := fields i.val (Nat.zero_le _) ((show i.val < (p 0).val from hi).trans_eq h₀) 0
    simpa [ownerAt,cell,bank,value,Fin.ofNat_eq_cast,Fin.cast_val_eq_self] using h
  · intro i hi
    have h := (show i.val < (p 2).val from hi).trans_eq h₂
    have hcap : p 4 = 1 := Fin.ext (h₄.trans (Nat.mod_eq_of_lt (h₄ ▸ (p 4).isLt)).symm)
    have hcount := fields i.val (Nat.zero_le _) h 1
    have hrow := fields i.val (Nat.zero_le _) h 2
    simp only [Fin.ofNat_eq_cast,Fin.cast_val_eq_self] at hcount hrow
    rw [preimage_singleton (h₂ ▸ (p 2).isLt.le) i h]
    refine ⟨?_,?_⟩
    · change (out (cell p 1 i).val).val = 1
      change out (cell p 1 i).val = 1 at hcount
      rw [hcount]; exact Nat.mod_eq_of_lt (h₄.ge.trans_lt (p 4).isLt)
    · intro z
      have hz : z.val = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (show z.val < 1 from z.isLt))
      simpa [rowAt,hcap,hz,cell,bank,value] using hrow

end CompressorRecords.RefreshPlacement

end VPVNP
end Computability
end OAI
