import OAI.Hierarchy.ProbeStageWordStore

namespace OAI
/-! # The native linear scan invoked only on a missed candidate string -/

namespace Hierarchy.ProbeStage.Fallback
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing

/-- The counter starts at zero after a chunk hit, or at the degree on a miss. `left` and
`right` are cells holding the starting addresses of the current endpoint's counter blocks. -/
structure Layout where
  remaining : ℕ
  chosen : ℕ
  left : ℕ
  right : ℕ
  quota : ℕ

def cell (a : ℕ) : Formula 1 := .load (.lit a)

def count (base cursor : ℕ) : Formula 1 := .load (.op .add (cell base) (cell cursor))

/-- The counted loop has already decremented the cursor when it enters this expression. -/
def update (s : Layout) : Formula 1 :=
  .select .lt (count s.left s.remaining) (.lit s.quota)
    (.select .lt (count s.right s.remaining) (.lit s.quota) (cell s.remaining) (cell s.chosen)) (cell s.chosen)

def possible {w : ℕ} (s : Layout) (m : Memory w) (c : Word w) : Prop :=
  m (m (s.left:Word w).val+c).val < (s.quota:Word w) ∧
    m (m (s.right:Word w).val+c).val < (s.quota:Word w)

instance {w : ℕ} (s : Layout) (m : Memory w) (c : Word w) : Decidable (possible s m c) :=
  inferInstanceAs (Decidable (_ ∧ _))

def result {w : ℕ} (s : Layout) (m : Memory w) :=
  let c := m (s.remaining:Word w).val
  if possible s m c then c else m (s.chosen:Word w).val

def next {w : ℕ} (s : Layout) (m : Memory w) : Memory w := Function.update m s.chosen (result s m)

theorem update_eval {w : ℕ} (s : Layout) (m : Memory w) :
    WordStore.value s.chosen (update s) m = result s m := by
  let c := m (s.remaining:Word w).val
  let l := m (m (s.left:Word w).val+c).val
  let r := m (m (s.right:Word w).val+c).val
  change (if decide (l<(s.quota:Word w))=true then (if decide (r<(s.quota:Word w))=true then c else m (s.chosen:Word w).val) else m (s.chosen:Word w).val)=
    (if l<(s.quota:Word w) ∧ r<(s.quota:Word w) then c else m (s.chosen:Word w).val)
  by_cases a : l<(s.quota:Word w) <;> by_cases b : r<(s.quota:Word w) <;> simp [a,b]

def procedure (w : ℕ) (s : Layout) : Procedure w :=
  (WordStore.put w s.chosen (update s)).counted (s.remaining:Word w)

def image {w : ℕ} (s : Layout) (m : Memory w) :=
  WordStore.down (s.remaining:Word w) (next s) (m (s.remaining:Word w).val).val m

theorem execute {w : ℕ} (s : Layout) (m : Memory w) (room : s.chosen+1 < 2^w)
    (other : (s.remaining:Word w).val ≠ s.chosen) :
    (procedure w s).Exec m (image s m) ((m (s.remaining:Word w).val).val*(7+(2*(update s).work+8))+4) := by
  apply WordStore.down_exec
  · intro a
    unfold next
    rw [← update_eval]
    exact WordStore.execute s.chosen (update s) a room
  · intro a
    exact Function.update_of_ne other _ _

/-- The logical result of trying the colors from `n-1` down to zero is the least available
color below `n`, or the preexisting choice when none are available. -/
def pick (good : ℕ → Bool) : ℕ → ℕ → ℕ
  | 0,initial => initial
  | n+1,initial => pick good n (if good n then n else initial)

theorem pick_miss (good : ℕ → Bool) (n initial : ℕ) (miss : ∀ c<n, good c=false) :
    pick good n initial=initial := by
  induction n generalizing initial with
  | zero => rfl
  | succ n ih => simp only [pick,miss n (by omega),Bool.false_eq_true,ite_false]; exact ih _ (fun c h=>miss c (by omega))

theorem pick_hit (good : ℕ → Bool) (n initial c : ℕ) (hc : c<n) (hit : good c=true)
    (prior : ∀ j<c, good j=false) : pick good n initial=c := by
  induction n generalizing initial with
  | zero => omega
  | succ n ih =>
    rw [pick]
    by_cases h : c=n
    · subst n
      simpa [hit] using pick_miss good c c prior
    · exact ih _ (by omega)

end Hierarchy.ProbeStage.Fallback

end OAI
