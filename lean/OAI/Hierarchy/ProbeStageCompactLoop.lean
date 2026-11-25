import OAI.Hierarchy.ProbeStageCompactControls
import OAI.Hierarchy.ProbeStageProgramSize
import OAI.Hierarchy.ProtocolRAMCheapCode
import OAI.ThreeFlat.XParentTimeProcedure

namespace OAI
/-! # A single native counted visit loop, with the original zero root cells restored -/

namespace Hierarchy.ProbeStage.Native.CompactLoop
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat RAM PhysicalProcedure DescriptorExpr PhysicalPinsExpr
open scoped Fin.CommRing BigOperators

/-- The two temporary controls are in the original zero root group. -/
theorem in_root {h : ℕ} (large : 4≤h) : 2^h≤cursor h ∧ cursor h<limit h ∧ limit h<2*2^h := by
  have enough : 2^4≤2^h:=Nat.pow_le_pow_right (by decide) large
  dsimp [cursor,limit]
  omega

private theorem ne (h : ℕ) : cursor h≠limit h := by simp [cursor,limit]

private theorem next {w : ℕ} (h i j : ℕ) (m : Memory w) :
    Function.update (cells h i m) (cursor h) (j:Word w)=cells h j m := by
  funext x
  by_cases a : x=cursor h
  · subst x; simp [cells,ne]
  · simp [cells,Function.update_apply,a]

private theorem initial {w : ℕ} (h : ℕ) (m : Memory w) :
    Function.update (Function.update m (limit h) ((2^h:ℕ):Word w)) (cursor h) 0=cells h 0 m := by
  funext x
  by_cases a : x=cursor h
  · subst x; simp [cells,ne]
  · simp [cells,Function.update_apply,a]

private theorem finish {w : ℕ} (h j : ℕ) (m : Memory w) (c : m (cursor h)=0) (l : m (limit h)=0) :
    Function.update (Function.update (cells h j m) (cursor h) 0) (limit h) 0=m := by
  funext x
  by_cases a : x=cursor h
  · subst x; simp [ne,c]
  · by_cases b : x=limit h
    · subst x; simp [l]
    · simp [cells,a,b]

/-- One copy of the row body is installed. The traversal initializes the cursor itself. -/
def program {w : ℕ} (h : ℕ) (body : Procedure w) : Procedure w :=
  (((WordStore.put w (limit h) (.lit (2^h))).seq (XParentTimeLoop.traversal (cursor h) (limit h) body)).seq
    (WordStore.put w (cursor h) (.lit 0))).seq (WordStore.put w (limit h) (.lit 0))

def cost (h : ℕ) (price : ℕ→ℕ) := 38+10*2^h+∑i∈Finset.range (2^h),price i

private theorem store {w : ℕ} (a b : ℕ) (m : Memory w) (room : a+1<2^w) :
    (WordStore.put w a (.lit b)).Exec m (Function.update m a (b:Word w)) 10 :=
  WordStore.execute a (.lit b) m room

/-- The per-row invoice may depend on the genuine chronological state. Only the two
actual finite addresses are touched by the surrounding traversal. -/
theorem run {w : ℕ} (h : ℕ) (body : Procedure w) (row : ℕ→Memory w) (price : ℕ→ℕ)
    (room : limit h+1<2^w)
    (doneCursor : row (2^h) (cursor h)=0) (doneLimit : row (2^h) (limit h)=0)
    (step : ∀j,j<2^h→body.Exec (cells h j (row j)) (cells h j (row (j+1))) (price j)) :
    (program h body).Exec (row 0) (row (2^h)) (cost h price) := by
  let n:=2^h
  let state (j : ℕ) (mem : Memory w) := mem=cells h j (row j)
  have flags (j : ℕ) (m : Memory w) (ok : state j m) : m (cursor h)=(j:Word w) := by
    rw [show m=cells h j (row j) from ok]
    simp [cells,ne]
  have top (j : ℕ) (m : Memory w) (ok : state j m) : m (limit h)=(n:Word w) := by
    rw [show m=cells h j (row j) from ok]
    simp [cells,n]
  have each (j : ℕ) (less : j<n) : body.Spec (state j)
      (fun _ o=>o (cursor h)=(j:Word w) ∧ state (j+1) (Function.update o (cursor h) ((j+1:ℕ):Word w))) (price j) := by
    intro P R K M pc reg pub exit placed data cfg mem entry hmem
    obtain ⟨t,ht,after,im,advance,returned,eqn⟩ :=
      step j less M pc reg pub exit placed data cfg mem entry hmem
    subst im
    exact ⟨t,ht,after,_,advance,returned,by simp [cells,ne],next h j (j+1) (row (j+1))⟩
  have c : cursor h+1<2^w := by change 2^h+6+1<2^w;change 2^h+7+1<2^w at room;omega
  have l : limit h<2^w:=by omega
  have cap : n<2^w:=by change 2^h<2^w;change 2^h+7+1<2^w at room;omega
  have loop : (XParentTimeLoop.traversal (cursor h) (limit h) body).Spec
      (fun m=>state 0 (Function.update m (cursor h) (0:Word w))) (fun _ o=>state n o)
      (8+10*n+∑j∈Finset.range n,price j) :=
    XParentTimeLoop.traverse_run (cursor h) (limit h) n body price state (by omega) l cap flags top each
  let m:=Function.update (row 0) (limit h) (n:Word w)
  have middle : (XParentTimeLoop.traversal (cursor h) (limit h) body).Exec m (cells h n (row n))
      (8+10*n+∑i∈Finset.range n,price i) := by
    intro P R K M pc reg pub exit placed data cfg u entry hu
    subst u
    exact loop M pc reg pub exit placed data cfg m entry (initial h (row 0))
  have ran : (program h body).Exec (row 0)
      (Function.update (Function.update (cells h n (row n)) (cursor h) 0) (limit h) 0)
      (((10+(8+10*n+∑i∈Finset.range n,price i))+10)+10) :=
    Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then
      (store (limit h) n (row 0) room) middle) (store (cursor h) 0 _ c))
      (store (limit h) 0 _ room)
  rw [finish h n (row n) doneCursor doneLimit] at ran
  change (program h body).Exec (row 0) (row n) (38+10*n+∑i∈Finset.range n,price i)
  have bill : ((10+(8+10*n+∑i∈Finset.range n,price i))+10)+10 =
      38+10*n+∑i∈Finset.range n,price i := by omega
  rw [←bill]
  intro P R K M pc reg pub exit placed data cfg mem entry start
  exact ran M pc reg pub exit placed data cfg mem entry start

private theorem literal_cheap (w a val : ℕ) : CheapCode (WordStore.put w a (.lit val)) :=
  writing_cheap _ _ _ _ (by simp [AdmissionBank.closed,Term.literal,admissible,opAllowed])

theorem cheap {w : ℕ} (h : ℕ) (body : Procedure w) (ok : CheapCode body) : CheapCode (program h body) := by
  have loop : CheapCode (XParentTimeLoop.traversal (cursor h) (limit h) body) := by
    intro P R K pc reg pub exit i
    induction i using Fin.addCases with
    | left j =>
      simp only [XParentTimeLoop.traversal,XParentTimeLoop.block,Fin.addCases_left]
      fin_cases j <;> trivial
    | right j =>
      simp only [XParentTimeLoop.traversal,XParentTimeLoop.block,Fin.addCases_right,ContinuationLink.Block.reindex]
      exact ok _ _ _ _ j
  intro P R K pc reg pub exit i
  exact cheap_seq (cheap_seq (cheap_seq (literal_cheap w (limit h) (2^h)) loop)
    (literal_cheap w (cursor h) 0)) (literal_cheap w (limit h) 0) pc reg pub exit i

theorem code {w : ℕ} (h : ℕ) (body : Procedure w) : text (program h body)=63+text body := by
  have literal (a b : ℕ) : text (WordStore.put w a (.lit b))=15 := by
    simp [WordStore.put,PhysicalInputPhases.writing,text,Term.labels_eq,AdmissionBank.binds_closed,Formula.work]
  simp only [program,text_seq,literal]
  dsimp only [XParentTimeLoop.traversal,text]
  omega

end Hierarchy.ProbeStage.Native.CompactLoop

end OAI
