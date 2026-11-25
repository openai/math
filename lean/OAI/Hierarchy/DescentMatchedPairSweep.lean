import OAI.Hierarchy.DescentMatchedPairRecord

namespace OAI
/-! # Dense immutable matched rows across the chronological list of whole items -/

namespace Hierarchy.DescentPacking.PairRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing
variable {w n : ℕ} {z bins dest dead scratch : ℕ}

def sweep (w n : ℕ) (src : ℕ→Inputs) (z bins dest dead scratch : ℕ) : ℕ→ℕ→Procedure w
  | _,0 => scan w scratch 0 (.lit 0)
  | t,c+1 => (records w n (src t) z bins dest dead scratch (List.finRange 9)).seq
      (sweep w n src z bins dest dead scratch (t+1) c)
termination_by _ c => c

def output (n : ℕ) (src : ℕ→Inputs) (z bins dest dead scratch : ℕ) : ℕ→ℕ→Memory w→Memory w
  | _,0,m => m
  | t,c+1,m => output n src z bins dest dead scratch (t+1) c
      (result n (src t) z bins dest dead scratch (List.finRange 9) m)
termination_by _ c _ => c

def cost (n : ℕ) (src : ℕ→Inputs) (z bins dest dead : ℕ) : ℕ→ℕ→ℕ
  | _,0 => 4
  | t,c+1 => ticks n (src t) z bins dest dead (List.finRange 9)+cost n src z bins dest dead (t+1) c
termination_by _ c => c

theorem record_agrees {s : Inputs} (m : Memory w) (b : Space w n s bins dest dead scratch m) :
    agrees dest (result n s z bins dest dead scratch (List.finRange 9) m) m := by
  intro x hx
  have := b.dense
  have := b.padding
  apply records_frame _ _ b _ (.inl (by omega))
  intro _ _ q
  unfold target
  split <;> omega

theorem sweep_exec (src : ℕ→Inputs) (t c : ℕ) (m : Memory w) (room : scratch < 2^w)
    (space : ∀i,t ≤ i→i<t+c→Space w n (src i) bins dest dead scratch m) :
    (sweep w n src z bins dest dead scratch t c).Exec m (output n src z bins dest dead scratch t c m)
      (cost n src z bins dest dead t c) := by
  induction c generalizing t m with
  | zero =>
    simp only [sweep, output, cost]
    have empty : ProtocolRAM.image scratch 0 (.lit 0) m = m :=
      fillSegment_zero _ _ _
    intro P R K machine pc reg pub exit installed vals cfg mem entry same
    have step := @scan_exec w scratch 0 (.lit 0) m trivial (by simpa using room)
      P R K machine pc reg pub exit installed vals cfg mem entry same
    simpa only [empty, Nat.zero_mul, Nat.add_zero] using step
  | succ c ih =>
    simp only [sweep, output, cost]
    have first := space t le_rfl (by omega)
    have same := record_agrees (z:=z) m first
    let fs := List.finRange 9
    let mid := result n (src t) z bins dest dead scratch fs m
    have later : (sweep w n src z bins dest dead scratch (t+1) c).Exec mid
        (output n src z bins dest dead scratch (t+1) c mid)
        (cost n src z bins dest dead (t+1) c) :=
      ih (t+1) mid (fun i hi ht => transfer (space i (by omega) (by omega)) same)
    have headStep : (records w n (src t) z bins dest dead scratch fs).Exec m mid
        (ticks n (src t) z bins dest dead fs) :=
      @records_exec w n (src t) z bins dest dead scratch fs m first
    exact @Procedure.Exec.then w (records w n (src t) z bins dest dead scratch fs)
      (sweep w n src z bins dest dead scratch (t+1) c) m mid
      (output n src z bins dest dead scratch (t+1) c mid)
      (ticks n (src t) z bins dest dead fs) (cost n src z bins dest dead (t+1) c)
      (@headStep) (@later)

theorem sweep_frame (src : ℕ→Inputs) (t c : ℕ) (m : Memory w)
    (space : ∀i,t ≤ i→i<t+c→Space w n (src i) bins dest dead scratch m)
    (x : ℕ) (out : x < scratch ∨ scratch+2*n≤x)
    (miss : ∀i,t ≤ i→i<t+c→∀f : Fin 9,∀q : Fin n,x≠target (src i) bins dest dead f.val m q) :
    output n src z bins dest dead scratch t c m x=m x := by
  induction c generalizing t m with
  | zero => simp only [output]
  | succ c ih =>
    simp only [output]
    have early := space t le_rfl (by omega)
    have same := record_agrees (z:=z) m early
    exact (ih (t+1) _ (fun i hi ht=>transfer (space i (by omega) (by omega)) same)
      (fun i hi ht f q=>by rw [target_transfer (space i (by omega) (by omega)) same];exact miss i (by omega) (by omega) f q)).trans
      (records_frame _ m early x out (fun f _ q=>miss t le_rfl (by omega) f q))

/-- The previous scans issue the two prefix words before the writer starts.
Every later active item starts after all units of each earlier accepted item. -/
def ordered (src : ℕ→Inputs) (bins t c : ℕ) (m : Memory w) : Prop :=
  ∀a b,t≤a→a<b→b<t+c→(m (src a).choice).val < bins →
    (m (src a).acceptedBefore).val+(m (src a).amount).val≤(m (src b).acceptedBefore).val

theorem sweep_read (src : ℕ→Inputs) (t c : ℕ) (m : Memory w)
    (space : ∀i,t ≤ i→i<t+c→Space w n (src i) bins dest dead scratch m)
    (sorted : ordered src bins t c m) (a : ℕ) (ha : t≤a) (last : a<t+c) (f : Fin 9) (q : Fin n)
    (accept : (m (src a).choice).val < bins) (live : q.val < (m (src a).amount).val) :
    output n src z bins dest dead scratch t c m (dest+9*((m (src a).acceptedBefore).val+q.val)+f.val)=
      (field (src a) z f).eval m (q.val:Word w) := by
  induction c generalizing t m with
  | zero => omega
  | succ c ih =>
    simp only [output]
    let m₁ := result n (src t) z bins dest dead scratch (List.finRange 9) m
    have phase := space t le_rfl (by omega)
    have same : agrees dest m₁ m := record_agrees m phase
    have next (i : ℕ) (hi : t+1 ≤ i) (ht : i<t+1+c) :=
      transfer (space i (by omega) (by omega)) same
    by_cases first : a=t
    · subst a
      have hr := phase.dense
      have hd := phase.padding
      have qn := q.isLt
      have fn := f.isLt
      have kept := sweep_frame (z:=z) src (t+1) c m₁ next
        (dest+9*((m (src t).acceptedBefore).val+q.val)+f.val) (.inl (by omega)) (by
          intro i hi ht g r
          rw [target_transfer (space i (by omega) (by omega)) same]
          have order := sorted t i le_rfl (by omega) (by omega) accept
          unfold target
          split <;> omega)
      exact kept.trans (nine_fields m phase f q accept live)
    · have loc := space a ha last
      have nt : t+1≤a := by omega
      have order : ordered src bins (t+1) c m₁ := by
        intro i j lowI before endJ chosen
        have bi := space i (by omega) (by omega)
        have bj := space j (by omega) (by omega)
        simp only [same _ (low _ bi.choice)] at chosen
        simp only [same _ (low _ bi.acceptedBefore),same _ (low _ bi.amount),same _ (low _ bj.acceptedBefore)]
        exact sorted i j (by omega) before (by omega) chosen
      have read := ih (t+1) m₁ next order nt (by omega)
        (by simpa only [same _ (low _ loc.choice)] using accept) (by simpa only [same _ (low _ loc.amount)] using live)
      rw [same _ (low _ loc.acceptedBefore)] at read
      exact read.trans (eval_below _ _ m m₁ (fits (z:=z) (bins:=bins) (dead:=dead) loc.toEarly f).2 same)

end Hierarchy.DescentPacking.PairRAM

end OAI
