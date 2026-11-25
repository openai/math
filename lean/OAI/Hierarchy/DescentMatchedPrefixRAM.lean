import OAI.Hierarchy.DescentMatchedPairRAM

namespace OAI
/-! # Recording compact and original stream offsets from physical first-fit tags -/

namespace Hierarchy.DescentPacking.PairRAM.Prefix
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing BigOperators
variable {w : ℕ}

def base (out t : ℕ) := out+2*t

theorem base_succ (out t : ℕ) : base out (t+1)=base out t+2 := by simp [base,Nat.mul_add,Nat.add_assoc]

def term (bins need tag out t : ℕ) : Expr :=
  let a := scalar need
  let live := Expr.branch .lt (scalar tag) (.lit bins) a (.lit 0)
  .branch .eq .row (.lit 0) (add (scalar (base out t)) live) (add (scalar (base out t+1)) a)

def column (bins : ℕ) (need tag : ℕ→ℕ) (out t : ℕ) :=
  term bins (need t) (tag t) out t

def steps (w bins : ℕ) (need tag : ℕ→ℕ) (out : ℕ) : ℕ→ℕ→Procedure w
  | t,0 => scan w (base out t) 0 (.lit 0)
  | t,c+1 => (scan w (base out (t+1)) 2 (column bins need tag out t)).seq (steps w bins need tag out (t+1) c)
termination_by _ c => c

def history (bins : ℕ) (need tag : ℕ→ℕ) (out : ℕ) : ℕ→ℕ→Memory w→Memory w
  | _,0,m => m
  | t,c+1,m => history bins need tag out (t+1) c
      (ProtocolRAM.image (base out (t+1)) 2 (column bins need tag out t) m)
termination_by _ c _ => c

def program (w bins : ℕ) (need tag : ℕ→ℕ) (out count : ℕ) :=
  (scan w out 2 (.lit 0)).seq (steps w bins need tag out 0 count)

def after (bins : ℕ) (need tag : ℕ→ℕ) (out count : ℕ) (m : Memory w) :=
  history bins need tag out 0 count (ProtocolRAM.image out 2 (.lit 0) m)

theorem term_work (bins need tag out t : ℕ) : (term bins need tag out t).work=39 := by rfl

private theorem wordFits {a dst : ℕ} (small : 1 < 2^w) (lo : a < dst) :
    (scalar a).Fits w dst := ⟨⟨Nat.zero_lt_one,small,Nat.succ_le_of_lt lo⟩,trivial⟩

private theorem step_fit (bins : ℕ) {need tag out t : ℕ} (one : 1 < 2^w)
    (lowN : need < out) (lowT : tag < out) : (term bins need tag out t).Fits w (base out (t+1)) := by
  have offset : out≤base out t := Nat.le_add_right _ _
  rw [base_succ]
  exact ⟨trivial,trivial,
    ⟨wordFits one (by omega),wordFits one (by omega),trivial,wordFits one (by omega),trivial⟩,
    ⟨wordFits one (by omega),wordFits one (by omega)⟩⟩

theorem steps_exec (bins : ℕ) (need tag : ℕ→ℕ) (out t c : ℕ) (m : Memory w)
    (needBelow : ∀i,need i < out) (tagBelow : ∀i,tag i < out)
    (room : base out (t+c)+2 < 2^w) :
    (steps w bins need tag out t c).Exec m (history bins need tag out t c m) (c*168+4) := by
  induction c generalizing t m with
  | zero =>
    have empty : ProtocolRAM.image (base out t) 0 (.lit 0) m=m := fillSegment_zero _ _ _
    have bound : base out t+0 < 2^w := by simp only [Nat.add_zero] at room ⊢; omega
    have run : (scan w (base out t) 0 (.lit 0)).Exec m (ProtocolRAM.image (base out t) 0 (.lit 0) m) 4 :=
      @scan_exec w (base out t) 0 (.lit 0) m trivial bound
    rw [empty] at run
    simp only [steps,history,Nat.zero_mul,Nat.zero_add]
    exact @run
  | succ c ih =>
    have early : base out (t+1)+2 < 2^w := by dsimp [base] at *;omega
    let mid := ProtocolRAM.image (base out (t+1)) 2 (column bins need tag out t) m
    have first : (scan w (base out (t+1)) 2 (column bins need tag out t)).Exec m mid 168 := by
      have clock : 4+2*(2*(column bins need tag out t).work+4)=168 := by
        rw [column,term_work]
      rw [← clock]
      exact @scan_exec w (base out (t+1)) 2 (column bins need tag out t) m
        (step_fit bins (by omega) (needBelow t) (tagBelow t)) early
    have shift : t+1+c=t+(c+1) := by omega
    have tail : (steps w bins need tag out (t+1) c).Exec mid (history bins need tag out (t+1) c mid)
        (c*168+4) := ih (t+1) mid (by rw [shift]; exact room)
    have clock : (c+1)*168+4=168+(c*168+4) := by omega
    rw [steps,history,clock]
    exact @Procedure.Exec.then w _ _ m mid _ 168 (c*168+4) first tail


theorem exec (bins : ℕ) (need tag : ℕ→ℕ) (out count : ℕ) (m : Memory w)
    (needBelow : ∀i,need i < out) (tagBelow : ∀i,tag i < out)
    (room : base out count+2 < 2^w) :
    (program w bins need tag out count).Exec m (after bins need tag out count m) (count*168+20) := by
  let init := ProtocolRAM.image out 2 (.lit 0) m
  have begin_ : (scan w out 2 (.lit 0)).Exec m init 16 :=
    @scan_exec w out 2 (.lit 0) m trivial (by dsimp [base] at room; omega)
  have end_ : (steps w bins need tag out 0 count).Exec init (history bins need tag out 0 count init)
      (count*168+4) := steps_exec bins need tag out 0 count init needBelow tagBelow (by simpa using room)
  have clock : count*168+20=16+(count*168+4) := by omega
  rw [clock]
  exact @Procedure.Exec.then w _ _ m init _ 16 (count*168+4) begin_ end_

theorem frame (bins : ℕ) (need tag : ℕ→ℕ) (out t c : ℕ) (m : Memory w) (x : ℕ)
    (early : x < base out (t+1)) : history bins need tag out t c m x=m x := by
  induction c generalizing t m with
  | zero => simp only [history]
  | succ c ih =>
    rw [history]
    exact (ih (t+1) _ (by rw [base_succ out (t+1)];omega)).trans
      (ProtocolRAMGeneratedWrite.frame_image (base out (t+1)) 2 (column bins need tag out t) m x (.inl early))

def mass (m : Memory w) (need : ℕ→ℕ) (t : ℕ) := (m (need t)).val
def matched (bins : ℕ) (m : Memory w) (need tag : ℕ→ℕ) (t : ℕ) :=
  if (m (tag t)).val < bins then mass m need t else 0

private theorem next_words (bins need tag out t : ℕ) (m : Memory w)
    (count : bins < 2^w) (wide : 1 < 2^w) :
    let dst := base out (t+1)
    let o := ProtocolRAM.image dst 2 (term bins need tag out t) m
    o dst=m (base out t)+(if (m tag).val < bins then m need else 0) ∧
      o (dst+1)=m (base out t+1)+m need := by
  constructor
  · simpa [term,Expr.eval,Comparison.test,Fin.lt_def,Fin.val_cast_of_lt count] using
      ProtocolRAMGeneratedWrite.read_image (base out (t+1)) 2 (term bins need tag out t) m (0:Fin 2)
  · have diff : (1:Word w)≠0 := by
      intro e
      have hit := congrArg Fin.val e
      simp [Nat.mod_eq_of_lt wide] at hit
    simpa [term,Expr.eval,Comparison.test,diff] using
      ProtocolRAMGeneratedWrite.read_image (base out (t+1)) 2 (term bins need tag out t) m (1:Fin 2)

/-- The stored offsets add the exact measured quantities of the preceding whole
items, counting every incoming item on the thin side and only accepted ones in
the replacement-pair output. Addition is in the target word ring. -/
theorem reads (bins : ℕ) (need tag : ℕ→ℕ) (out t c : ℕ) (m : Memory w)
    (needBelow : ∀i,need i < out) (tagBelow : ∀i,tag i < out)
    (count : bins < 2^w) (wide : 1 < 2^w) (j : ℕ) (hj : j≤c) :
    let o := history bins need tag out t c m
    o (base out (t+j))=m (base out t)+(∑i : Fin j,matched bins m need tag (t+i.val):ℕ) ∧
    o (base out (t+j)+1)=m (base out t+1)+(∑i : Fin j,mass m need (t+i.val):ℕ) := by
  induction c generalizing t m j with
  | zero =>
    have : j=0 := by omega
    simp [this,history]
  | succ c ih =>
    cases j with
    | zero =>
      have a := frame bins need tag out t (c+1) m (base out t) (by rw [base_succ];omega)
      have b := frame bins need tag out t (c+1) m (base out t+1) (by rw [base_succ];omega)
      simpa using And.intro a b
    | succ j =>
      let m₁ := ProtocolRAM.image (base out (t+1)) 2 (column bins need tag out t) m
      have kept (a : ℕ) (ha : a < out) : m₁ a=m a :=
        ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (by dsimp [base];omega))
      have ma (i : ℕ) : mass m₁ need i=mass m need i := by simp [mass,kept _ (needBelow i)]
      have me (i : ℕ) : matched bins m₁ need tag i=matched bins m need tag i := by
        simp only [matched,ma,kept _ (tagBelow i)]
      have next := ih (t+1) m₁ j (by omega)
      have cur := next_words bins (need t) (tag t) out t m count wide
      have ae : m₁ (base out (t+1))=m (base out t)+(matched bins m need tag t:Word w) := by
        dsimp only [matched,mass]
        split <;> simp_all [m₁,column,Fin.cast_val_eq_self]
      have be : m₁ (base out (t+1)+1)=m (base out t+1)+(mass m need t:Word w) := by
        simpa [m₁,column,mass,Fin.cast_val_eq_self] using cur.2
      simp only [me,ma,ae,be] at next
      simpa [history,Fin.sum_univ_succ,Nat.cast_add,add_assoc,Nat.add_left_comm,Nat.add_comm,m₁] using next

/-- The public zero seed and immutable first-fit input give exclusive prefix
sums without any prepared counters. -/
theorem issued (bins : ℕ) (need tag : ℕ→ℕ) (out c : ℕ) (m : Memory w)
    (needBelow : ∀i,need i < out) (tagBelow : ∀i,tag i < out)
    (count : bins < 2^w) (wide : 1 < 2^w) (j : ℕ) (hj : j≤c) :
    let o := after bins need tag out c m
    o (base out j)=(∑i : Fin j,matched bins m need tag i.val:ℕ) ∧
      o (base out j+1)=(∑i : Fin j,mass m need i.val:ℕ) := by
  let init := ProtocolRAM.image out 2 (.lit 0) m
  have zero : init out=0 := by simpa [init,Expr.eval] using ProtocolRAMGeneratedWrite.read_image out 2 (.lit 0) m (0:Fin 2)
  have one : init (out+1)=0 := by simpa [init,Expr.eval] using ProtocolRAMGeneratedWrite.read_image out 2 (.lit 0) m (1:Fin 2)
  have keep (a : ℕ) (h : a < out) : init a=m a := ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl h)
  have ma (i : ℕ) : mass init need i=mass m need i := by simp [mass,keep _ (needBelow i)]
  have me (i : ℕ) : matched bins init need tag i=matched bins m need tag i := by simp only [matched,keep _ (tagBelow i),ma]
  have proof := reads bins need tag out 0 c init needBelow tagBelow count wide j hj
  change history bins need tag out 0 c init (base out j) = _ ∧
    history bins need tag out 0 c init (base out j+1) = _
  simpa only [Nat.zero_add,base,Nat.mul_zero,Nat.add_zero,zero,one,zero_add,me,ma] using proof

theorem issued_frame (bins : ℕ) (need tag : ℕ→ℕ) (out c : ℕ) (m : Memory w) (x : ℕ) (low : x < out) :
    after bins need tag out c m x=m x :=
  (frame bins need tag out 0 c _ x (by dsimp [base];omega)).trans
    (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl low))

end Hierarchy.DescentPacking.PairRAM.Prefix

end OAI
