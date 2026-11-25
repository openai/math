import OAI.Hierarchy.DescentGLRuntime
import OAI.Hierarchy.DescentSelectedMixing

namespace OAI
/-! # Chronological native row recording and publication of the invertible mixing map -/

namespace Hierarchy.DescentGL.PhysicalTrajectory
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentIntegerScale DescentWalshTables RowStageRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w : ℕ}

def pointer (k base t : ℕ) := (placed k base t).row

def outputBase (k base : ℕ) := (placed k base k).data

/-- At stage t the score builder sees exactly depths t+1 through k of the one
shared weight table. Its prefix pointers address words written by earlier stages. -/
def cpu (w k base : ℕ) (bank : ℕ→ℕ) (t : ℕ) :=
  RowStageRAM.program (h:=t) (r:=k-(t+1)) w (placed k base t)
    (fun i=>pointer k base i.val) (fun j=>bank (t+1+j.val))

def update (k base : ℕ) (bank : ℕ→ℕ) (t : ℕ) (m : Memory w) :=
  RowStageRAM.after (h:=t) (r:=k-(t+1)) (placed k base t)
    (fun i=>pointer k base i.val) (fun j=>bank (t+1+j.val)) m

def charge (k base : ℕ) (bank : ℕ→ℕ) (t : ℕ) :=
  RowStageRAM.ticks (h:=t) (r:=k-(t+1)) (placed k base t)
    (fun i=>pointer k base i.val) (fun j=>bank (t+1+j.val))

def rowProgram (w k base : ℕ) (bank : ℕ→ℕ) : ℕ → Procedure w
  | 0 => scan w base (2^k) (SpanRAM.zero k)
  | t+1 => (rowProgram w k base bank t).seq (cpu w k base bank t)

def result (k base : ℕ) (bank : ℕ→ℕ) (m : Memory w) : ℕ → Memory w
  | 0 => ProtocolRAM.image base (2^k) (SpanRAM.zero k) m
  | t+1 => update k base bank t (result k base bank m t)

def time (k base : ℕ) (bank : ℕ→ℕ) : ℕ → ℕ
  | 0 => 4+(2^k)*16
  | t+1 => time k base bank t+charge k base bank t

def program (w k base : ℕ) (bank : ℕ→ℕ) :=
  (rowProgram w k base bank k).seq
    (DescentGLPermutationRAM.program w (outputBase k base) (fun i : Fin k=>pointer k base i.val))

def finalMemory (k base : ℕ) (bank : ℕ→ℕ) (m : Memory w) :=
  DescentGLPermutationRAM.after (outputBase k base) (fun i : Fin k=>pointer k base i.val) (result k base bank m k)

/-- The caller supplies only the original mounted depth-weight columns and the
single end of the allocated arena. All intermediate addresses are determined. -/
structure Room (w k base : ℕ) (bank : ℕ→ℕ) : Prop where
  tables : ∀ j : Fin (k+1), bank j.val+2^k≤base
  last : outputBase k base+2^k<2^w

private theorem earlier {k base i t : ℕ} (lt : i<t) :
    pointer k base i < (placed k base t).mask := by
  have leq := Nat.mul_le_mul_right (3*2^k+1) lt
  dsimp [pointer,placed]
  rw [Nat.succ_mul] at leq
  omega

private theorem room_step {w k base : ℕ} {bank : ℕ→ℕ} (space : Room w k base bank)
    {t : ℕ} (lt : t<k) : (placed k base t).Room k w := by
  apply placed_room
  have pay := Nat.mul_le_mul_right (3*2^k+1) lt
  have cap := space.last
  dsimp [outputBase,placed] at cap ⊢
  rw [Nat.succ_mul] at pay
  omega

private theorem mask_le_data (k base t : ℕ) :
    (placed k base t).mask ≤ (placed k base t).data :=
  Nat.le_add_right _ (2^k)

private theorem base_le_data (k base t : ℕ) : base ≤ (placed k base t).data :=
  (Nat.le_add_right base (t*(3*2^k+1))).trans (mask_le_data k base t)

private theorem width {w k base : ℕ} {bank : ℕ→ℕ} (room : Room w k base bank) :
    base+2^k<2^w :=
  (Nat.add_le_add_right (base_le_data k base k) (2^k)).trans_lt room.last

theorem prefix_exec {w k base : ℕ} (bank : ℕ→ℕ) (m : Memory w) (space : Room w k base bank)
    (t : ℕ) (ht : t≤k) : (rowProgram w k base bank t).Exec m (result k base bank m t) (time k base bank t) := by
  induction t with
  | zero => exact SpanRAM.zero_exec base m (width space)
  | succ t ih =>
    obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le ht
    let k := t+1+r
    let shelf := placed k base t
    let mem := result k base bank m t
    let step (d : ℕ) : Prop :=
      let ptr := fun i : Fin (t+1+d) => pointer k base i.val
      let banks := fun j : Fin (d+1) => bank (t+1+j.val)
      (RowStageRAM.program (h:=t) (r:=d) w shelf ptr banks).Exec mem
        (RowStageRAM.after (h:=t) (r:=d) shelf ptr banks mem)
        (RowStageRAM.ticks (h:=t) (r:=d) shelf ptr banks)
    have before := room_step space (show t<k by dsimp [k]; omega)
    have inputs (j : Fin (r+1)) : (Bank.mk (bank (t+1+j.val)) k).Fits w shelf.data := by
      have raw := space.tables (Fin.natAdd (t+1) j)
      change bank (t+1+j.val)+2^k≤base at raw
      exact ⟨Nat.two_pow_pos _, (Nat.le_add_left (2^k) base).trans_lt (width space),
        raw.trans (base_le_data k base t)⟩
    have run : step r := RowStageRAM.execute (h:=t) (r:=r) shelf
      (fun i => pointer k base i.val) (fun j => bank (t+1+j.val)) mem before
      (fun i => (earlier (base:=base) (k:=k) i.isLt).trans_le (mask_le_data k base t)) inputs
    have actual : step (k-(t+1)) := (congrArg step (Nat.add_sub_cancel_left (t+1) r)).mpr run
    have prefixRun : (rowProgram w k base bank t).Exec m mem (time k base bank t) :=
      ih (by omega)
    exact @Procedure.Exec.then w (rowProgram w k base bank t) (cpu w k base bank t)
      m mem (update k base bank t mem) (time k base bank t) (charge k base bank t)
      (@prefixRun) (@actual)

structure Recorded {k : ℕ} (base : ℕ) (L : Layout k) (t : ℕ) (ht : t≤k)
    (raw m : Memory w) : Prop where
  old : ∀ x<base,m x=raw x
  rows : ∀a : Fin t,m (pointer k base a.val)=((rowIndex k (rowFunctional L (a.castLE ht))).val:Word w)
  mask : SpanRAM.bitmap (placed k base t).mask (fun a : Fin t=>rowFunctional L (a.castLE ht)) m

private theorem index_functional {k : ℕ} (L T : Layout k) (j : Fin k)
    (same : layoutRow L j.val=layoutRow T j.val) : rowFunctional L j=rowFunctional T j := by
  apply LinearMap.ext
  intro x
  simpa [rowFunctional_apply,layoutRow,j.isLt] using congrFun same x

private theorem stage_record {h r w base q B : ℕ} (bank : ℕ→ℕ)
    (W : Fin ((h+1+r)+1)→Bits (h+1+r)→ℕ) (L T : Layout (h+1+r)) (m raw : Memory w)
    (room : Room w (h+1+r) base bank) (hQ : 0<q) (scale : 3*(h+1+r)+B+2≤w)
    (caps : ∀j d,W j d≤2^B) (weights : ∀ j (x : Fin (2^(h+1+r))),
      raw (bank j.val+x.val)=(W j (DescentGLScoreRAM.vec x):Word w))
    (prev : Recorded base L h (by omega) raw m)
    (agree : ∀j<h, layoutRow T j=layoutRow L j)
    (selected : rowFunctional T ⟨h,by omega⟩=(rowIndex _).symm (chosenIndex (show h<h+1+r by omega) L
      (collisionRowData ⟨h,by omega⟩ (fun j d=>(W j d.val:ℝ)/(q:ℝ)^2) L).2)) :
    Recorded base T (h+1) (by omega) raw (update (h+1+r) base bank h m) := by
  let k := h+1+r
  let s := placed k base h
  let ptr := fun i : Fin k=>pointer k base i.val
  let banks := fun j : Fin (r+1)=>bank (h+1+j.val)
  let vals := fun j : Fin (r+1)=>W (Fin.natAdd (h+1) j)
  let out := RowStageRAM.after s ptr banks m
  have emitted : update (h+1+r) base bank h m=out := by
    let afterAt (d : ℕ) := RowStageRAM.after (h:=h) (r:=d) s
      (fun i => pointer k base i.val) (fun j => bank (h+1+j.val)) m
    change afterAt (k-(h+1)) = afterAt r
    exact congrArg afterAt (Nat.add_sub_cancel_left (h+1) r)
  rw [emitted]
  have fits := room_step room (show h<k by dsimp [k];omega)
  have rawLoads (j : Fin (r+1)) (z : Fin (2^k)) : m (banks j+z.val)=(vals j (DescentGLScoreRAM.vec z):Word w) := by
    have loc := room.tables (Fin.natAdd (h+1) j)
    have hi := z.isLt
    change banks j+2^k≤base at loc
    exact (prev.old _ (by omega)).trans (weights (Fin.natAdd (h+1) j) z)
  have chosen := RowStageRAM.publish s ptr banks m fits L vals hQ prev.mask prev.rows rawLoads (fun i=>by
    let kept := surviving L ((rowIndex _).symm i)
    have card : kept.card≤2^k := by simpa only [card_bits] using kept.card_le_univ
    have bound := rowNumerator_bound r k B vals kept card (fun j d=>caps _ _)
    calc
      2*rowNumerator r vals kept < 2*2^(k+2*r+B+1) := Nat.mul_lt_mul_of_pos_left bound (by decide)
      _ = 2^(k+2*r+B+2) := (pow_succ' (2:ℕ) (k+2*r+B+1)).symm
      _ ≤ 2^w := Nat.pow_le_pow_right (by decide) (by dsimp [k];omega))
  rw [collisionRowData_snd] at selected
  have picked : out s.row = ((rowIndex k (rowFunctional T ⟨h,by dsimp [k];omega⟩)).val:Word w) := by
    rw [selected,Equiv.apply_symm_apply]
    exact chosen.1
  have matched (i : Fin h) : rowFunctional T (i.castLE (show h≤k by dsimp [k];omega))=
      rowFunctional L (i.castLE (show h≤k by dsimp [k];omega)) :=
    index_functional _ _ _ (agree i.val i.isLt)
  have previous (x : ℕ) (lo : x<s.data) : out x=m x :=
    RowStageRAM.old_word s ptr banks m fits x lo
  refine ⟨fun x lo=>(previous x (lo.trans_le (base_le_data k base h))).trans (prev.old x lo),?_,?_⟩
  · intro i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · exact picked
    · exact (previous _ ((earlier (base:=base) (k:=k) j.isLt).trans_le (mask_le_data k base h))).trans
        ((prev.rows j).trans (congrArg (fun f=>(↑(rowIndex k f).val:Word w)) (matched j).symm))
  · rw [placed_next]
    convert chosen.2 using 1
    funext i
    refine Fin.lastCases ?_ (fun j=>?_) i
    · have lastIdx : (Fin.last h).castLE (show h+1≤k by dsimp [k]; omega) =
          (⟨h, by dsimp [k]; omega⟩ : Fin k) := Fin.ext rfl
      simpa only [Fin.snoc_last, lastIdx, vals] using selected
    · have oldIdx : j.castSucc.castLE (show h+1≤k by dsimp [k]; omega) =
          j.castLE (show h≤k by dsimp [k]; omega) := Fin.ext rfl
      simpa only [Fin.snoc_castSucc, oldIdx] using matched j

def Weights {k : ℕ} (W : Fin (k+1)→Bits k→ℕ) (q : ℕ) (j : Fin (k+1)) (d : Nonzero k) : ℝ :=
  (W j d.val:ℝ)/(q:ℝ)^2

def Chooses {k : ℕ} (run : ℕ→Layout k) (weights : Fin (k+1)→Nonzero k→ℝ) : Prop :=
  ∀ i : Fin k, (∀ j < i.val, layoutRow (run (i.val+1)) j=layoutRow (run i.val) j) ∧
    rowFunctional (run (i.val+1)) i=(rowIndex k).symm
      (chosenIndex i.isLt (run i.val) (collisionRowData i weights (run i.val)).2)

theorem recorded {k base q B : ℕ} (bank : ℕ→ℕ) (W : Fin (k+1)→Bits k→ℕ)
    (run : ℕ→Layout k) (chooses : Chooses run (Weights W q)) (m : Memory w)
    (room : Room w k base bank) (hQ : 0<q) (scale : 3*k+B+2≤w) (cap : ∀j d,W j d≤2^B)
    (loads : ∀ j (x : Fin (2^k)),m (bank j.val+x.val)=(W j (DescentGLScoreRAM.vec x):Word w))
    (t : ℕ) (ht : t≤k) : Recorded base (run t) t ht m (result k base bank m t) := by
  induction t with
  | zero =>
    refine ⟨fun x lo=>SpanRAM.frame _ _ _ m x (.inl lo),(fun a => a.elim0),?_⟩
    have empty : (fun a : Fin 0=>rowFunctional (run 0) (a.castLE ht))=(Fin.elim0 : Fin 0→Row k) := by
      funext a; exact a.elim0
    rw [empty]
    simpa [placed,result] using SpanRAM.zero_bitmap base m (show 2^k≤2^w by have := width room;omega)
  | succ t ih =>
    have prev := ih (show t≤k by omega)
    obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le ht
    have tick := chooses (⟨t,by omega⟩ : Fin (t+1+r))
    exact stage_record bank W (run t) (run (t+1)) (result _ base bank m t) m room hQ scale cap loads
      prev tick.1 tick.2

theorem exec {k base : ℕ} (bank : ℕ→ℕ) (m : Memory w) (room : Room w k base bank) :
    (program w k base bank).Exec m (finalMemory k base bank m)
      (time k base bank k+DescentGLPermutationRAM.clock k) := by
  apply Procedure.Exec.then (prefix_exec bank m room k le_rfl)
  apply DescentGLPermutationRAM.run _ _ _ room.last
  intro i
  exact (earlier (base:=base) (k:=k) i.isLt).trans_le (mask_le_data k base k)

theorem receipt {k base q B : ℕ} (bank : ℕ→ℕ) (W : Fin (k+1)→Bits k→ℕ)
    (run : ℕ→Layout k) (chooses : Chooses run (Weights W q)) (m : Memory w)
    (room : Room w k base bank) (hQ : 0<q) (scale : 3*k+B+2≤w) (cap : ∀j d,W j d≤2^B)
    (loads : ∀ j (x : Fin (2^k)),m (bank j.val+x.val)=(W j (DescentGLScoreRAM.vec x):Word w)) :
    let out := finalMemory k base bank m
    (∀i : Fin k,out (pointer k base i.val) =
      ((rowIndex k (rowFunctional (run k) i)).val:Word w)) ∧
    (∀x : Fin (2^k),out (outputBase k base+x.val)=
      ((finFunctionFinEquiv ((run k) (finFunctionFinEquiv.symm x))).val:Word w)) ∧
    ∀x<base,out x=m x := by
  have state := recorded bank W run chooses m room hQ scale cap loads k le_rfl
  let ptr := fun i : Fin k=>pointer k base i.val
  have stored : DescentGLPermutationRAM.stored ptr (result k base bank m k) (run k) :=
    fun i=>state.rows i
  have kept (x : ℕ) (before : x<outputBase k base) :
      finalMemory k base bank m x=result k base bank m k x :=
    DescentGLPermutationRAM.frame _ ptr _ x (.inl before)
  refine ⟨fun i=> (kept _ ((earlier (base:=base) (k:=k) i.isLt).trans_le (mask_le_data k base k))).trans
    (stored i),?_,fun x before=>(kept x (before.trans_le (base_le_data k base k))).trans (state.old x before)⟩
  exact DescentGLPermutationRAM.read _ ptr _ (run k) stored (show 2^k≤2^w by have := width room;omega)

/-- The very same physical procedure realizes the selected GL completion and its
sub-average conditional cost on the mounted weight columns. -/
theorem mixing {k base q B : ℕ} (bank : ℕ→ℕ) (W : Fin (k+1)→Bits k→ℕ)
    (initial : Layout k) (m : Memory w) (room : Room w k base bank) (hQ : 0<q)
    (scale : 3*k+B+2≤w) (cap : ∀j d,W j d≤2^B)
    (loads : ∀ j (x : Fin (2^k)),m (bank j.val+x.val)=(W j (DescentGLScoreRAM.vec x):Word w)) :
    let out := finalMemory k base bank m
    let f := allDepthCollisionCost (Weights W q)
    (program w k base bank).Exec m out (time k base bank k+DescentGLPermutationRAM.clock k) ∧
    ∃ μ : Layout k, f μ ≤ (∑L,f L)/Fintype.card (Layout k) ∧
      (∀i : Fin k,out (pointer k base i.val)=((rowIndex k (rowFunctional μ i)).val:Word w)) ∧
      (∀x : Fin (2^k),out (outputBase k base+x.val)=
        ((finFunctionFinEquiv (μ (finFunctionFinEquiv.symm x))).val:Word w)) ∧ ∀x<base,out x=m x := by
  obtain ⟨run,_,steps,bound⟩ := chosenRow_collisionTrajectory initial (Weights W q)
  exact ⟨exec bank m room,run k,bound,receipt bank W run (fun i=>⟨(steps i).1,(steps i).2.1⟩)
    m room hQ scale cap loads⟩

theorem time_le (k base : ℕ) (bank : ℕ→ℕ) (t : ℕ) (ht : t≤k) :
    time k base bank t ≤ 4+2^k*16+t*perRow k := by
  induction t with
  | zero => simp [time]
  | succ t ih =>
    have before := ih (show t≤k by omega)
    have one : charge k base bank t ≤ perRow k := by
      obtain ⟨r,rfl⟩ := Nat.exists_eq_add_of_le ht
      let k := t+1+r
      let clockAt (d : ℕ) := RowStageRAM.ticks (h:=t) (r:=d) (placed k base t)
        (fun i => pointer k base i.val) (fun j => bank (t+1+j.val))
      have measured : clockAt r ≤ perRow k := ticks_le (h:=t) (r:=r) (placed k base t)
        (fun i => pointer k base i.val) (fun j => bank (t+1+j.val))
      exact (congrArg clockAt (Nat.add_sub_cancel_left (t+1) r)).trans_le measured
    simp only [time,Nat.succ_mul]
    omega

theorem total_clock (k base : ℕ) (bank : ℕ→ℕ) :
    time k base bank k+DescentGLPermutationRAM.clock k ≤
      4+2^k*16+k*(3200*(k+1)*2^(3*k))+DescentGLPermutationRAM.clock k := by
  have sum := time_le k base bank k le_rfl
  have step := Nat.mul_le_mul_left k (perRow_le k)
  omega

end
end Hierarchy.DescentGL.PhysicalTrajectory

end OAI
