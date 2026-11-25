import OAI.Hierarchy.TaggedWideDatedLayout

namespace OAI
/-! # Physical nonoverlap of every earlier written scatter window -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open ProbeStage.CoreBoard.HistoryRoles
open scoped BigOperators Classical
theorem Ordered.append {a b lo mid hi : ℕ} {p : Fin a→Scatter} {q : Fin b→Scatter}
    (lm : lo ≤ mid) (mh : mid ≤ hi) (l : Ordered lo mid p) (r : Ordered mid hi q) :
    Ordered lo hi (Fin.addCases p q) := by
  refine ⟨?_,?_,?_⟩
  · intro i;induction i using Fin.addCases with
    | left i=>simpa using l.lower i
    | right j=>simpa using lm.trans (r.lower j)
  · intro i;induction i using Fin.addCases with
    | left i=> simp only [Fin.addCases_left];exact (l.upper i).trans mh
    | right i=>simpa using r.upper i
  · intro i j hj
    induction i using Fin.addCases with
    | left i=>
      induction j using Fin.addCases with
      | left j=>simpa using l.separate i j (by exact hj)
      | right j=>simpa using (l.upper i).trans (r.lower j)
    | right i=>
      induction j using Fin.addCases with
      | left j=>have h:=j.isLt;change a+i.val < j.val at hj;omega
      | right j=>
        have before:i < j:=by change a+i.val < a+j.val at hj;change i.val < j.val;omega
        simpa using r.separate i j before

theorem Ordered.spaced {n base gap : ℕ} (p : Fin n→Scatter)
    (starts : ∀i,(p i).floor=base+i.val*gap)
    (ends : ∀i,(p i).stop ≤ base+(i.val+1)*gap) : Ordered base (base+n*gap) p := by
  refine ⟨fun i=>by rw [starts];omega,?_,?_⟩
  · intro i
    exact (ends i).trans (Nat.add_le_add_left (Nat.mul_le_mul_right gap i.isLt) base)
  · intro i j before
    rw [starts]
    exact (ends i).trans (Nat.add_le_add_left (Nat.mul_le_mul_right gap before) base)

variable {T : ℕ} (p : Dated T) (rom work : ℕ)

theorem role_order : Ordered work (p.rolesEnd work)
    (fun k : Fin ((T+1)*3) =>
      let pair : Fin (T+1) × Fin 3 := finProdFinEquiv.symm k
      p.rolePage rom work pair.1 pair.2) := by
  rw [show p.rolesEnd work=work+((T+1)*3)*p.roleSpan by simp [Dated.rolesEnd,Nat.mul_assoc]]
  apply Ordered.spaced (gap:=p.roleSpan)
  · intro i
    obtain ⟨⟨j,f⟩,rfl⟩:=finProdFinEquiv.surjective i
    simp only [Equiv.symm_apply_apply]
    simp only [Scatter.floor,Dated.rolePage,Dated.roleStart,DatedRoleSheets.sheet,DatedRoleSheets.sink,
      Dated.roleSpan,finProdFinEquiv_apply_val,Nat.add_sub_cancel]
    ring
  · intro i
    obtain ⟨⟨j,f⟩,rfl⟩:=finProdFinEquiv.surjective i
    simp only [Equiv.symm_apply_apply]
    simp only [Scatter.stop,Dated.rolePage,Dated.roleStart,DatedRoleSheets.sheet,DatedRoleSheets.sink,
      Dated.roleSpan,DatedRoleSheets.span,finProdFinEquiv_apply_val]
    apply le_of_eq
    ring

theorem party_order (shape : Fin T→Shape) (base : ℕ) (window : Fin T→Scatter)
    (real : ∀j,(window j).floor=offset base (fun j=>(shape j).span p.sites) j ∧
      (window j).stop=offset base (fun j=>(shape j).span p.sites) j+(shape j).span p.sites) :
    Ordered base (endOf base (fun j=>(shape j).span p.sites)) window := by
  apply Ordered.spaced (gap:=stride (fun j=>(shape j).span p.sites))
  · exact fun i=>(real i).1
  · intro i
    rw [(real i).2,Nat.add_mul,one_mul]
    dsimp [offset]
    have sub : (shape i).span p.sites ≤ stride (fun j=>(shape j).span p.sites) :=
      Finset.single_le_sum (f:=fun j=>(shape j).span p.sites) (fun _ _=>Nat.zero_le _) (Finset.mem_univ i)
    omega


/-- The original emitted width and the two physically distinct endpoint
socket scans are the final three scatter pages. -/
theorem last_pair_order : Ordered (p.maskStart work) (p.slotBase work true-1)
    (Fin.cases (p.widthPage rom work) (fun _ : Fin 1=>p.slotPage work false)) := by
  have widthFloor : (p.widthPage rom work).floor = p.maskStart work := by
    simp [Scatter.floor, Dated.widthPage]
  have widthStop : (p.widthPage rom work).stop = p.slotStart work := rfl
  have slotFloor : (p.slotPage work false).floor = p.slotStart work := by
    simp [Scatter.floor, Dated.slotPage, Dated.slotBase]
  have slotStop : (p.slotPage work false).stop = p.slotBase work true - 1 := by
    simp [Scatter.stop, Dated.slotPage, Dated.slotBase]; omega
  have orderedStart : p.maskStart work ≤ p.slotStart work := by
    simp [Dated.slotStart]; omega
  have orderedEnd : p.slotStart work ≤ p.slotBase work true - 1 := by
    simp [Dated.slotBase]
  constructor
  · intro i
    induction i using Fin.cases with
    | zero => simp only [Fin.cases_zero, widthFloor, le_refl]
    | succ i => simpa only [Fin.cases_succ, slotFloor] using orderedStart
  · intro i
    induction i using Fin.cases with
    | zero => simpa only [Fin.cases_zero, widthStop] using orderedEnd
    | succ i => simp only [Fin.cases_succ, slotStop, le_refl]
  · intro i j before
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact (lt_irrefl _ before).elim
      | succ j => simp only [Fin.cases_zero, Fin.cases_succ, widthStop, slotFloor, le_refl]
    | succ i =>
      have one : i.succ.val = 1 := by rw [Subsingleton.elim i 0]; rfl
      have bound := j.isLt
      change i.succ.val < j.val at before
      omega

/-- All original date writes occupy disjoint ascending intervals, including
empty ballot pages and the signed width/port emitters. -/
theorem Dated.ordered : Ordered work (p.workEnd work) (p.sheets rom work) := by
  have ballot : Ordered (p.rolesEnd work) (p.controlStart work) (p.ballotPage rom work) := by
    apply party_order p p.ballot (p.rolesEnd work)
    intro j
    simp [Scatter.floor,Scatter.stop,Dated.ballotPage,Dated.ballotStart,Shape.sheet,Shape.span,Nat.add_assoc]
  have ctrl : Ordered (p.controlStart work) (p.maskStart work) (p.controlPage rom work) := by
    apply party_order p p.control (p.controlStart work)
    intro j
    simp [Scatter.floor,Scatter.stop,Dated.controlPage,Dated.controlBase,Shape.sheet,Shape.span,Nat.add_assoc]
  have bc : p.rolesEnd work≤p.controlStart work:=Nat.le_add_right ..
  have cm : p.controlStart work≤p.maskStart work:=Nat.le_add_right ..
  have wr : work≤p.rolesEnd work:=Nat.le_add_right ..
  have ms : p.maskStart work≤p.slotBase work true-1:=by
    simp [Dated.slotBase,Dated.slotStart]; omega
  have se : p.slotBase work true-1≤p.workEnd work:=by
    simp [Dated.slotBase,Dated.workEnd]
  have last : Ordered (p.slotBase work true-1) (p.workEnd work) (fun _ : Fin 1=>p.slotPage work true) := by
    constructor
    · intro _;exact le_rfl
    · intro _;simp [Scatter.stop,Dated.slotPage,Dated.slotBase,Dated.workEnd]; omega
    · intro i j hij;fin_cases i;fin_cases j;omega
  exact Ordered.append (((wr.trans bc).trans cm).trans ms) se
    (Ordered.append ((wr.trans bc).trans cm) ms
       (Ordered.append wr (bc.trans cm) (role_order p rom work) (Ordered.append bc cm ballot ctrl))
       (last_pair_order p rom work)) last

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end
end OAI
