import OAI.Computability.MultitapeWeakETH.PhysicalBlocks
import OAI.Computability.MultitapeWeakETH.Epoch

/-! # Interpreting an epoch table on physical tape configurations -/

namespace OAI.Computability.MultitapeWeakETH.PhysicalBlocks

open IntegerMultiplication
open scoped Classical
noncomputable section
variable {M : Machine}

def config : Phase M → Config M
  | .running c | .halted c => c

def stopped : Phase M → Bool
  | .running _ => false
  | .halted _ => true

/-- Execute a segment starting in either phase. Its final halt test can freeze
the machine, leaving all heads and cells fixed for the remainder. -/
def segment (coins : ℕ → M.Choice) (start : ℕ) (p : Phase M) : ℕ → Phase M
  | 0 => p
  | t+1 => freezeStep M (coins (start+t)) (segment coins start p t)

theorem frozenRun_segment (coins : ℕ → M.Choice) (init : Config M) (start t : ℕ) :
    segment coins start (frozenRun M coins init start) t = frozenRun M coins init (start+t) := by
  induction t with
  | zero => simp [segment]
  | succ t ih => simp [segment,ih,frozenRun]

theorem freeze_motion (p : Phase M) (choice : M.Choice) (i : M.Tapes) :
    |((config (freezeStep M choice p)).tape i).pos - ((config p).tape i).pos| ≤ 1 := by
  cases p with
  | halted _ => simp [freezeStep,config]
  | running c =>
    cases h : TM.advance (M.rule choice) c with
    | none => simp [freezeStep,config,h]
    | some d => simpa [freezeStep,config,h] using head_step _ h i

def Fits {b : ℕ} (base : M.Tapes → ℤ) (p : Phase M) :=
  ∀ i, ((config p).tape i).pos / (b:ℤ) = base i

def region (b : ℕ) (base : M.Tapes → ℤ) (i : M.Tapes) : Set ℤ :=
  {z | some (i,z/(b:ℤ)) ∈ epochKeys M base}

theorem inside_segment {b : ℕ} (hb : 0 < b) {base : M.Tapes → ℤ} {p : Phase M}
    (fits : Fits (b:=b) base p) (coins : ℕ → M.Choice) (start t : ℕ) (ht : t ≤ b) (i : M.Tapes) :
    ((config (segment coins start p t)).tape i).pos ∈ region b base i := by
  apply mem_epochKeys
  rw [← fits i]
  simpa only [Nat.zero_add,segment] using epoch_blocks hb (fun j => ((config (segment coins start p j)).tape i).pos)
    (fun _ => freeze_motion _ _ _) 0 t ht

structure PhaseAgrees (cells : M.Tapes → Set ℤ) (p q : Phase M) : Prop where
  flag : stopped p = stopped q
  cfg : AgreesOn cells (config p) (config q)

private theorem replay_freeze {cells : M.Tapes → Set ℤ} {p q : Phase M} (choice : M.Choice)
    (agree : PhaseAgrees cells p q) (inside : ∀ i, ((config p).tape i).pos ∈ cells i) :
    PhaseAgrees cells (freezeStep M choice p) (freezeStep M choice q) ∧
      ∀ i z, z ∉ cells i → ((config (freezeStep M choice q)).tape i).absolute z =
        ((config q).tape i).absolute z := by
  cases p <;> cases q
  case running.running a b =>
    have ac : AgreesOn cells a b := agree.cfg
    cases h : TM.advance (M.rule choice) a with
    | none =>
      have ha : M.rule choice a.pc (fun i => (a.tape i).view 0) = none := by
        simpa [TM.advance] using h
      rw [ac.state,ac.same_reads inside] at ha
      have hb : TM.advance (M.rule choice) b = none := by simp [TM.advance,ha]
      exact ⟨by simpa [freezeStep,h,hb] using
        (show PhaseAgrees cells (.halted a) (.halted b) from ⟨rfl,agree.cfg⟩),
        by simp [freezeStep,hb,config]⟩
    | some a' =>
      obtain ⟨b',hb,agree',unchanged⟩ := replay_step _ ac inside h
      simp only [freezeStep,h,hb]
      exact ⟨⟨rfl,agree'⟩,unchanged⟩
  case halted.halted a b => exact ⟨agree,fun _ _ _ => rfl⟩
  all_goals have contra := agree.flag; simp [stopped] at contra

theorem replay_segment {b : ℕ} (hb : 0 < b) {base : M.Tapes → ℤ} {p q : Phase M}
    (fits : Fits (b:=b) base p) (coins : ℕ → M.Choice) (start length : ℕ) (length_le : length ≤ b)
    (agree : PhaseAgrees (region b base) p q) :
    PhaseAgrees (region b base) (segment coins start p length) (segment coins start q length) ∧
      ∀ i z, z ∉ region b base i → ((config (segment coins start q length)).tape i).absolute z =
        ((config q).tape i).absolute z := by
  induction length with
  | zero => exact ⟨agree,fun _ _ _ => rfl⟩
  | succ t ih =>
    have le : t ≤ b := by omega
    obtain ⟨atT,outside⟩ := ih le
    obtain ⟨step,same⟩ := replay_freeze (coins (start+t)) atT (inside_segment hb fits coins start t le)
    exact ⟨step,fun i z hz => (same i z hz).trans (outside i z hz)⟩

def offset {b : ℕ} (hb : 0 < b) (z : ℤ) : Fin b :=
  ⟨(z % b).toNat,by
    have pos : (0:ℤ) < b := by omega
    have := Int.emod_nonneg z pos.ne'
    have := Int.emod_lt_of_pos z pos
    omega⟩

private theorem offset_eq {b : ℕ} (hb : 0 < b) (z : ℤ) :
    ((offset hb z).val:ℤ) = z % b :=
  Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))

def store {b : ℕ} (hb : 0 < b) (p : Phase M) : (i : Key M) → Value M b i
  | none => (stopped p,(config p).pc,fun i => offset hb ((config p).tape i).pos)
  | some (i,j) => fun r => ((config p).tape i).absolute (j * b + r.val)

theorem block_offset {b : ℕ} (hb : 0 < b) (z : ℤ) :
    z / b * b + ((offset hb z).val:ℤ) = z := by
  rw [offset_eq,add_comm,Int.emod_add_ediv_mul]

private theorem cell_block {b : ℕ} (hb : 0 < b) (j : ℤ) (r : Fin b) :
    (j*b+r.val)/(b:ℤ) = j := by
  have small : (r.val:ℤ) / b = 0 := Int.ediv_eq_zero_of_lt (by omega) (by omega)
  rw [add_comm,Int.add_mul_ediv_right _ _ (by omega),small,zero_add]

theorem phaseAgrees_of_store {b : ℕ} (hb : 0 < b) {base : M.Tapes → ℤ} {p q : Phase M}
    (hp : Fits (b:=b) base p) (hq : Fits (b:=b) base q)
    (same : ∀ k ∈ epochKeys M base, store hb p k = store hb q k) :
    PhaseAgrees (region b base) p q := by
  have ctrl := same none (Finset.mem_insert_self ..)
  change (stopped p,(config p).pc,fun i => offset hb ((config p).tape i).pos) =
         (stopped q,(config q).pc,fun i => offset hb ((config q).tape i).pos) at ctrl
  obtain ⟨flag,state,offs⟩ := Prod.mk.inj ctrl |>.imp_right Prod.mk.inj
  refine ⟨flag,state,?_,?_⟩
  · intro i
    have pos := congrArg (fun f : M.Tapes → Fin b => ((f i).val:ℤ)) offs
    have a := block_offset hb ((config p).tape i).pos
    have c := block_offset hb ((config q).tape i).pos
    rw [hp i] at a
    rw [hq i] at c
    omega
  · intro i z hz
    have e := congrFun (same (some (i,z/b)) hz) (offset hb z)
    simpa only [store,block_offset] using e

theorem store_of_phaseAgrees {b : ℕ} (hb : 0 < b) {base : M.Tapes → ℤ} {p q : Phase M}
    (agree : PhaseAgrees (region b base) p q) :
    ∀ k ∈ epochKeys M base, store hb p k = store hb q k := by
  rintro (_ | ⟨i,j⟩) hk
  · simp only [store,agree.flag,agree.cfg.state,agree.cfg.heads]; rfl
  · funext r
    apply agree.cfg.contents
    simpa only [region,Set.mem_ofPred_eq,cell_block hb] using hk

/-- Each local epoch table may quantify over a private witness for its run.
This witness can be replayed on the actual tapes, including on halted paths.
All blocks outside the recorded neighborhood are left unchanged. -/
theorem realize_epoch {b : ℕ} (hb : 0 < b) {base finish : M.Tapes → ℤ}
    {witness actual : Phase M} (hw : Fits (b:=b) base witness) (ha : Fits (b:=b) base actual)
    (same : ∀ k ∈ epochKeys M base, store hb witness k = store hb actual k)
    (coins : ℕ → M.Choice) (start len : ℕ) (hl : len ≤ b)
    (hf : Fits (b:=b) finish (segment coins start witness len)) :
    Fits (b:=b) finish (segment coins start actual len) ∧
    (∀ k ∈ epochKeys M base, store hb (segment coins start witness len) k =
      store hb (segment coins start actual len) k) ∧
    ∀ k ∉ epochKeys M base, store hb (segment coins start actual len) k = store hb actual k := by
  obtain ⟨agree,unchanged⟩ := replay_segment hb hw coins start len hl (phaseAgrees_of_store hb hw ha same)
  refine ⟨fun i => ?_,store_of_phaseAgrees hb agree,?_⟩
  · rw [← agree.cfg.heads i,hf i]
  · rintro (_ | ⟨i,j⟩) hk
    · exact (hk (Finset.mem_insert_self ..)).elim
    · funext r
      apply unchanged
      simpa only [region,Set.mem_ofPred_eq,cell_block hb] using hk

end
end OAI.Computability.MultitapeWeakETH.PhysicalBlocks
