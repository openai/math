import OAI.Hierarchy.DescentLiteralTable
import OAI.Hierarchy.DescentTerminalProfileCodes
import OAI.Hierarchy.ProtocolRAMSumScoresCheap
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Native validation of every used and unused selector row and the cumulative rejection bit -/
namespace Hierarchy.DescentTerminalEpochFlags
open DescentSixParty ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {w n C : ℕ}

/-- The same profile field key used for new gadget histories. The static ROM is shared. -/
def invalid (C x : ℕ) : ℕ := if (decode C x).isSome then 0 else 1

def romMemory (C : ℕ) (rom : Bank) (m : Memory w) : Memory w :=
  fillSegment rom.base (alphabet C) (fun a => (invalid C (a-rom.base) : Word w)) m

def HasROM (C : ℕ) (rom : Bank) (m : Memory w) : Prop :=
  ∀i < alphabet C,m (rom.base+i)=(invalid C i : Word w)

theorem rom_read (C : ℕ) (rom : Bank) (m : Memory w) : HasROM C rom (romMemory C rom m) := by
  intro i hi
  simp [romMemory,fillSegment,show rom.base ≤ rom.base+i ∧ rom.base+i < rom.base+alphabet C by omega]

theorem rom_frame (C : ℕ) (rom : Bank) (m : Memory w) {a : ℕ}
    (other : a < rom.base ∨ rom.base+alphabet C ≤ a) : romMemory C rom m a=m a := by
  simp [romMemory,fillSegment,show ¬(rom.base ≤ a ∧ a < rom.base+alphabet C) by omega]

def scalar (a : ℕ) : Expr := .lookup ⟨a,0⟩ (.lit 0)
private theorem scalar_read (a : ℕ) (m : Memory w) (i : Word w) :
    (scalar a).eval m i=m a := by simp [scalar,Expr.eval,Bank.read,Bank.size]

def seatExpr (C count : ℕ) (codes rom : Bank) : Expr :=
  let raw := Expr.lookup codes .row
  .branch .lt .row (scalar count)
    (.branch .lt raw (.lit (alphabet C)) (.lookup rom raw) (.lit 1))
    (.branch .eq raw (.lit 0) (.lit 0) (.lit 1))

def scores (C count : ℕ) (codes : Bank) (m : Memory w) (i : Fin n) : ℕ :=
  if SeatValid C (m count).val (m (codes.base+i.val)).val i.val then 0 else 1

private theorem bank_read (b : Bank) (m : Memory w) (i : Word w)
    (small : i.val < b.size) : b.read m i=m (b.base+i.val) := by
  simp [Bank.read,Nat.mod_eq_of_lt small]

theorem seat_reads (C count : ℕ) (codes rom : Bank) (m : Memory w) (table : HasROM C rom m)
    (span : n ≤ codes.size) (wide : n < 2^w) (letters : alphabet C ≤ rom.size)
    (fit : alphabet C < 2^w) : SumScores.Reads m (seatExpr C count codes rom) (scores (n:=n) C count codes m) := by
  intro i
  let raw := m (codes.base+i.val)
  have iv : (i.val : Word w).val=i.val := Fin.val_cast_of_lt (i.isLt.trans wide)
  have input : codes.read m (i.val:Word w)=raw := by
    simp [raw,Bank.read,iv,Nat.mod_eq_of_lt (i.isLt.trans_le span)]
  have ab : ((alphabet C:ℕ):Word w).val=alphabet C := Fin.val_cast_of_lt fit
  change (seatExpr C count codes rom).eval m (i.val:Word w) =
    ((if SeatValid C (m count).val raw.val i.val then 0 else 1 : ℕ):Word w)
  have ae : ((i.val:Word w) < m count) ↔ i.val < (m count).val := by
    change (i.val:Word w).val < _ ↔ _
    rw [iv]
  have ce : (raw < (alphabet C:Word w)) ↔ raw.val < alphabet C := by
    change raw.val < (alphabet C:Word w).val ↔ _
    rw [ab]
  have test : (seatExpr C count codes rom).eval m (i.val:Word w) =
      (if i.val < (m count).val then
        if raw.val < alphabet C then rom.read m raw else 1
      else if raw = 0 then 0 else 1) := by
    simp only [seatExpr,Expr.eval,scalar_read,Comparison.test,input,
      Nat.cast_zero,Nat.cast_one,decide_eq_true_eq,beq_iff_eq,ae,ce]
  rw [test]
  by_cases active : i.val < (m count).val
  · by_cases good : raw.val < alphabet C
    · have r := (bank_read rom m raw (good.trans_le letters)).trans (table raw.val good)
      simp [active,good,r,SeatValid,invalid]
    · have bad : decode C raw.val=none := by simp [decode,good]
      simp [active,good,SeatValid,bad]
  · by_cases zero : raw=0
    · simp [active,SeatValid,zero]
    · have val : raw.val≠0 := fun h => zero (Fin.ext h)
      simp [active,SeatValid,zero,val]

def stage (w C count : ℕ) (codes rom : Bank) (n out : ℕ) :=
  SumScores.procedure w out n 1 (seatExpr C count codes rom)

def fee (C count : ℕ) (codes rom : Bank) (n : ℕ) :=
  4+(n+1)*(42+2*(seatExpr C count codes rom).work)

theorem stage_run (C count : ℕ) (codes rom : Bank) (n out : ℕ)
    (hr : rom.Fits w out) (hc : codes.Fits w out) (hn : (Bank.mk count 0).Fits w out)
    (letters : alphabet C ≤ rom.size) (slots : n ≤ codes.size) (room : out+(n+1) < 2^w) :
    (stage w C count codes rom n out).Spec (HasROM C rom)
      (fun m o => (o (out+n)=if ∀i : Fin n,SeatValid C (m count).val (m (codes.base+i.val)).val i.val
        then 0 else 1) ∧ ∀a, a < out ∨ out+n+1 ≤ a → o a=m a) (fee C count codes rom n) ∧
      CheapCode (stage w C count codes rom n out) := by
  refine ⟨?_,@PruneFlag.cheap w out n 1 (seatExpr C count codes rom)⟩
  intro P R V machine pc reg pub exit inst publicWords cfg m entry table
  let sc : Fin n → ℕ := scores C count codes m
  have bill : (∑i,sc i) ≤ n := by
    calc
      _ ≤ ∑_ : Fin n,1 := Finset.sum_le_sum fun i _=>by dsimp [sc,scores]; split <;> decide
      _ = _ := by simp
  have efit : (seatExpr C count codes rom).Fits w out :=
    ⟨trivial,⟨hn,trivial⟩,
      ⟨⟨hc,trivial⟩,trivial,⟨hr,hc,trivial⟩,trivial⟩,
      ⟨⟨hc,trivial⟩,trivial,trivial,trivial⟩⟩
  have bounds : (stage w C count codes rom n out).Spec (fun before=>SumScores.Reads before (seatExpr C count codes rom) sc)
      (fun before after=>after=fillSegment out (n+1) (SumScores.word out 1 sc) before)
      (fee C count codes rom n) := @SumScores.run w n out 1 (seatExpr C count codes rom) sc
        efit room (by omega) (by omega)
  have reads := seat_reads C count codes rom m table slots (by omega) letters (letters.trans_lt hr.2.1)
  obtain ⟨clock,time,state,o,step,done,eq⟩:=bounds machine pc reg pub exit inst publicWords cfg m entry reads
  refine ⟨clock,time,state,o,step,done,?_,?_⟩
  · rw [eq,SumScores.read_flag]
    have char : (∑i,sc i)=0 ↔ ∀i : Fin n,SeatValid C (m count).val (m (codes.base+i.val)).val i.val := by
      rw [Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
      simp [sc,scores]
    by_cases z : (∑i,sc i)=0
    · simp [z,char.mp z]
    · rw [ite_eq_left (show 1 ≤ _ from Nat.pos_of_ne_zero z),ite_eq_right (mt char.mpr z)]
  · intro a outside
    simp [eq,fillSegment,show ¬(out ≤ a ∧ a < out+(n+1)) by omega]

/-- The former cumulative flag can be a nonboolean seed histogram count. -/
def sticky (previous current exterior : ℕ) : Expr :=
  .branch .eq (scalar previous) (.lit 0)
    (.branch .eq (scalar current) (.lit 0)
      (.branch .eq (scalar exterior) (.lit 0) (.lit 0) (.lit 1))
      (.lit 1))
    (.lit 1)

def step (w previous current exterior out : ℕ) := scan w out 1 (sticky previous current exterior)

theorem step_exec (previous current exterior out : ℕ) (m : Memory w)
    (hp : (Bank.mk previous 0).Fits w out) (hc : (Bank.mk current 0).Fits w out)
    (he : (Bank.mk exterior 0).Fits w out) (room : out+1 < 2^w) :
    let o := image out 1 (sticky previous current exterior) m
    (step w previous current exterior out).Exec m o (4+1*(2*(sticky previous current exterior).work+4)) ∧
      CheapCode (step w previous current exterior out) ∧
      o out=(if m previous=0 ∧ m current=0 ∧ m exterior=0 then 0 else 1) ∧
      ∀a, a≠out → o a=m a := by
  have sf : (sticky previous current exterior).Fits w out := by
    exact ⟨⟨hp,trivial⟩,trivial,⟨⟨hc,trivial⟩,trivial,
      ⟨⟨he,trivial⟩,trivial,trivial,trivial⟩,trivial⟩,trivial⟩
  refine ⟨@scan_exec w out 1 (sticky previous current exterior) m sf room,
    @scan_cheap w out 1 (sticky previous current exterior),?_,?_⟩
  · have r := ProtocolRAMGeneratedWrite.read_image out 1 (sticky previous current exterior) m (0:Fin 1)
    by_cases p : m previous=0 <;> by_cases c : m current=0 <;> by_cases e : m exterior=0 <;>
      simpa [sticky,Expr.eval,Comparison.test,scalar_read,p,c,e] using r
  · intro a ne
    exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)

/-- Emit the branch-independent profile validity table once. -/
def install (w C : ℕ) (rom : Bank) :=
  ProtocolRAM.program w (DescentSeedCountCheck.literals rom.base (invalid C) (alphabet C))

theorem installed (C : ℕ) (rom : Bank) (room : rom.base+alphabet C < 2^w) (m : Memory w) :
    (install w C rom).Exec m (romMemory C rom m) (4+10*alphabet C) ∧ CheapCode (install w C rom) := by
  have same : ProtocolRAM.result (DescentSeedCountCheck.literals rom.base (invalid C) (alphabet C)) m =
      romMemory C rom m := by
    funext a
    exact DescentSeedCountCheck.literal_rows rom.base (invalid C) (alphabet C) m a
  refine ⟨?_,@ProtocolRAM.program_cheap w (DescentSeedCountCheck.literals rom.base (invalid C) (alphabet C))⟩
  rw [←same,←DescentSeedCountCheck.literal_time rom.base (invalid C) (alphabet C)]
  exact @ProtocolRAM.program_exec w (DescentSeedCountCheck.literals rom.base (invalid C) (alphabet C)) m
    (DescentSeedCountCheck.literals_fit rom.base (invalid C) (alphabet C) room)

def epochProgram (w C count : ℕ) (codes rom : Bank) (n out previous exterior dst : ℕ) :=
  (stage w C count codes rom n out).seq (step w previous (out+n) exterior dst)

def epochCost (C count : ℕ) (codes rom : Bank) (n out previous exterior : ℕ) :=
  fee C count codes rom n + (4+1*(2*(sticky previous (out+n) exterior).work+4))

theorem epochCost_eq (C count : ℕ) (codes rom : Bank) (n out previous exterior : ℕ) :
    epochCost C count codes rom n out previous exterior = 68+126*(n+1) := by
  change (4+(n+1)*126) + 64 = _
  omega

private theorem spec_from_outputs {A : Procedure w} (result : Memory w → Memory w)
    {post : Memory w → Memory w → Prop} {budget : ℕ}
    (run : ∀ m, A.Exec m (result m) budget ∧ post m (result m)) :
    A.Spec (fun _ => True) post budget := by
  intro pr re publ machine pc reg pub exit inst data cfg m entry _
  obtain ⟨exec,holds⟩ := run m
  obtain ⟨time,cost,st,o,h,finish,eq⟩ := exec machine pc reg pub exit inst data cfg m entry rfl
  exact ⟨time,cost,st,o,h,finish,eq.symm ▸ holds⟩

private theorem seq_true {A B : Procedure w} {pre : Memory w → Prop}
    {left right post : Memory w → Memory w → Prop} {a b : ℕ}
    (first : A.Spec pre left a) (second : B.Spec (fun _ => True) right b)
    (done : ∀ m mid o, left m mid → right mid o → post m o) :
    (A.seq B).Spec pre post (a+b) :=
  @Procedure.Spec.mono w (A.seq B) pre pre (fun m o => ∃ mid, left m mid ∧ right mid o)
    post (a+b) (a+b)
    (@Procedure.Spec.seq w A B pre (fun _ => True) left right a b (@first) (@second)
      (fun _ _ _ => trivial))
    (fun _ h => h) (fun m o ⟨mid,l,r⟩ => done m mid o l r) le_rfl

/-- Scan all seats and update the cumulative bit after the exterior proposal service.
Both previous flags may be any nonzero word. Epochs with no seats also preserve prior failures. -/
theorem epoch_run (C count : ℕ) (codes rom : Bank) (n out previous exterior dst : ℕ)
    (hr : rom.Fits w out) (hc : codes.Fits w out) (hn : (Bank.mk count 0).Fits w out)
    (letters : alphabet C ≤ rom.size) (slots : n ≤ codes.size)
    (earlier : previous < out ∧ exterior < out) (apart : out+n+1 ≤ dst) (room : dst+1 < 2^w) :
    (epochProgram w C count codes rom n out previous exterior dst).Spec (HasROM C rom)
      (fun m o => (o dst = if m previous=0 ∧ m exterior=0 ∧
        ∀i : Fin n,SeatValid C (m count).val (m (codes.base+i.val)).val i.val then 0 else 1) ∧
        ∀a, (a < out ∨ out+n+1 ≤ a) → a≠dst → o a=m a)
      (epochCost C count codes rom n out previous exterior) ∧
    CheapCode (epochProgram w C count codes rom n out previous exterior dst) := by
  have small := show out+(n+1) < 2^w by omega
  obtain ⟨test,cheap⟩ := stage_run C count codes rom n out hr hc hn letters slots small
  have fits (a : ℕ) (ha : a < dst) : (Bank.mk a 0).Fits w dst := by
    change 0 < 1 ∧ 1 < 2^w ∧ a+1 ≤ dst
    omega
  let P := step w previous (out+n) exterior dst
  have issue : P.Spec (fun _ => True) (fun mid o =>
      o dst=(if mid previous=0 ∧ mid (out+n)=0 ∧ mid exterior=0 then 0 else 1) ∧
      ∀a, a≠dst → o a=mid a) (4+1*(2*(sticky previous (out+n) exterior).work+4)) := by
    apply spec_from_outputs (A:=P) (image dst 1 (sticky previous (out+n) exterior))
    intro mid
    obtain ⟨run,_,facts⟩ := step_exec previous (out+n) exterior dst mid (fits _ (by omega)) (fits _ (by omega))
      (fits _ (by omega)) room
    exact ⟨@run,facts⟩
  refine ⟨?_,@cheap_seq w (stage w C count codes rom n out) P (@cheap)
    (@scan_cheap w dst 1 (sticky previous (out+n) exterior))⟩
  apply seq_true (A:=stage w C count codes rom n out) (B:=P) (@test) (@issue)
  intro m mid o hm end_
  refine ⟨?_,fun a away ne => (end_.2 a ne).trans (hm.2 a away)⟩
  have one : (1:Word w)≠0 := by
    intro eq
    have h1 : (1:Word w).val=1 := by
      change 1 % (2^w) = 1
      exact Nat.mod_eq_of_lt (by omega)
    have v := congrArg Fin.val eq
    rw [h1,Fin.val_zero] at v
    omega
  rw [end_.1,hm.1,hm.2 previous (Or.inl earlier.1),hm.2 exterior (Or.inl earlier.2)]
  by_cases valid : ∀ i : Fin n, SeatValid C (m count).val (m (codes.base+i.val)).val i.val <;>
    simp [valid,one]

/-- Every chained physical epoch extends the previously checked list of predicates.
The list may come from a dependent sequence of reached matching tables. -/
theorem all_epochs {last : ℕ} (flag : Fin (last+1) → Word w) (seedOK : Prop)
    (epochOK exteriorOK : Fin last → Prop) (seed : flag 0=0 ↔ seedOK)
    (issued : ∀i : Fin last, flag i.succ=0 ↔ flag i.castSucc=0 ∧ exteriorOK i ∧ epochOK i) :
    flag (Fin.last last)=0 ↔ seedOK ∧ (∀i,exteriorOK i) ∧ (∀i,epochOK i) := by
  have go (j : ℕ) (hj : j ≤ last) :
      flag ⟨j,Nat.lt_succ_of_le hj⟩=0 ↔ seedOK ∧ ∀i : Fin last,i.val < j → exteriorOK i ∧ epochOK i := by
    induction j with
    | zero=>simpa using seed
    | succ j ih=>
      let i : Fin last := ⟨j,by omega⟩
      change flag i.succ=0 ↔ _
      rw [issued i]
      have hprev := ih (Nat.le_of_succ_le hj)
      change flag i.castSucc=0 ↔ _ at hprev
      rw [hprev]
      constructor
      · rintro ⟨⟨a,old⟩,ext,ep⟩
        refine ⟨a,fun u hu => ?_⟩
        by_cases before : u.val < j
        · exact old u before
        · obtain rfl : u=i := Fin.ext (by dsimp [i];omega)
          exact ⟨ext,ep⟩
      · rintro ⟨a,ok⟩
        have end_ := ok i (Nat.lt_succ_self j)
        exact ⟨⟨a,fun u hu=>ok u (by omega)⟩,end_.1,end_.2⟩
  rw [show flag (Fin.last last)=0 ↔ _ from go last le_rfl]
  simp [forall_and]


end
end Hierarchy.DescentTerminalEpochFlags

end OAI
