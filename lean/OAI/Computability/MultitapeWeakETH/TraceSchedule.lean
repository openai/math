import OAI.Computability.MultitapeWeakETH.InputBlocks

/-! # The fixed trace schedule, its clock and its network bounds -/

namespace OAI.Computability.MultitapeWeakETH.PhysicalBlocks

open scoped Classical
noncomputable section

def cut (T b j : ℕ) := min (j*b) (T+1)
def epochs (T b : ℕ) := T/b+1

theorem cut_succ (T b j : ℕ) :
    cut T b j ≤ cut T b (j+1) ∧ cut T b (j+1) ≤ cut T b j + b := by
  simp only [cut,Nat.succ_mul]
  omega

theorem cut_final (T : ℕ) {b : ℕ} (hb : 0 < b) : cut T b (epochs T b) = T+1 := by
  have h := Nat.mod_add_div T b
  have r := Nat.mod_lt T hb
  simp only [cut,epochs,Nat.succ_mul,mul_comm (T/b) b]
  omega

variable (M : Machine)
local instance : Fintype M.Tapes := @Fintype.ofFinite _ M.tapesFinite

/-- Record the heads of a run through the inclusive deadline, padding with its
final head positions. -/
def boundaryPos (coins : ℕ → M.Choice) (initial : Config M) (T : ℕ) (i : M.Tapes) (t : ℕ) :=
  ((config (frozenRun M coins initial (min t (T+1)))).tape i).pos

theorem boundary_motion (coins : ℕ → M.Choice) (initial : Config M) (T : ℕ) (i : M.Tapes) (t : ℕ) :
    |boundaryPos M coins initial T i (t+1) - boundaryPos M coins initial T i t| ≤ 1 := by
  by_cases before : t < T+1
  · simpa only [boundaryPos,min_eq_left (Nat.succ_le_of_lt before),min_eq_left before.le,frozenRun] using
      freeze_motion (frozenRun M coins initial t) (coins t) i
  · simp [boundaryPos,min_eq_right (by omega : T+1 ≤ t),min_eq_right (by omega : T+1 ≤ t+1)]

def headIndex := Fintype.equivFin M.Tapes

def traceOf {b : ℕ} (hb : 0 < b) (T : ℕ) (coins : ℕ → M.Choice) (initial : Config M) :
    TraceCode (Fintype.card M.Tapes) (epochs T b) :=
  recordBlocks _ b hb (fun i => boundaryPos M coins initial T ((headIndex M).symm i))
    (fun _ => boundary_motion M coins initial T _)

def bases {b T : ℕ} (start : M.Tapes → ℤ) (code : TraceCode (Fintype.card M.Tapes) (epochs T b)) :
    ℕ → M.Tapes → ℤ
  | 0,i => start i / b
  | j+1,i => bases start code j i + if h : j < epochs T b then ((code ⟨j,h⟩ (headIndex M i)).val:ℤ)-1 else 0

theorem traceOf_fits {b : ℕ} (hb : 0 < b) (T : ℕ) (coins : ℕ → M.Choice) (initial : Config M)
    {j : ℕ} (hj : j ≤ epochs T b) :
    Fits (b:=b) (bases M (fun i => (initial.tape i).pos) (traceOf M hb T coins initial) j)
      (frozenRun M coins initial (cut T b j)) := by
  intro i
  induction j with
  | zero => simp [cut,bases,config,frozenRun]
  | succ j ih =>
    have lt : j < epochs T b := by omega
    obtain eq := recordBlocks_decode (epochs:=epochs T b) hb
      (fun k t => boundaryPos M coins initial T ((headIndex M).symm k) t)
      (fun k => boundary_motion M coins initial T _) ⟨j,lt⟩ (headIndex M i)
    simp only [Equiv.symm_apply_apply,boundaryPos] at eq
    change ((traceOf M hb T coins initial ⟨j,lt⟩ (headIndex M i)).val:ℤ)-1 =
      ((config (frozenRun M coins initial (cut T b (j+1)))).tape i).pos / b -
        ((config (frozenRun M coins initial (cut T b j))).tape i).pos / b at eq
    simp only [bases,dite_eq_left lt]
    rw [← ih lt.le]
    omega

variable (n b T : ℕ)
def vertices := n ⌈/⌉ b + epochs T b + n ⌈/⌉ b
def inVertex : Fin (n ⌈/⌉ b) ↪ Fin (vertices n b T) :=
  ⟨fun j => ⟨j.val,by have := j.isLt; unfold vertices; omega⟩,fun _ _ eq => Fin.ext (congrArg (Fin.val (n:=vertices n b T)) eq)⟩
def outVertex : Fin (n ⌈/⌉ b) ↪ Fin (vertices n b T) :=
  ⟨fun j => ⟨n ⌈/⌉ b + epochs T b + j.val,Nat.add_lt_add_left j.isLt _⟩,
   fun _ _ eq => Fin.ext (Nat.add_left_cancel (congrArg Fin.val eq))⟩

def schedule (base : ℕ → M.Tapes → ℤ) (v : Fin (vertices n b T)) : Finset (Key M) :=
  if v.val < n ⌈/⌉ b then ioKeys M (leftTape M) (leftStart M n) n b v.val
  else if v.val < n ⌈/⌉ b + epochs T b then epochKeys M (base (v.val - n ⌈/⌉ b))
  else ioKeys M M.output (M.offset n) n b (v.val - (n ⌈/⌉ b + epochs T b))

def traceNetwork (base : ℕ → M.Tapes → ℤ) : Network n b :=
  TraceNetwork.network (schedule M n b T base) (fun _ => widthFactor M * b)
    (inVertex n b T) (outVertex n b T)

def degreeFactor := max (widthFactor M) (2*(3 * Fintype.card M.Tapes + 2))

theorem traceNetwork_bounded (base : ℕ → M.Tapes → ℤ) :
    (traceNetwork M n b T base).Bounded (degreeFactor M) := by
  apply TraceNetwork.bounded
  · intro v
    apply le_trans _ (le_max_right ..)
    apply Nat.mul_le_mul_left
    unfold schedule
    split
    · exact (ioKeys_card ..).trans (by omega)
    · split
      · exact (epochKeys_card ..).trans (by omega)
      · exact (ioKeys_card ..).trans (by omega)
  · intro _
    exact Nat.mul_le_mul_right _ (le_max_left ..)

theorem traceNetwork_size (base : ℕ → M.Tapes → ℤ) :
    (traceNetwork M n b T base).vertices * b ≤ 3*(b+T+n) := by
  have bound := Nat.div_mul_le_self (n+b-1) b
  have time := Nat.div_mul_le_self T b
  change (n ⌈/⌉ b + (T/b+1) + n ⌈/⌉ b)*b ≤ _
  simp only [Nat.ceilDiv_eq_add_pred_div,add_mul,one_mul]
  omega

end
end OAI.Computability.MultitapeWeakETH.PhysicalBlocks
