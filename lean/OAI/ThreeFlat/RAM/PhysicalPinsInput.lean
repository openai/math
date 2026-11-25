import Mathlib.Data.ZMod.Defs
import OAI.ThreeFlat.Diagonal.BoundaryWire
import OAI.ThreeFlat.RAM.ContractionMemory
import OAI.ThreeFlat.RAM.DescriptorExpr

namespace OAI
/-! # Paired external input and the native gather for the physical H evaluator -/

namespace ThreeFlat.RAM.PhysicalPinsInput

open Computability.VPVNP.BurstRAM DescriptorExpr BitLayout Diagonal.BoundaryWire
open scoped Fin.CommRing
variable {w k d T a : ℕ}

/-- Physical bits 2j and 2j+1 hold the row and column external states. The
advice starts after all pairs. Both auxiliary words are supplied as zeros. -/
def rawBit (D : Fin d → Bool) (x y : Fin T → Bool) (n : ℕ) : Bool :=
  if h : n < 2*T then
    let j : Fin T := ⟨n/2,by omega⟩
    if n%2=0 then x j else y j
  else if h : n-2*T<d then D ⟨_,h⟩ else false

theorem raw_left (D : Fin d → Bool) (x y : Fin T → Bool) (j : Fin T) :
    rawBit D x y (2*j.val) = x j := by
  have h := j.isLt
  simp [rawBit,show 2*j.val<2*T by omega]

theorem raw_right (D : Fin d → Bool) (x y : Fin T → Bool) (j : Fin T) :
    rawBit D x y (2*j.val+1) = y j := by
  have h := j.isLt
  simp [rawBit,show 2*j.val+1<2*T by omega,show (2*j.val+1)/2=j.val by omega,
    show (2*j.val+1)%2=1 by omega]

theorem raw_advice (D : Fin d → Bool) (x y : Fin T → Bool) (j : Fin d) :
    rawBit D x y (2*T+j.val) = D j := by simp [rawBit,j.isLt]

/-- Canonical boundary state for two catalyst halves and a zero auxiliary word. -/
def endpoint {chunks : ℕ} (x : Fin (chunks*a+chunks*a) → Bool) : State chunks a :=
  (stateEquiv chunks a).symm (Fin.append x (fun _ : Fin a => false))

def logical (D : Fin d → Bool) (x y : Fin T → Bool) : Fin (d+((T+a)+(T+a))) → Bool :=
  Fin.append D (Fin.append (Fin.append x (fun _ => false)) (Fin.append y (fun _ => false)))

theorem logical_pins {chunks : ℕ} (D : Fin d → Bool) (x y : Fin (chunks*a+chunks*a) → Bool) :
    logical (a:=a) D x y = pinBits D (endpoint x) (endpoint y) := by
  unfold logical pinBits endpoint
  rw [(stateEquiv chunks a).apply_symm_apply (Fin.append x (fun _ : Fin a => false)),
    (stateEquiv chunks a).apply_symm_apply (Fin.append y (fun _ : Fin a => false))]
  rfl

/-- Option-valued absolute offset within the staged raw tape. -/
def source (d T a j : ℕ) : Option ℕ :=
  if j<d then some (2*T+j)
  else if j<d+T then some (2*(j-d))
  else if j<d+T+a then none
  else if j<d+T+a+T then some (2*(j-(d+T+a))+1)
  else none

theorem source_read (D : Fin d → Bool) (x y : Fin T → Bool) (j : Fin (d+((T+a)+(T+a)))) :
    ((source d T a j.val).map (rawBit D x y)).getD false = logical D x y j := by
  refine Fin.addCases (fun u => ?_) (fun z => ?_) j
  · simpa [source,logical,u.isLt] using raw_advice D x y u
  refine Fin.addCases (fun u => ?_) (fun u => ?_) z
  · refine Fin.addCases (fun s => ?_) (fun s => ?_) u
    · have hs := s.isLt
      simp only [Fin.val_natAdd,Fin.val_castAdd,logical,Fin.append_right,Fin.append_left]
      simpa [source,show ¬d+s.val<d by omega,show d+s.val<d+T by omega] using raw_left D x y s
    · have hs := s.isLt
      simp only [Fin.val_natAdd,Fin.val_castAdd,logical,Fin.append_right,Fin.append_left]
      simp [source,show ¬d+(T+s.val)<d by omega,show ¬d+(T+s.val)<d+T by omega,
        show d+(T+s.val)<d+T+a by omega]
  · refine Fin.addCases (fun s => ?_) (fun s => ?_) u
    · have hs := s.isLt
      simp only [Fin.val_natAdd,Fin.val_castAdd,logical,Fin.append_right,Fin.append_left]
      simpa [source,show ¬d+(T+a+s.val)<d by omega,
        show ¬d+(T+a+s.val)<d+T by omega,show ¬d+(T+a+s.val)<d+T+a by omega,
        show d+(T+a+s.val)<d+T+a+T by omega,show d+(T+a+s.val)-(d+T+a)=s.val by omega]
        using raw_right D x y s
    · have hs := s.isLt
      simp only [Fin.val_natAdd,logical,Fin.append_right]
      simp [source,show ¬d+(T+a+(T+s.val))<d by omega,show ¬d+(T+a+(T+s.val))<d+T by omega,
        show ¬d+(T+a+(T+s.val))<d+T+a by omega,show ¬d+(T+a+(T+s.val))<d+T+a+T by omega]

def pinCount (d T a : ℕ) := d+((T+a)+(T+a))

/-- A native affine read, relative to the absolute address being filled. -/
def readAffine (base stride start : ℕ) : Term w k 1 :=
  .load (.binary .add (.literal (base : Word w)) (.binary .mul (.literal (stride : Word w))
    (.binary .sub (.result 0) (.literal (start : Word w)))))

def before (cut : ℕ) (yes no : Term w k 1) : Term w k 1 :=
  .select .lt (.result 0) (.literal (cut : Word w)) yes no

private theorem before_eval (q z : ℕ) (yes no : Term w k 1) (data : Fin k → Word w) (m : Memory w)
    (hq : q<2^w) (hz : z<2^w) :
    (before q yes no).eval data m (fun _ => (z : Word w)) =
      if z<q then yes.eval data m (fun _ => (z : Word w)) else no.eval data m (fun _ => (z : Word w)) := by
  have h : ((z : Word w)<(q : Word w)) ↔ z<q := by
    change ((z : Word w) : ℕ) < ((q : Word w) : ℕ) ↔ _
    rw [Fin.val_cast_of_lt hz,Fin.val_cast_of_lt hq]
  simp [before,Comparison.test,Term.eval,h]

private theorem affine_eval (base stride start z : ℕ) (data : Fin k → Word w) (m : Memory w)
    (above : start≤z) (fit : base+stride*(z-start)<2^w) :
    (readAffine base stride start).eval data m (fun _ => (z : Word w)) = m (base+stride*(z-start)) := by
  simp only [readAffine,Term.eval_load,Term.eval_binary,Term.eval_literal,Term.eval,PrivateRAM.BinaryOp.eval]
  rw [← Nat.cast_sub above,← Nat.cast_mul,← Nat.cast_add,Fin.val_cast_of_lt fit]

/-- Branches compare absolute destination pin positions, and insert literal zero for the
two omitted auxiliary words. -/
def gather (d T a stage : ℕ) : Term w k 1 :=
  before (2+d) (readAffine (stage+2*T) 1 2)
    (before (2+d+T) (readAffine stage 2 (2+d))
      (before (2+d+T+a) (.literal 0)
        (before (2+d+T+a+T) (readAffine (stage+1) 2 (2+d+T+a)) (.literal 0))))

theorem gather_binds (d T a stage : ℕ) : (gather (w:=w) (k:=k) d T a stage).binds ≤ 50 := by
  simp [gather,before,readAffine,Term.binds,Term.binary,Term.load,Term.literal,Term.select]

theorem gather_eval (D : Fin d → Bool) (x y : Fin T → Bool) (j : Fin (d+((T+a)+(T+a))))
    (stage : ℕ) (data : Fin k → Word w) (m : Memory w) (dst : 2+pinCount d T a<2^w)
    (src : stage+2*T+d<2^w)
    (raw : ∀ i, i<2*T+d → m (stage+i)=bitWord w (rawBit D x y i)) :
    (gather d T a stage).eval data m (fun _ => ((2+j.val : ℕ) : Word w)) =
      bitWord w (logical D x y j) := by
  have hj := j.isLt
  unfold pinCount at dst
  rw [← source_read]
  unfold gather
  repeat rw [before_eval _ _ _ _ _ _ (by omega) (by omega)]
  by_cases h₀ : j.val<d
  · have hz : 2+j.val<2+d := by omega
    rw [ite_eq_left hz,affine_eval _ _ _ _ _ _ (by omega) (by omega)]
    rw [show stage+2*T+1*(2+j.val-2)=stage+(2*T+j.val) by omega,raw _ (by omega)]
    simp [source,h₀]
  by_cases h₁ : j.val<d+T
  · rw [ite_eq_right (by omega),ite_eq_left (by omega),affine_eval _ _ _ _ _ _ (by omega) (by omega)]
    rw [show 2+j.val-(2+d)=j.val-d by omega,raw _ (by omega)]
    simp [source,h₀,h₁]
  by_cases h₂ : j.val<d+T+a
  · rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left (by omega)]
    simp [source,h₀,h₁,h₂,bitWord]
  by_cases h₃ : j.val<d+T+a+T
  · rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_left (by omega),
      affine_eval _ _ _ _ _ _ (by omega) (by omega)]
    rw [show stage+1+2*(2+j.val-(2+d+T+a))=stage+(2*(j.val-(d+T+a))+1) by omega,raw _ (by omega)]
    simp [source,h₀,h₁,h₂,h₃]
  · rw [ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega),ite_eq_right (by omega)]
    simp [source,h₀,h₁,h₂,h₃,bitWord]

/-- The low initialization writes both literal cells, the gathered pin cells and a zero
to every hidden-choice word before the generated cell-record interval. -/
def low (d T a stage : ℕ) : Term w k 1 :=
  before 2 (.result 0) (before (2+pinCount d T a) (gather d T a stage) (.literal 0))

theorem low_binds (d T a stage : ℕ) : (low (w:=w) (k:=k) d T a stage).binds ≤ 56 := by
  have h := gather_binds (w:=w) (k:=k) d T a stage
  simp only [low,before,Term.select,Term.binds_letThen,Term.binds_rename,Term.literal,Term.binds]
  omega

/-- The native initializer writes the standard contraction image below its first
record, even when the input RAM contains arbitrary words outside the staged tape. -/
theorem low_eval {F : Type*} [Fintype F] [Semiring F] [Nonempty F]
    (N : BitNetwork F (pinCount d T a)) (code : FieldCode F w)
    (D : Fin d → Bool) (x y : Fin T → Bool) (stage : ℕ) (data : Fin k → Word w)
    (mem : Memory w) (q : Word w) (h : q.val<cellsBase (pinCount d T a) N.internal)
    (hd : cellsBase (pinCount d T a) N.internal < 2^w) (src : stage+2*T+d<2^w)
    (raw : ∀ i, i<2*T+d → mem (stage+i)=bitWord w (rawBit D x y i)) :
    (low d T a stage).eval data mem (fun _ => q) =
      memory N code (logical D x y) (fun _=>false) q.val := by
  have hp : 2+pinCount d T a<2^w := by unfold cellsBase hiddenBase at hd; omega
  have hw : 2<2^w := by omega
  have value (s : BitSource N.internal (pinCount d T a)) :=
    read_source N code (logical D x y) (fun _=>false) s
  have z : ((q.val : ℕ) : Word w) = q := Fin.cast_val_eq_self q
  conv_lhs => rw [← z]
  unfold low
  rw [before_eval _ _ _ _ _ _ hw q.isLt]
  by_cases lit : q.val<2
  · rw [ite_eq_left lit]
    rcases (by omega : q.val=0 ∨ q.val=1) with h|h
    · simpa [h,Term.eval,bitWord,sourceAddress,BitSource.read,memory] using (value (.constant false)).symm
    · simpa [h,Term.eval,bitWord,sourceAddress,BitSource.read,memory] using (value (.constant true)).symm
  rw [ite_eq_right lit,before_eval _ _ _ _ _ _ hp q.isLt]
  by_cases pin : q.val<2+pinCount d T a
  · let i : Fin (pinCount d T a) := ⟨q.val-2,by omega⟩
    have qi : 2+i.val=q.val := by dsimp [i]; omega
    rw [ite_eq_left pin,← qi,gather_eval D x y i stage data mem hp src raw]
    exact (value (.pin i)).symm
  · let i : Fin N.internal := ⟨q.val-hiddenBase (pinCount d T a),
      by unfold cellsBase hiddenBase at h; unfold hiddenBase; omega⟩
    have qi : sourceAddress (.hidden i : BitSource N.internal (pinCount d T a)) = q.val := by
      dsimp [i,sourceAddress,hiddenBase]; omega
    rw [ite_eq_right pin,Term.eval_literal,← qi]
    exact (value (.hidden i)).symm

end ThreeFlat.RAM.PhysicalPinsInput

end OAI
