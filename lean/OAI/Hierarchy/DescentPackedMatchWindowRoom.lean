import OAI.Hierarchy.DescentPackedMatchPhysicalOrder
import OAI.Hierarchy.DescentPackedMatchProfilePass
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Paying the last two packed profile reads from the measured occurrence count -/

namespace Hierarchy.DescentPacking.PackedMatch.ProfileTable
open ProtocolRAM DescentSIMDLookup MatchedStageRAM
open scoped Classical BigOperators
variable {C : Type} [Fintype C] {M n R w : ℕ}

def radix (s : Shape) (M : ℕ) := max 1 (M*s.pairs)

theorem radix_positive (s : Shape) (M : ℕ) : 0<radix s M := by simp [radix]
theorem radix_fits (s : Shape) (M : ℕ) : M*s.pairs≤radix s M := le_max_right ..

/-- Include the next word even when the last real profile ends at a word boundary. -/
def rawBank (base seats R : ℕ) : Bank := ⟨base,Nat.clog 2 (seats/R+2)⟩

theorem rawBank_size (base seats R : ℕ) :
    seats/R+2≤(rawBank base seats R).size ∧ (rawBank base seats R).size<2*(seats/R+2) := by
  let t := seats/R+2
  have ht : 1<t := Nat.succ_lt_succ (Nat.zero_lt_succ (seats/R))
  have pos := Nat.clog_pos (by decide : 1<2) ht
  have low := Nat.pow_pred_clog_lt_self (by decide : 1<2) ht
  refine ⟨Nat.le_pow_clog (by decide) _,?_⟩
  change 2^Nat.clog 2 t<2*t
  calc
    2^Nat.clog 2 t = 2^((Nat.clog 2 t).pred.succ) :=
      congrArg (fun k : ℕ => (2:ℕ)^k) (Nat.succ_pred_eq_of_pos pos).symm
    _ = 2*2^(Nat.clog 2 t).pred := by rw [pow_succ,Nat.mul_comm]
    _ < 2*t := Nat.mul_lt_mul_of_pos_left low (by decide)

theorem digit_room (s : Shape) (R : ℕ) (digit : 0<s.digit) : R≤2^(s.digit*R) := by
  have before : R≤ s.digit*R := by simpa using Nat.mul_le_mul_right R (show 1≤ s.digit from digit)
  exact Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) before)

theorem word_room {s : Shape} {l : Layout} (r : Room s M R n w l) (digit : 0<s.digit) : 2*R≤2^w := by
  have tables : 2^(s.digit*R)<2^w := by simpa only [Bank.size,r.scan.keyO] using r.scan.offset.2.1
  have exponent : s.digit*R<w := Nat.lt_of_not_ge (fun bad=>tables.not_ge
    (Nat.pow_le_pow_right (by decide : 0<2) bad))
  calc
    2*R≤2*2^(s.digit*R) := Nat.mul_le_mul_left _ (digit_room s R digit)
    _ = 2^(s.digit*R+1) := by rw [pow_succ,Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) exponent

theorem native_count {s : Shape} {l : Layout} (r : Room s M R n w l)
    (digit : 0<s.digit) (pos : 0<R) (span : M*s.pairs≤R) (key : Cell (s.outputBits*M)) :
    chunkCount s M key≤R ∧ chunkCount s M key<2^w := by
  have small := (chunkCount_bound s M key).trans span
  have total := word_room r digit
  exact ⟨small,by omega⟩

theorem measured_prefix (s : Shape) (keys : Fin n→Cell (s.outputBits*M))
    (seat : C↪Fin n×Fin M) (amount : C→ℕ)
    (measured : Chronology.Counts seat amount (fun i=>laneCounts s M (keys i)))
    (k : ℕ) (fit : k≤n) :
    PackedProfileCursor.total (quota s keys) k≤∑c,amount c := by
  let counts := fun i=>laneCounts s M (keys i)
  have start := Chronology.start seat amount counts measured k fit
  change PackedProfileCursor.total (Chronology.chunk counts) k≤_
  rw [start]
  calc
    _ ≤ countAt (Chronology.rank seat) amount (n*M) :=
      countAt_mono _ _ (Nat.mul_le_mul_right M fit)
    _ = _ := countAt_end _ _ (fun c=>(finProdFinEquiv (seat c)).isLt)

theorem window_room (s : Shape) (keys : Fin n→Cell (s.outputBits*M))
    (seat : C↪Fin n×Fin M) (amount : C→ℕ)
    (measured : Chronology.Counts seat amount (fun i=>laneCounts s M (keys i)))
    (seats : ℕ) (paid : (∑c,amount c)≤ seats) (raw : Bank) (spare : seats/R+2≤raw.size) :
    ∀i : Fin n,PackedProfileCursor.total (quota s keys) i.val/R+1<raw.size := by
  intro i
  have lower := (measured_prefix s keys seat amount measured i.val i.isLt.le).trans paid
  have value := Nat.div_le_div_right (c:=R) lower
  omega

theorem measured_rooms (s : Shape) (keys : Fin n→Cell (s.outputBits*M))
    (seat : C↪Fin n×Fin M) (amount : C→ℕ)
    (measured : Chronology.Counts seat amount (fun i=>laneCounts s M (keys i)))
    (raw : Bank) (seats : ℕ) (paid : (∑c,amount c)≤ seats) (spare : seats/R+2≤raw.size)
    (l : Layout) (r : Room s M R n w l) (digit : 0<s.digit) :
    2*R≤2^w ∧ R≤2^(s.digit*R) ∧
      ∀i : Fin n,PackedProfileCursor.total (quota s keys) i.val/R+1<raw.size :=
  ⟨word_room r digit,digit_room s R digit,window_room s keys seat amount measured seats paid raw spare⟩

end Hierarchy.DescentPacking.PackedMatch.ProfileTable

end OAI
