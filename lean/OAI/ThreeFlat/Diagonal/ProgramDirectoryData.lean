import OAI.ThreeFlat.Diagonal.NavigationDirectory
import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule

namespace OAI
/-! # The chronological directory and its length for the physical program -/

namespace ThreeFlat.Diagonal.PhysicalStage.Program

open NavigationDirectory CompressorPacking.Native.ShrinkStage
open scoped Classical
noncomputable section
variable {F : Type} [Field F]

/-- The high radix is always the number of remaining *unconsumed* lane words.
New base ordinals append the adjacent-tag digit or the expander-port digit. -/
def directory : {s : ℕ} → (P : Program F s) → (residualBits oldBase : ℕ) → List Stage
  | _, .done _, _, _ => []
  | _, .shrink s t _ _ tail, rem, v =>
    let d := 2^s
    let tag := 2^CompressorPacking.tagBits d
    let x : Dimensions := ⟨v,d,2*d+1,tag,2^(tail.charge+rem),2^t⟩
    .shrink x :: directory tail rem (v*tag)
  | _, .refresh s _ h pad _ _ _ _ _ _ _ _ _ _ _ tail, rem, v =>
    .refresh v (2^s) (2^(tail.charge+rem)) h pad :: directory tail rem (v*2^s)

def length : {s : ℕ} → Program F s → ℕ
  | _, .done _ => 0
  | _, .shrink _ _ _ _ p => p.length+1
  | _, .refresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p => p.length+1

theorem directory_length {s : ℕ} (P : Program F s) (r v : ℕ) : (P.directory r v).length=P.length := by
  induction P generalizing v with
  | done => rfl
  | shrink _ _ _ _ p ih => simp only [directory,length,List.length_cons,ih]
  | refresh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ p ih => simp only [directory,length,List.length_cons,ih]

theorem header_length {s : ℕ} (P : Program F s) (K r v : ℕ) (c : Cursor) :
    (NavigationDirectory.tape K (P.directory r v) c).length = 64*P.length := by
  rw [NavigationDirectory.tape_length,directory_length]

end
end ThreeFlat.Diagonal.PhysicalStage.Program

end OAI
