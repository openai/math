import OAI.Hierarchy.ProbeStageAddress

namespace OAI
/-! # Static directories and private counters of the single-record allocator -/

namespace Hierarchy.ProbeStage.Native

def copies := 16
def fieldWidth (h : ℕ) := max 1 h
def fieldChunks (h : ℕ) := if h=0 then 16 else 48
def stringLength (h : ℕ) := 8*(4*h+2)
def groupBlocks (h d j : ℕ) := radix h d^j * blocks (2^widthLog h d j) (radix h d)
def regionSize (h d : ℕ) := (288*d+17)*extent h d
def region (h d j : ℕ) (i : Fin 16) := bankBase h d copies j 18+i.val*regionSize h d
def scratch (h d j : ℕ) (i : Fin 12) := bankBase h d copies j 14+i.val

theorem chunks_cover (h : ℕ) :
    stringLength h≤fieldChunks h*fieldWidth h ∧ fieldChunks h≤stringLength h ∧ fieldChunks h≤48 := by
  by_cases hz : h=0
  · simp [hz,stringLength,fieldChunks,fieldWidth]
  · have one : 1≤h := by omega
    simp [fieldChunks,hz,fieldWidth,max_eq_right one,stringLength]; omega

theorem least_size (h d : ℕ) : 2^(fieldWidth h) ≤ regionSize h d := by
  have n : 2^h≤extent h d := Nat.pow_le_pow_right (by decide) (by unfold roomBits;omega)
  have c : 2≤288*d+17 := by omega
  have bound := (Nat.mul_le_mul_left 2 n).trans (Nat.mul_le_mul_right (extent h d) c)
  apply le_trans _ bound
  by_cases hz : h=0
  · simp [fieldWidth,hz]
  · simp [fieldWidth,max_eq_right (by omega : 1≤h)]

/-- Each of the sixteen regions has the same fixed extent. The first
twelve hold hardwired offsets, labels and word tables. The last four hold
the two counter arrays and two arrays of mutable mask chunks. -/
theorem region_room {h d j : ℕ} (hd : 1≤d) (hj : j≤rounds d) :
    let B := radix h d
    let M := groupBlocks h d j
    let cap := regionSize h d
    M≤cap ∧ B≤cap ∧ B^4≤cap ∧ B^4*stringLength h≤cap ∧ M*B≤cap ∧
      M*(B^4*fieldChunks h)≤cap := by
  let B := radix h d
  let M := groupBlocks h d j
  let cap := regionSize h d
  have pos : 0<B := radix_pos h d
  have blocksPos : 0<blocks (2^widthLog h d j) B := by
    change 0<blocks (2^widthLog h d j) (radix h d)
    rw [blocks_exact]
    positivity
  have mp : 0<M := Nat.mul_pos (pow_pos pos _) blocksPos
  have lp : 0<stringLength h := by unfold stringLength;omega
  have counts := occurrences_at_depth (h:=h) hd hj
  have level : 4^j*2^h ≤ extent h d := by
    rw [extent,room_slots]
    exact Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) (by omega))
  rw [Nat.mul_assoc (288*d+17)] at counts
  have mem := counts.trans (Nat.mul_le_mul_left _ level)
  change M*(B^4*stringLength h+B)≤cap at mem
  have ca : M*B≤cap := (Nat.mul_le_mul_left M (Nat.le_add_left B _)).trans mem
  have payload : M*(B^4*stringLength h)≤cap :=
    (Nat.mul_le_mul_left M (Nat.le_add_right _ B)).trans mem
  have unit : B^4*stringLength h≤cap := (Nat.le_mul_of_pos_left _ mp).trans payload
  exact ⟨(Nat.le_mul_of_pos_right _ pos).trans ca,(Nat.le_mul_of_pos_left _ mp).trans ca,
    (Nat.le_mul_of_pos_right _ lp).trans unit,unit,ca,
    (Nat.mul_le_mul_left M (Nat.mul_le_mul_left _ (chunks_cover h).2.1)).trans payload⟩

/-- Every color has an equal-length directory interval. Its unused tail is
padding; only the true occurrence length is followed by the native scatter. -/
theorem padded_directory {h d : ℕ} (hd : 1≤d) :
    radix h d*(radix h d^4*stringLength h)≤regionSize h d := by
  let B := radix h d
  let f := digit h d
  have pos : 0<B := radix_pos h d
  have size : f+1 ≤ B := Nat.lt_two_pow_self
  have divstate := Nat.div_add_mod h (9*d)
  have rem := Nat.mod_lt h (by omega : 0<9*d)
  have hb : h ≤ (9*d)*(f+1) := by dsimp [f,digit];rw [Nat.mul_add,Nat.mul_one];omega
  have high : h ≤ 9*d*B := hb.trans (Nat.mul_le_mul_left _ size)
  have rep : stringLength h≤(288*d+16)*B := by unfold stringLength;nlinarith only [high,pos]
  have pow : B^6≤B^9 := Nat.pow_le_pow_right pos (by decide)
  have log : 9*f≤h := by
    have scale := Nat.mul_le_mul_right f (show 9≤9*d by omega)
    exact scale.trans (by unfold f digit;omega)
  have limit : B^9≤extent h d := by
    change (2^f)^9 ≤ 2^roomBits h d
    rw [← pow_mul,Nat.mul_comm f 9]
    exact Nat.pow_le_pow_right (by decide) (log.trans (by unfold roomBits;omega))
  calc
    B*(B^4*stringLength h) ≤ B*(B^4*((288*d+16)*B)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ rep)
    _ = (288*d+16)*B^6 := by ring
    _ ≤ regionSize h d := Nat.mul_le_mul (by omega) (pow.trans limit)

theorem region_end (h d j : ℕ) (i : Fin 16) :
    region h d j i+regionSize h d≤output h d copies j := by
  have cap := Nat.mul_le_mul_right (regionSize h d) (show i.val+1≤16 by omega)
  rw [Nat.succ_mul] at cap
  have diff : stride d copies-9=23+16*(288*d+17) := by unfold stride copies;omega
  unfold region output bankBase
  rw [diff,Nat.add_mul,Nat.mul_assoc]
  unfold regionSize at cap ⊢
  omega

theorem region_separate (h d j : ℕ) {i k : Fin 16} (order : i<k) :
    region h d j i+regionSize h d≤region h d j k := by
  have cap := Nat.mul_le_mul_right (regionSize h d) (show i.val+1≤k.val from order)
  rw [Nat.succ_mul] at cap
  unfold region
  omega

theorem scratch_separate (h d j : ℕ) (i : Fin 12) (k : Fin 16) : scratch h d j i<region h d j k := by
  have c : 2≤roomBits h d := by unfold roomBits;omega
  have lower : 4≤extent h d := Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) c
  unfold scratch region bankBase
  omega

end Hierarchy.ProbeStage.Native

end OAI
