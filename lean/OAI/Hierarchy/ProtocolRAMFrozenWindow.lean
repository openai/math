import OAI.Hierarchy.ProtocolRAMPackedLayout

namespace OAI
/-! # A forward, disjoint address allocation for one entire reported format -/
namespace Hierarchy.ProtocolRAMFrozenWindow
open ProtocolRAM ProtocolRAMPackedRanked

structure Size where
  rows : ℕ
  bins : ℕ
  groups : ℕ
  D : ℕ
  C : ℕ
  cap : ℕ

def Size.page (s : Size) := 2^groupBits s.rows
def Size.anchor (s : Size) (r : ℕ) (f : Fin 4) : Bank := ⟨r+2+f.val*s.page,groupBits s.rows⟩
def Size.rankStart (s : Size) (r : ℕ) := r+2+4*s.page
def Size.rank (s : Size) (r : ℕ) := fresh (s.rankStart r) s.rows s.bins
def Size.base (s : Size) (r : ℕ) := finish (s.rankStart r) s.rows s.bins
def Size.maskWords (s : Size) := s.C+2*(s.C*2*s.D)
def Size.widthBase (s : Size) (r : ℕ) := s.base r+s.maskWords
def Size.widthWords (s : Size) := 2*s.groups*s.D
def Size.src (s : Size) (r : ℕ) := s.widthBase r+s.widthWords
def Size.tape (s : Size) := 10*(s.rows*s.cap)
def Size.widthSrc (s : Size) (r : ℕ) := s.src r+s.tape
def Size.stop (s : Size) (r : ℕ) := s.widthSrc r+s.tape

theorem Size.start_base (s : Size) (r : ℕ) : s.rankStart r ≤ s.base r := by
  simp only [Size.base, finish, fresh, Layout.rank, Bank.size, Nat.add_assoc]
  exact Nat.le_add_right ..

theorem Size.base_stop (s : Size) (r : ℕ) : s.base r ≤ s.stop r := by
  unfold Size.stop Size.widthSrc Size.src Size.widthBase
  omega

theorem Size.before (s : Size) (r a : ℕ) (low : a<r) :
    a<(s.anchor r 0).base ∧ a<(s.rank r).spread ∧ a < s.base r ∧ a≠r ∧ a≠r+1 := by
  have h:=s.start_base r
  change a<r+2+0*s.page ∧ a < s.rankStart r ∧ a < s.base r ∧ a≠r ∧ a≠r+1
  unfold Size.rankStart at *
  omega

theorem Size.rank_fits (s : Size) (r W : ℕ) (room : s.stop r<2^W) :
    (s.rank r).Fits W s.rows s.bins :=
  fresh_fits _ _ _ _ ((s.base_stop r).trans_lt room)

theorem Size.anchor_fits (s : Size) (r W : ℕ) (room : s.stop r<2^W) (f : Fin 4) :
    (s.anchor r f).Fits W (s.rank r).spread := by
  have h := (s.start_base r).trans ((s.base_stop r).trans (Nat.le_of_lt room))
  have hi := Nat.mul_le_mul_right s.page f.isLt
  rw [Nat.succ_mul] at hi
  have lr := (s.start_base r).trans_lt ((s.base_stop r).trans_lt room)
  change 0 < s.page ∧ s.page<2^W ∧ r+2+f.val*s.page+s.page ≤ s.rankStart r
  unfold Size.rankStart at *
  exact ⟨Nat.two_pow_pos _,by omega,by omega⟩

theorem Size.anchor_sep (s : Size) (r : ℕ) :
    (s.anchor r 0).base+s.rows≤(s.anchor r 1).base ∧
    (s.anchor r 1).base+s.rows≤(s.anchor r 2).base ∧
    (s.anchor r 2).base+s.rows≤(s.anchor r 3).base ∧
    (s.anchor r 3).base+s.rows ≤ s.rankStart r := by
  have cap : s.rows ≤ s.page := group_capacity s.rows
  change r+2+0*s.page+s.rows≤r+2+1*s.page ∧ r+2+1*s.page+s.rows≤r+2+2*s.page ∧
    r+2+2*s.page+s.rows≤r+2+3*s.page ∧ r+2+3*s.page+s.rows≤r+2+4*s.page
  omega

theorem Size.stop_add (s : Size) (r : ℕ) : s.stop r=r+s.stop 0 := by
  simp only [Size.stop,Size.widthSrc,Size.src,Size.widthBase,Size.base,Size.rankStart,finish,fresh,
    Layout.rank,Bank.size,Nat.zero_add,Nat.add_assoc]

theorem Size.stop_le (s : Size) (r : ℕ) :
    s.stop r ≤ r+36*s.rows+s.bins+s.C+4*(s.C*s.D)+2*(s.groups*s.D)+20*(s.rows*s.cap)+19 := by
  have page : s.page≤2*(s.rows+1) := bias_words s.rows
  have alloc := finish_words (s.rankStart r) s.rows s.bins
  change s.base r≤r+2+4*s.page+28*s.rows+s.bins+9 at alloc
  have mask : s.maskWords=s.C+4*(s.C*s.D) := by unfold Size.maskWords;ring
  have width : s.widthWords=2*(s.groups*s.D) := by unfold Size.widthWords;ring
  simp only [Size.stop,Size.widthSrc,Size.src,Size.widthBase,mask,width,Size.tape]
  omega

theorem Size.needs (s : Size) (cap : 1 ≤ s.cap) :
    s.stop 0 ≤ 56*(s.rows*s.cap+s.bins+s.C+s.C*s.D+s.groups*s.D+1) := by
  have raw:=s.stop_le 0
  have nonempty : s.rows ≤ s.rows*s.cap := by simpa using Nat.mul_le_mul_left s.rows cap
  omega

end Hierarchy.ProtocolRAMFrozenWindow

end OAI
