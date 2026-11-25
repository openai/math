import OAI.ThreeFlat.Diagonal.PhysicalShrinkBase
import OAI.ThreeFlat.Diagonal.PhysicalShrinkAdmission
import OAI.ThreeFlat.Diagonal.PhysicalRefreshAdmission
import OAI.ThreeFlat.Diagonal.PhysicalBlockSchedule

namespace OAI
/-! # Width-generic chronological stage clocks of the native shrinking and refresh program -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression CompressorPacking Native.ShrinkStage Native.ShrinkStage.Resident
open NavigationPass NavigationDirectory
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F]

namespace Program
/-- The fixed instruction and table coefficients of the specific finite program. -/
def nativeCoefficient (K : ℕ) : {s : ℕ} → Program F s → ℕ
  | _,.done _ => 0
  | _,.shrink s t T _ tail => (shrink_absolute_time T s (2^t) K).choose + nativeCoefficient K tail
  | _,.refresh _ _ _ _ _ _ _ T _ _ sym rows zero _ _ tail =>
      133+(refresh_absolute_time T sym rows zero K).choose + nativeCoefficient K tail

/-- The installed stage budgets, at each actual directory address. -/
def nativeTicks {W : ℕ} (K : ℕ) (cur : Word W) : {s : ℕ} → Program F s → Cursor → ℕ → ℕ → ℕ
  | _,.done _,_,_,_ => 0
  | _,.shrink s t T _ tail,c,r,v =>
    let b := tail.charge+r
    let x := dims (shrinkStage s (2^t)) v (CompressorPacking.tagBits (2^s)) b
    shrinkAbsoluteTicks T s (2^t) K cur c v b+
      nativeTicks K cur tail (allocate K c (.shrink x)).next r (v*2^CompressorPacking.tagBits (2^s))
  | _,.refresh s _ h pad _ _ _ T _ _ sym rows zero _ _ tail,c,r,v =>
    let b := tail.charge+r
    refreshAbsoluteTicks T sym rows zero K cur c v b+
      nativeTicks K cur tail (allocate K c (.refresh v (2^s) (2^b) h pad)).next r (v*2^s)


/-- Every accepted shrink branch has exactly this physical head budget and this
tail-directory lookup, even though the graph itself depends on the decoded branch. -/
theorem native_shrink_step {s t W : ℕ} (T : ShrinkMotif.Table F)
    (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/2^t≤1/1024)
    (tail : Program F t) (K : ℕ) (cur : Word W) (c : Cursor) (r : ℕ)
    (a : State (2^s) (shrinkCharge s+(tail.charge+r))) :
    let ok : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/(2^t:ℕ)≤1/1024 := by exact_mod_cast small
    let M := shrinkBinary T s (2^t) (tail.charge+r) (Nat.two_pow_pos _) ok a
    let x := dims (shrinkStage s (2^t)) (Fintype.card a.Base) (CompressorPacking.tagBits (2^s)) (tail.charge+r)
    ∀ q,nativeTicks K cur (.shrink s t T small tail) c r (Fintype.card a.Base) =
      shrinkBudget T s (2^t) (tail.charge+r) (Nat.two_pow_pos _) ok a K cur c+
        nativeTicks K cur tail (allocate K c (.shrink x)).next r (Fintype.card (M.next q).Base) := by
  dsimp only
  intro q
  rw [shrinkBudget_absolute,shrinkBinary_next_base]
  rfl

theorem native_refresh_step {s t h pad W : ℕ} {cst : Fin (2^s)→Fin (2^s)→ℕ} {γ C : ℝ}
    (T : RefreshMotif.Table F cst (1+h+pad) C) (hm : 2≤2^s) (hh : 0<h)
    (sym : ∀ i j,cst i j=cst j i) (rows : ∀ i,∑ j,cst i j=h) (zero : ∀ i,cst i i=0)
    (conn : Expander.Bound (Expander.transition cst h) ℝ γ) (degree : 1+h+pad=2^t)
    (tail : Program F t) (K : ℕ) (cur : Word W) (c : Cursor) (r : ℕ)
    (a : State (2^s) (s+(tail.charge+r))) :
    let M := refreshBinary T a hm hh sym rows zero conn
    let v := Fintype.card a.Base
    ∀ q,nativeTicks K cur (.refresh s t h pad cst γ C T hm hh sym rows zero conn degree tail) c r v =
      refreshCallTime T a sym rows zero K cur c+
        nativeTicks K cur tail (allocate K c (.refresh v (2^s) (2^(tail.charge+r)) h pad)).next r
          (Fintype.card (M.next q).Base) := by
  dsimp only
  intro q
  rw [refreshCallTime_absolute,refreshBinary_next_base]
  rfl

theorem nativeTicks_le {s W : ℕ} (K : ℕ) (cur : Word W) (P : Program F s) (c : Cursor) (r v : ℕ) :
    nativeTicks K cur P c r v≤nativeCoefficient K P*(1+v*2^(P.charge+r)) := by
  induction P generalizing c v with
  | done s => simp [nativeTicks,nativeCoefficient]
  | shrink s t T small tail ih =>
    let b := tail.charge+r
    let x := dims (shrinkStage s (2^t)) v (CompressorPacking.tagBits (2^s)) b
    let a := (shrink_absolute_time T s (2^t) K).choose
    let z := v*2^(shrinkCharge s+b)
    have h := (shrink_absolute_time T s (2^t) K).choose_spec W cur c b v
    have ar := shrink_positions s t b v
    have sizes : (v*2^(CompressorPacking.tagBits (2^s)))*2^b≤z := by
      have q : x.outputSites*4≤z := ar.2.trans_eq ar.1
      change ((v*2^(CompressorPacking.tagBits (2^s)))*2^b)*4≤z at q
      omega
    have tailCost := (ih (allocate K c (.shrink x)).next (v*2^(CompressorPacking.tagBits (2^s)))).trans
      (Nat.mul_le_mul_left _ (Nat.add_le_add_left sizes 1))
    change shrinkAbsoluteTicks T s (2^t) K cur c v b+_ ≤
      (a+nativeCoefficient K tail)*(1+v*2^((shrinkCharge s+tail.charge)+r))
    rw [Nat.add_assoc (shrinkCharge s) tail.charge r,Nat.add_mul]
    exact Nat.add_le_add h tailCost
  | refresh s t h pad cst γ C T hm hh sym rows zero conn degree tail ih =>
    let b := tail.charge+r
    let a := (refresh_absolute_time T sym rows zero K).choose
    let z := v*2^(s+b)
    let entry := allocate K c (.refresh v (2^s) (2^b) h pad)
    have sizes : v*2^s*2^b=z := (refresh_positions s b v h pad).2
    have one := (refresh_absolute_time T sym rows zero K).choose_spec W cur c b v
    rw [sizes] at one
    have headCost : refreshAbsoluteTicks T sym rows zero K cur c v b≤(133+a)*(1+z) :=
      one.trans (by change 133+a*z≤_; nlinarith only [Nat.zero_le a,Nat.zero_le z])
    have tailCost := ih entry.next (v*2^s)
    change nativeTicks K cur tail entry.next r (v*2^s)≤nativeCoefficient K tail*(1+(v*2^s)*2^b) at tailCost
    rw [sizes] at tailCost
    change refreshAbsoluteTicks T sym rows zero K cur c v b+_ ≤
      ((133+a)+nativeCoefficient K tail)*(1+v*2^((s+tail.charge)+r))
    rw [Nat.add_assoc s tail.charge r,Nat.add_mul]
    exact Nat.add_le_add headCost tailCost

theorem nativeCoefficient_cast {s t : ℕ} (K : ℕ) (e : s=t) (P : Program F s) :
    nativeCoefficient K (e ▸ P : Program F t)=nativeCoefficient K P := by cases e;rfl


end Program

namespace Block
variable (B : Block F)

def shrinkNativeCoefficients (K : ℕ) : ℕ → ℕ → ℕ
  | 0,_ => 0
  | n+1,i => (shrink_absolute_time B.shrink (B.exponent i) (2^B.exponent (i+1)) K).choose+
        shrinkNativeCoefficients K n (i+1)

/-- The displayed coefficient uses the actual sequence of shrinking dyadic degrees
and the specific refresh graph and field table chosen for the block. -/
def nativeCoefficient (K : ℕ) :=
  B.shrinkNativeCoefficients K B.levels 0+(133+(refresh_absolute_time B.refresh B.symmetric B.degree B.loopless K).choose)

theorem native_shrinkPrefix (K n i : ℕ) (P : Program F (B.exponent (i+n))) :
    Program.nativeCoefficient K (B.shrinkPrefix n i P)=B.shrinkNativeCoefficients K n i+Program.nativeCoefficient K P := by
  induction n generalizing i with
  | zero => simp [shrinkPrefix,shrinkNativeCoefficients]
  | succ n ih => simp only [shrinkPrefix,Program.nativeCoefficient,ih,Program.nativeCoefficient_cast,
      shrinkNativeCoefficients,Nat.add_assoc]

theorem native_prefix (K : ℕ) (P : Program F (B.exponent 0)) :
    Program.nativeCoefficient K (B.prefix P)=B.nativeCoefficient K+Program.nativeCoefficient K P := by
  simp only [«prefix»,native_shrinkPrefix,Program.nativeCoefficient_cast,Program.nativeCoefficient,
    nativeCoefficient,Nat.add_assoc]

theorem native_repeat (K n : ℕ) : Program.nativeCoefficient K (B.repeat n)=n*B.nativeCoefficient K := by
  induction n with
  | zero => simp only [Block.«repeat», Program.nativeCoefficient, Nat.zero_mul]
  | succ n ih => simpa only [Block.«repeat»,native_prefix,ih,Nat.succ_mul] using
        Nat.add_comm (B.nativeCoefficient K) (n*B.nativeCoefficient K)

theorem native_block_time {W : ℕ} (K : ℕ) (cur : Word W) (c : Cursor) (r v : ℕ) :
    Program.nativeTicks K cur (B.repeat 1) c r v≤B.nativeCoefficient K*(1+v*2^((B.repeat 1).charge+r)) := by
  simpa only [native_repeat,Nat.one_mul] using Program.nativeTicks_le K cur (B.repeat 1) c r v

theorem native_repeated_time {W : ℕ} (K n : ℕ) (cur : Word W) (c : Cursor) (r v : ℕ) :
    Program.nativeTicks K cur (B.repeat n) c r v≤n*B.nativeCoefficient K*(1+v*2^((B.repeat n).charge+r)) := by
  simpa only [native_repeat] using Program.nativeTicks_le K cur (B.repeat n) c r v

/-- The original trace uses k banks and k lane bits. -/
theorem native_cursor_time {W : ℕ} (K n : ℕ) (cur : Word W) (c : Cursor) {k r : ℕ}
    (split : (B.repeat n).charge+r=k) :
    Program.nativeTicks K cur (B.repeat n) c r k≤n*B.nativeCoefficient K*(1+k*2^k) := by
  simpa only [split] using B.native_repeated_time K n cur c r k


end Block
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
