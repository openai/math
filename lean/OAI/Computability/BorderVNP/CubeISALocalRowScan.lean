import OAI.Computability.BorderVNP.CubeISALengthScan
import OAI.Computability.BorderVNP.RoutingISATableClear

/-! # Clearing and comparing an incident declaration row

Both operations visit exactly the number of cube coordinates. Clearing precedes
each owned role, including the second role when both endpoints have one team.
Comparison uses that row's two addresses and leaves the shared table intact.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LocalRow

open VPVNP.BurstRAM CubeLengths

variable {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)

/-- Clear the addressed coordinate and advance the local cursor. -/
def clearBody : Code := .block [.binary .add 62 58 56, .store 62 0, .binary .add 56 56 1]

/-- Clear one incident row of the true subtotal array before tallying it. -/
def clear : Code := .whileLt 56 57 clearBody

/-- Compare this row's local subtotal to the saved declaration at all coordinates. -/
def compare : Code := .whileLt 56 57 rowBody

/-- The physically cleared interval contains exactly the required zero initialization. -/
theorem clear_run (r : Bank w) (m : Memory w) (base a : ℕ)
    (zero : readings r 0 = 0) (one : readings r 1 = 1) (start : readings r 56 = 0)
    (dim : readings r 57 = a) (ptr : readings r 58 = base) (room : base+a ≤ 2^w) :
    BoundedRun pub mac clear r m (4*a+1) (fun z => z.mem = zeroPrefix base a (readings m)) := by
  let P (k : ℕ) (z : NatState) := z.reg 0 = 0 ∧ z.reg 1 = 1 ∧ z.reg 56 = k ∧
    z.reg 57 = a ∧ z.reg 58 = base ∧ z.mem = zeroPrefix base k (readings m)
  have step (k : ℕ) (hk : k < a) (t : Bank w) (mt : Memory w) (hs : P k (.ofWords t mt)) :
      BoundedRun pub mac clearBody t mt 3 (P (k+1)) := by
    let z := NatState.ofWords t mt
    obtain ⟨h0,h1,h56,h57,h58,hm⟩ := hs
    change z.reg 0 = 0 at h0
    change z.reg 1 = 1 at h1
    change z.reg 56 = k at h56
    change z.reg 57 = a at h57
    change z.reg 58 = base at h58
    change z.mem = _ at hm
    have inc : k+1 < 2^w := by have := (r 57).isLt; change readings r 57 < _ at this; omega
    have addr : base+k < 2^w := by omega
    have safe : clearBody.fixedSafe w (readings pub) z := by
      simp (config := {decide := true}) [clearBody,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,
        Code.evalNat,addressOpFits,h56,h58,h1,addr,inc]
    apply (clearBody.runFixed pub mac t mt safe).mono (by decide)
    rintro y rfl
    change P (k+1) (clearBody.fixedEval _ z)
    simp (config := {decide := true}) [P,clearBody,Code.block,Code.fixedEval,Code.evalNat,addressOp,
      h0,h1,h56,h57,h58,hm,extend_zeroPrefix]
  have init : P 0 (.ofWords r m) :=
    ⟨zero,one,start,dim,ptr,by funext x; simp [zeroPrefix,NatState.ofWords]⟩
  apply (run_counted_loop pub mac 56 57 clearBody a 3 P (fun _ _ h => ⟨h.2.2.1,h.2.2.2.1⟩)
    step 0 (Nat.zero_le _) r m init).mono (by omega)
  exact fun _ h => h.2.2.2.2.2

private theorem evalReqEq (x y : Reg) (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    (requireEq x y).evalNat p m s = s := by simp [requireEq,Code.evalNat]

private theorem safeReqEq (x y : Reg) (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    (requireEq x y).safeReadOnly w p m s ↔ s x = s y := by simp [requireEq,Code.safeReadOnly]

private theorem fitReqEq (x y : Reg) (p : Arg → ℕ) (m : ℕ → ℕ) (s : Reg → ℕ) :
    (requireEq x y).relaxReject.safeReadOnly w p m s := by
  simp [requireEq,Code.relaxReject,Code.safeReadOnly]

/-- The local guard accepts exactly pointwise equality between the addressed
rows. The runtime scan never modifies memory or caller registers below 56. -/
theorem compare_run (r : Bank w) (m : Memory w) (A B N : ℕ)
    (cur : readings r 56 = 0) (lim : readings r 57 = N) (left : readings r 58 = A)
    (right : readings r 59 = B) (one : readings r 60 = 1)
    (fitA : A+N ≤ 2^w) (fitB : B+N ≤ 2^w) :
    TestRun pub mac compare r m (N*(rowBody.slots+1)+1)
      (∀ j : Fin N, readings m (A+j.val) = readings m (B+j.val))
      (Kept (readings r) (readings m)) := by
  let p := readings pub
  let mem := readings m
  let I := ScanState (readings r) mem N A B (readings r 61)
  let good j := mem (A+j) = mem (B+j)
  have step (i : ℕ) (hi : i < N) (t : Bank w) (mt : Memory w) (hs : I i (.ofWords t mt)) :
      TestRun pub mac rowBody t mt rowBody.slots (good i) (I (i+1)) := by
    have a : A+i < 2^w := by omega
    have b : B+i < 2^w := by omega
    have inc : i+1 < 2^w := by have := (r 57).isLt; change readings r 57 < _ at this; omega
    have h56 : readings t 56 = i := hs.cursor
    have h58 : readings t 58 = A := hs.left
    have h59 : readings t 59 = B := hs.right
    have h60 : readings t 60 = 1 := hs.one
    have hm : readings mt = mem := hs.kept.1
    apply readTest _ t mt _ _ (by decide)
    · change (Code.block [.binary .add 62 58 56, .load 62 62, .binary .add 63 59 56,
        .load 63 63, (requireEq 62 63).relaxReject, .binary .add 56 56 60]).safeReadOnly _ _ _ _
      simp (config := {decide := true}) [Code.block,Code.safeReadOnly,Code.evalNat_relaxReject,
        evalReqEq,fitReqEq,Code.evalNat,addressOp,addressOpFits,h56,h58,h59,h60,a,b,inc]
    · simp (config := {decide := true}) [rowBody,Code.block,safeReqEq,Code.safeReadOnly,evalReqEq,Code.evalNat,
        addressOp,addressOpFits,h56,h58,h59,h60,hm,a,b,inc,good]
    · refine ⟨keptEval _ _ (by decide) hs.kept,?_,?_,?_,?_,?_,?_⟩ <;>
        simp (config := {decide := true}) [rowBody,Code.block,evalReqEq,Code.evalNat,addressOp,
          h56,h58,h59,h60] <;> first | exact hs.limit | exact hs.value
  have init : I 0 (.ofWords r m) := ⟨⟨rfl,fun _ _ => rfl⟩,cur,lim,left,right,one,rfl⟩
  apply (test_counted_loop 56 57 rowBody N (fun _ => rowBody.slots) good I
    (fun _ _ hs => ⟨hs.cursor,hs.limit⟩) step 0 (Nat.zero_le _) r m init).mono
  · simp [Finset.sum_const]
  · simp only [Nat.zero_le, good, mem]
    exact ⟨fun h j => h j.val trivial j.isLt, fun h j _ hj => h ⟨j,hj⟩⟩
  · exact fun _ h => h.kept

end RoutingISA.LocalRow

end BorderVNP
end Computability
end OAI
