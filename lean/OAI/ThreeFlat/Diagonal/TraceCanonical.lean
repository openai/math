import OAI.ThreeFlat.Diagonal.TraceRowCode
import OAI.ThreeFlat.Diagonal.TraceWordTests
import OAI.Computability.VPVNP.LiveHeaderBits

namespace OAI
/-! # Checking the canonical bit pattern of a single CPU row -/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP.VerifierNetwork (Frame)
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization TraceBanks TraceWords
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r : ℕ}

abbrev CodePin (w r : ℕ) := Fin (5+r) × Fin (w+1)
private abbrev E (w r : ℕ) := Expr (CodePin w r)

private def wpin (j : Fin (5+r)) (k : Fin (w+1)) : E w r := .input (j,k)
private def lit (v : Word (w+1)) (k : Fin (w+1)) : E w r := .const (bits v k)
private def low (j : Fin (5+r)) : Fin (w+1) → E w r :=
  Fin.snoc (fun i : Fin w => wpin j i.castSucc) (.const false)

def codePins (a : Fin (5+r) → Word (w+1)) : CodePin w r → Bool := fun i => bits (a i.1) i.2

private theorem low_eval (j : Fin (5+r)) (a : Fin (5+r) → Word (w+1)) (i : Fin (w+1)) :
    (low j i).eval (codePins a) = bits (wide (narrow (a j))) i := by
  induction i using Fin.lastCases with
  | last => simp [low, Expr.eval, bits, wide, Nat.testBit_lt_two_pow (narrow (a j)).isLt]
  | cast k => simp [low, wpin, Expr.eval, codePins, bits, wide, narrow, k.isLt]

private def tagLit (hw : 3 ≤ w+1) (t : Fin 8) : Word (w+1) :=
  ⟨t.val, lt_of_lt_of_le t.isLt (show 8 ≤ 2 ^ (w+1) from Nat.pow_le_pow_right (by decide : 0 < 2) hw)⟩

/-- Rebuild a candidate of the specified tag and counter using the supplied
register low bits and any operands actually consumed by that tag. -/
def candidate (i : Fin p) (t : Fin 8) (a : Fin (5+r) → Word (w+1)) :
    Row (w+1) (Snapshot w p r) :=
  let hd := fun j : Fin 5 => a (j.castAdd r)
  let s : Snapshot w p r := ⟨i, narrow (hd 2), fun j => narrow (a (Fin.natAdd 5 j))⟩
  match t.val with
  | 1 => .move s .tick
  | 2 => .move s (.choice false)
  | 3 => .move s (.choice true)
  | 4 => .move s (.read (hd 3) (hd 4))
  | 5 => .move s (.write (hd 3) (hd 4))
  | 6 => .halt s none
  | 7 => .halt s (some (hd 4))
  | _ => .pad

private def expected (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (i : Fin p) (t : Fin 8) :
    Fin (5+r) → Fin (w+1) → E w r :=
  if t.val = 0 then fun _ => lit 0 else
    Fin.append
      ![lit (tagLit hw t), lit (i.castLE hp), low ((2 : Fin 5).castAdd r),
        if t.val = 4 ∨ t.val = 5 then wpin ((3 : Fin 5).castAdd r) else lit 0,
        if t.val = 4 ∨ t.val = 5 ∨ t.val = 7 then wpin ((4 : Fin 5).castAdd r) else lit 0]
      (fun j => low (Fin.natAdd 5 j))

set_option maxHeartbeats 1600000 in
private theorem expected_at (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (i : Fin p) (t : Fin 8)
    (a : Fin (5+r) → Word (w+1)) (j : Fin (5+r)) (k : Fin (w+1)) :
    ((expected hw hp i t j k).eval (codePins a)) = bits ((rowFormat hw hp).words (candidate i t a) j) k := by
  induction j using Fin.addCases with
  | left j =>
    fin_cases t <;> fin_cases j <;> first | exact low_eval _ _ _ | rfl
  | right j =>
    fin_cases t <;> simp [expected, candidate, regs, lit, Expr.eval, low_eval]

private theorem candidate_surjective (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (defaultPC : Fin p)
    (x : Row (w+1) (Snapshot w p r)) :
    ∃ i t, candidate i t ((rowFormat hw hp).words x) = x := by
  cases x with
  | pad => exact ⟨defaultPC,0,rfl⟩
  | halt s out =>
    obtain ⟨i,st,reg⟩ := s
    cases out with
    | none => exact ⟨i,6,by simp [candidate, rowFormat, packedWords, header, regs]⟩
    | some a => exact ⟨i,7,by simp [candidate, rowFormat, packedWords, header, regs]⟩
  | move s e =>
    obtain ⟨i,st,reg⟩ := s
    cases e with
    | tick => exact ⟨i,1,by simp [candidate, rowFormat, packedWords, header, regs]⟩
    | choice b =>
      cases b with
      | false => exact ⟨i,2,by simp [candidate, rowFormat, packedWords, header, regs]⟩
      | true => exact ⟨i,3,by simp [candidate, rowFormat, packedWords, header, regs]⟩
    | read a v => exact ⟨i,4,by simp [candidate, rowFormat, packedWords, header, regs]⟩
    | write a v => exact ⟨i,5,by simp [candidate, rowFormat, packedWords, header, regs]⟩

private def caseTest (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (i : Fin p) (t : Fin 8) : E w r :=
  allBits fun j => sameWord (wpin j) (expected hw hp i t j)

private theorem caseTest_at (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (i : Fin p) (t : Fin 8)
    (a : Fin (5+r) → Word (w+1)) :
    (caseTest hw hp i t).eval (codePins a) = true ↔ a = (rowFormat hw hp).words (candidate i t a) := by
  rw [caseTest, allBits_true, funext_iff]
  apply forall_congr'
  intro j
  exact sameWord_at _ _ _ (fun _ => rfl) (expected_at hw hp i t a j)

def canonical (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) : E w r :=
  Expr.disjoin (List.ofFn fun i : Fin p => Expr.disjoin (List.ofFn fun t : Fin 8 =>
    caseTest hw hp i t))

/-- The canonicality gate accepts exactly the packed words of one typed CPU
row. The tag and the counter lookup remove all unused register and payload
bits from the accepted padding and halted representations. -/
theorem canonical_at (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (defaultPC : Fin p)
    (a : Fin (5+r) → Word (w+1)) :
    (canonical hw hp).eval (codePins a) = true ↔ ∃ x, (rowFormat hw hp).words x = a := by
  simp only [canonical, Expr.eval_disjoin_true, List.mem_ofFn, exists_exists_eq_and, caseTest_at]
  constructor
  · rintro ⟨i,t,he⟩
    exact ⟨_,he.symm⟩
  · rintro ⟨x,rfl⟩
    obtain ⟨i,t,he⟩ := candidate_surjective hw hp defaultPC x
    exact ⟨i,t,by rw [he]⟩

set_option maxHeartbeats 1000000 in
private theorem expected_size (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (i : Fin p) (t : Fin 8)
    (j : Fin (5+r)) (k : Fin (w+1)) : (expected hw hp i t j k).size ≤ 1 := by
  induction j using Fin.addCases with
  | left j =>
    fin_cases t <;> fin_cases j <;> first | rfl | induction k using Fin.lastCases <;> simp [expected, low, lit, wpin, Expr.size]
  | right j =>
    fin_cases t <;> first | rfl | induction k using Fin.lastCases <;> simp [expected, low, wpin, Expr.size]

/-- Size of the one-row canonicality formula grows linearly with the number
of program counters and with the number of bits in a row. -/
theorem canonical_size (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) :
    (canonical (r := r) hw hp).size ≤ p * (8 * ((5+r) * ((w+1)*10+2)+2) + 2) + 1 := by
  have hcase (i : Fin p) (t : Fin 8) : (caseTest (r := r) hw hp i t).size ≤
      (5+r)*((w+1)*10+2)+1 := by
    apply allBits_size_le (s := (w+1)*10+1)
    intro j
    exact sameWord_size_le (wpin j) (expected hw hp i t j) (s := 1) (t := 1)
      (fun _ => by rfl) (expected_size hw hp i t j)
  have hor {n : ℕ} (es : Fin n → E w r) (D : ℕ) (h : ∀ i, (es i).size ≤ D) :
      (Expr.disjoin (List.ofFn es)).size ≤ n*(D+1)+1 := by
    simpa only [List.length_ofFn] using Expr.size_disjoin_le (List.ofFn es) D
      (fun _ hmem => by obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hmem; exact h i)
  exact hor _ _ (fun i => hor _ _ (hcase i))

noncomputable def canonicalFrame (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) : Frame (CodePin w r) Unit :=
  (Frame.initial (id : CodePin w r → CodePin w r)).step fun _ => canonical hw hp

/-- The actual AND/NOT gate transcript testing an arbitrary packed row. -/
theorem canonicalCircuit_at (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (defaultPC : Fin p)
    (z : Fin ((5+r)*(w+1)) → Bool) :
    ((canonicalFrame (r := r) hw hp).circuit ()).eval (fun jk => z (finProdFinEquiv jk)) = true ↔
      ∃ x, (rowFormat hw hp).encode x = z := by
  let a := (arrayBits (5+r) (w+1)).symm z
  have hpins : (fun jk => z (finProdFinEquiv jk)) = codePins a := by
    funext jk
    obtain ⟨j,k⟩ := jk
    change z (finProdFinEquiv (j,k)) = bits (a j) k
    rw [bits, Computability.VPVNP.LiveHeader.testBit_wordBits, ← arrayBits_at, Equiv.apply_symm_apply]
  rw [hpins]
  have hid : (Frame.initial (id : CodePin w r → CodePin w r)).eval (codePins a) = codePins a := funext fun j => by simp
  simp only [Frame.circuit_eval, canonicalFrame, Frame.step_eval, hid]
  rw [canonical_at hw hp defaultPC a]
  apply exists_congr
  intro x
  change _ ↔ (arrayBits (5+r) (w+1)) _ = z
  exact (arrayBits (5+r) (w+1)).eq_symm_apply

end ThreeFlat.Diagonal.TraceRows

end OAI
