import OAI.ThreeFlat.Diagonal.TraceInputSlots
import OAI.ThreeFlat.Diagonal.TraceCanonical
import OAI.ThreeFlat.Diagonal.TraceSlotFormat

namespace OAI
/-! # Header and native probe fields on the first comparator layer -/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP BurstRAM RAMSerialization TraceBanks TraceWords TraceSlots
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r : ℕ} {σ : Type*}

private abbrev W7 (σ : Type*) (b : ℕ) := Fin 7 → Fin b → Expr σ
private def literal {b : ℕ} (a : Word b) (k : Fin b) : Expr σ := .const (bits a k)

/-- Assemble the seven key words of a nonempty initialization record. -/
def initKey {b : ℕ} (a : Word b) (value : Fin b → Expr σ) : W7 σ b :=
  ![literal 0,literal a,literal 0,literal a,literal 0,literal 0,value]

theorem initKey_eval {b : ℕ} (hw : 2 ≤ b) (a v : Word b) (value : Fin b → Expr σ) (x : σ → Bool)
    (hv : ∀ k, (value k).eval x = bits v k) (j : Fin 7) (k : Fin b) :
    (initKey a value j k).eval x =
      bits (fields hw (some (⟨.init,a,v,a,0⟩ : WordRecord b)) j) k := by
  fin_cases j <;> first | exact hv _ | rfl

private def isTag (hw : 3 ≤ w+1) (pins : CodePin w r → Expr σ) (t : Fin 8) : Expr σ :=
  sameWord (fun k => pins ((0 : Fin 5).castAdd r,k)) (literal (tagWord hw t))

private def occupied (hw : 2 ≤ w+1) (pins : CodePin w r → Expr σ) (time : Word (w+1)) (rd : Bool) :
    W7 σ (w+1) :=
  ![literal 0, (fun k => pins ((3 : Fin 5).castAdd r,k)), literal (small hw 1),
    literal time, literal 0, literal (if rd then small hw 1 else small hw 2),
    (fun k => pins ((4 : Fin 5).castAdd r,k))]

/-- A CPU row supplies a read or write record when its tag selects one of
those instructions. Its other tags supply the unique padding record. -/
def probeKey (hw : 3 ≤ w+1) (pins : CodePin w r → Expr σ) (time : Word (w+1)) : W7 σ (w+1) :=
  fun j k => Expr.mux (isTag hw pins 4) (occupied (by omega) pins time true j k)
    (Expr.mux (isTag hw pins 5) (occupied (by omega) pins time false j k)
      (literal (fields (by omega) (none : Option (WordRecord (w+1))) j) k))

theorem probeKey_eval (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (pins : CodePin w r → Expr σ)
    (x : σ → Bool) (row : Row (w+1) (Snapshot w p r)) (t : Word (w+1))
    (hx : ∀ j k, (pins (j,k)).eval x = bits ((rowFormat hw hp).words row j) k)
    (j : Fin 7) (k : Fin (w+1)) :
    (probeKey hw pins t j k).eval x = bits (fields (by omega) (rowWordSlot t row) j) k := by
  have htag (tt : Fin 8) : (isTag hw pins tt).eval x = true ↔
      (header hw hp row 0) = tagWord hw tt := by
    apply sameWord_at
    · intro k
      simpa using hx ((0 : Fin 5).castAdd r) k
    · intro k
      rfl
  have haddr (n : Fin (w+1)) : (pins ((3 : Fin 5).castAdd r,n)).eval x = bits (header hw hp row 3) n := by
    simpa using hx ((3 : Fin 5).castAdd r) n
  have hdata (n : Fin (w+1)) : (pins ((4 : Fin 5).castAdd r,n)).eval x = bits (header hw hp row 4) n := by
    simpa using hx ((4 : Fin 5).castAdd r) n
  simp only [probeKey, Expr.eval_mux]
  cases row with
  | pad => simp [header, htag, tagWord, rowWordSlot, literal, Expr.eval, Fin.ext_iff]
  | halt s out => cases out <;> simp [header, htag, tagWord, rowWordSlot, literal, Expr.eval, Fin.ext_iff]
  | move s e =>
    cases e with
    | tick => simp [header, htag, tagWord, rowWordSlot, literal, Expr.eval, Fin.ext_iff]
    | choice b => cases b <;> simp [header, htag, tagWord, rowWordSlot, literal, Expr.eval, Fin.ext_iff]
    | read a v | write a v =>
      simp only [header] at htag haddr hdata
      fin_cases j <;> simp [htag, tagWord, occupied, literal, rowWordSlot, fields, Expr.eval,
        haddr, hdata, Fin.ext_iff]

/-- A selected output bit of an initialization key can observe only the
corresponding input bit of the public address. -/
theorem initKey_bit_congr {b : ℕ} (value : Fin b → Expr σ) (x : σ → Bool)
    (a a' : Word b) (j : Fin 7) (k : Fin b) (h : bits a k = bits a' k) :
    (initKey a value j k).eval x = (initKey a' value j k).eval x := by
  fin_cases j <;> first | exact h | rfl

/-- A probe's selected output bit can observe only that same bit of its timestamp,
regardless of the CPU input, including invalid CPU words. -/
theorem probeKey_bit_congr (hw : 3 ≤ w+1) (pins : CodePin w r → Expr σ) (x : σ → Bool)
    (t t' : Word (w+1)) (j : Fin 7) (k : Fin (w+1)) (h : bits t k = bits t' k) :
    (probeKey hw pins t j k).eval x = (probeKey hw pins t' j k).eval x := by
  have ho (rd : Bool) : (occupied (by omega) pins t rd j k).eval x =
      (occupied (by omega) pins t' rd j k).eval x := by
    fin_cases j <;> first | exact h | rfl
  simp only [probeKey, Expr.eval_mux, ho]

/-- Each initialized key bit is a single constant or a direct header input. -/
theorem initKey_size {b : ℕ} (a : Word b) (value : Fin b → Expr σ)
    (hv : ∀ j, (value j).size ≤ 1) (j : Fin 7) (k : Fin b) :
    (initKey a value j k).size ≤ 1 := by
  fin_cases j <;> first | exact hv _ | rfl

/-- Reading the two tag selectors is the only word-length part of each probe bit. -/
theorem probeKey_size (hw : 3 ≤ w+1) (pins : CodePin w r → Expr σ) (time : Word (w+1))
    (hp : ∀ j, (pins j).size ≤ 1) (j : Fin 7) (k : Fin (w+1)) :
    (probeKey hw pins time j k).size ≤ 56*(w+2) := by
  have htag (t : Fin 8) : (isTag hw pins t).size ≤ (w+1)*10+1 :=
    sameWord_size_le _ _ (s := 1) (t := 1) (fun j => hp ((0 : Fin 5).castAdd r,j)) (fun _ => by rfl)
  have hocc (rd : Bool) : (occupied (by omega) pins time rd j k).size ≤ 1 := by
    fin_cases j <;> first | exact hp _ | rfl
  have h4 := htag 4
  have h5 := htag 5
  have hr := hocc true
  have hw' := hocc false
  simp only [probeKey, Expr.mux, Expr.size, literal]
  omega

end ThreeFlat.Diagonal.TraceRows

end OAI
