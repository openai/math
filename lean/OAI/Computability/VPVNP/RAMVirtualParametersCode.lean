import OAI.Computability.VPVNP.RAMVirtualCeilLog
import OAI.Computability.VPVNP.RAMVirtualParameterBounds
import OAI.Computability.VPVNP.PrimedInputRAMOnce
import OAI.Computability.VPVNP.PrimedStackRAMNodeTable

/-!
# Computing the virtual site count on the private word RAM

The public words give the input length and live address width. Two ceiling
logarithms suffice to compute the least virtual site count and its bucket
size in Section 11. All iterations and arithmetic fit in a live word.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.VirtualParameters

open PrivateRAM PrimedInputRAM PrimedStackRAM

variable {w k : ℕ}

private def setup (pn pr : Fin k) : Flow 12 k :=
  straight (.constant 0 1) [.constant 1 2, .publicWord 4 pn, .publicWord 5 pr, .copy 2 4, .constant 3 0]

private def product : Flow 12 k :=
  straight (.copy 6 3) [.binary .mul 2 4 6, .constant 3 0]

private def finish : Flow 12 k :=
  straight (.constant 7 3) [.binary .add 8 1 1, .binary .add 9 6 7, .binary .div 9 9 8,
    .binary .add 10 5 3, .binary .sub 10 10 9, .binary .shiftLeft 7 0 9, .binary .shiftLeft 11 0 10]

/-- Fixed finite instruction text, with the length and address-width public slots supplied by the caller. -/
def program (pn pr : Fin k) : Flow 12 k :=
  .seq (setup pn pr) (.seq clogLoop (.seq product (.seq clogLoop finish)))

/-- Number of executed instructions, including the final test of each loop. -/
def ticks (n : ℕ) : ℕ := 4 * Nat.clog 2 n + 4 * Nat.clog 2 (n * Nat.clog 2 n) + 19

theorem ticks_le (n : ℕ) : ticks n ≤ 12 * Nat.clog 2 n + 19 := by
  unfold ticks
  have := clog_length_mul_clog_le n
  omega

/-- Integer parameters in the final register file, including both powers of two. -/
structure Result (n r : ℕ) (out : Regs w 12) : Prop where
  inputLength : (out 4).val = n
  addressBits : (out 5).val = r
  lengthLog : (out 6).val = Nat.clog 2 n
  bucket : (out 7).val = 2 ^ roundedUp 1 4 n
  four : (out 8).val = 4
  bucketBits : (out 9).val = roundedUp 1 4 n
  siteBits : (out 10).val = virtualSiteExponent r n
  sites : (out 11).val = 2 ^ virtualSiteExponent r n

private abbrev literal (w a : ℕ) : Word w := Fin.ofNat _ a

private def load (pub : Fin k → Word w) (pn pr : Fin k) (rs : Regs w 12) : Regs w 12 :=
  let fields : List (Fin 12 × Word w) := [(0, literal w 1), (1, literal w 2),
    (4, pub pn), (5, pub pr), (2, pub pn), (3, literal w 0)]
  fields.foldl (fun a j => Function.update a j.1 j.2) rs

private def prepare (rs : Regs w 12) : Regs w 12 :=
  Function.update (Function.update (Function.update rs (6 : Fin 12) (rs 3))
    2 (BinaryOp.mul.eval (rs 4) (rs 3))) 3 (literal w 0)

private theorem power_value (one exp : Word w) (h : one.val = 1) (he : exp.val < w) :
    (BinaryOp.shiftLeft.eval one exp).val = 2 ^ exp.val := by
  have hfit : 2 ^ exp.val < 2 ^ w := Nat.pow_lt_pow_right Nat.one_lt_two he
  simp [BinaryOp.eval, he, Nat.shiftLeft_eq, h, Nat.mod_eq_of_lt hfit]

private def finishRegs (rs : Regs w 12) : Regs w 12 :=
  let three := literal w 3
  let four := BinaryOp.add.eval (rs 1) (rs 1)
  let num := BinaryOp.add.eval (rs 6) three
  let q := BinaryOp.div.eval num four
  let sum := BinaryOp.add.eval (rs 5) (rs 3)
  let width := BinaryOp.sub.eval sum q
  let fields : List (Fin 12 × Word w) := [(7,three),(8,four),(9,num),(9,q),(10,sum),(10,width),
    (7,BinaryOp.shiftLeft.eval (rs 0) q),(11,BinaryOp.shiftLeft.eval (rs 0) width)]
  fields.foldl (fun a j => Function.update a j.1 j.2) rs

private theorem finishValues (n r : ℕ) (hn : 2 ≤ n) (rs : Regs w 12)
    (hOne : (rs 0).val = 1) (hTwo : (rs 1).val = 2)
    (hnat : (rs 4).val = n) (hr : (rs 5).val = r) (hc : (rs 6).val = Nat.clog 2 n)
    (hd : (rs 3).val = Nat.clog 2 (n * Nat.clog 2 n))
    (hcr : Nat.clog 2 n ≤ r) (hwidth : 3 * r + 4 ≤ w)
    (hnum : Nat.clog 2 n + 3 < 2 ^ w) (hsum : r + Nat.clog 2 (n * Nat.clog 2 n) < 2 ^ w) :
    Result n r (finishRegs rs) := by
  let three := literal w 3
  let four := BinaryOp.add.eval (rs 1) (rs 1)
  let num := BinaryOp.add.eval (rs 6) three
  let q := BinaryOp.div.eval num four
  let sum := BinaryOp.add.eval (rs 5) (rs 3)
  let width := BinaryOp.sub.eval sum q
  have hclog := Nat.clog_pos Nat.one_lt_two (by omega : 1 < n)
  have hw := Nat.lt_two_pow_self (n := w)
  have hthree : three.val = 3 := Nat.mod_eq_of_lt (by omega)
  have hfour : four.val = 4 := by
    change ((rs 1) + (rs 1)).val = 4
    rw [Fin.val_add_eq_of_add_lt (by omega), hTwo]
  have htop : num.val = Nat.clog 2 n + 3 := by
    change (rs 6 + three).val = _
    rw [Fin.val_add_eq_of_add_lt (by omega), hc, hthree]
  have hq : q.val = (Nat.clog 2 n + 3) / 4 := by
    have hdiv : q.val = num.val / four.val := Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt num.isLt)
    rw [hdiv, htop, hfour]
  have hval : sum.val = r + Nat.clog 2 (n * Nat.clog 2 n) := by
    change (rs 5 + rs 3).val = _
    rw [Fin.val_add_eq_of_add_lt (by omega), hr, hd]
  have hb : q.val = roundedUp 1 4 n := by
    rw [hq, roundedUp, pow_one, Nat.clog_pow_left]
  have hd' : width.val = virtualSiteExponent r n := by
    change (sum - q).val = _
    rw [Fin.sub_val_of_le (show q ≤ sum by change q.val ≤ sum.val; omega), hval,
      virtualSiteExponent_eq_add_sub _ _ hn, hq]
  have hlim := clog_length_mul_clog_le n
  have hqfit : q.val < w := by omega
  have hdfit : width.val < w := by rw [hd', virtualSiteExponent_eq_add_sub _ _ hn]; omega
  constructor
  · exact hnat
  · exact hr
  · exact hc
  · change (BinaryOp.shiftLeft.eval (rs 0) q).val = _
    rw [power_value _ _ hOne hqfit, hb]
  · exact hfour
  · exact hb
  · exact hd'
  · change (BinaryOp.shiftLeft.eval (rs 0) width).val = _
    rw [power_value _ _ hOne hdfit, hd']

private theorem seqTicks {pub : Fin k → Word w} {state : Word w} {m : Memory w}
    {a b : Flow 12 k} {rs mid out : Regs w 12} {j t : ℕ}
    (ha : Flow.Exec pub state a rs m (List.replicate j .tick) mid m)
    (hb : Flow.Exec pub state b mid m (List.replicate t .tick) out m) :
    Flow.Exec pub state (.seq a b) rs m (List.replicate (j+t) .tick) out m := by
  simpa only [List.replicate_add] using ha.seq hb

/-- Executing the fixed word program computes the prescribed virtual parameters
for each length at least two and each live address multiplier at least one. -/
theorem programRun (pub : Fin k → Word w) (pn pr : Fin k) (state : Word w) (m : Memory w)
    (rs : Regs w 12) (B n : ℕ) (hB : 1 ≤ B) (hn : 2 ≤ n)
    (hw : w = (addressWidth B n + 10) ^ 4) (hnat : (pub pn).val = n)
    (hr : (pub pr).val = addressWidth B n) :
    ∃ out, Flow.Exec pub state (program pn pr) rs m (List.replicate (ticks n) .tick) out m ∧
      Result n (addressWidth B n) out := by
  let r := addressWidth B n
  let c := Nat.clog 2 n
  let d := Nat.clog 2 (n * c)
  have hcr : c ≤ r := Nat.le_mul_of_pos_left _ hB
  have hc : 0 < c := Nat.clog_pos Nat.one_lt_two (by omega)
  have hwidth : 3 * r + 4 ≤ w := by
    rw [hw]
    calc
      _ ≤ (r + 10)^2 := by nlinarith [Nat.zero_le (r * r)]
      _ ≤ (r + 10)^4 := Nat.pow_le_pow_right (by omega) (by decide)
  obtain ⟨hprod, hsum, hnum⟩ := virtualParameterOperands_lt hB n
  change n * c + 1 < 2 ^ (r + 10) ^ 4 at hprod
  change r + d < 2 ^ (r + 10) ^ 4 at hsum
  change c + 3 < 2 ^ (r + 10) ^ 4 at hnum
  change w = (r + 10) ^ 4 at hw
  rw [← hw] at hprod hsum hnum
  have hsmall : n + 1 < 2 ^ w := by have := Nat.le_mul_of_pos_right n hc; omega
  let start := load pub pn pr rs
  have hstart : Flow.Exec pub state (setup pn pr) rs m (List.replicate 6 .tick) start m :=
    (Flow.once_sound pub state false _ rs m rfl).1
  have h₀ : (start 0).val = 1 := Nat.mod_eq_of_lt (by omega)
  have h₁ : (start 1).val = 2 := Nat.mod_eq_of_lt (by omega)
  obtain ⟨a, run₁, _, count₁, keep₁⟩ := clogRun pub state m n start h₀ h₁ hnat
    (show (start 3).val = 0 from Nat.zero_mod _) hsmall (by change c < 2 ^ w; omega)
  have haOne := (congrArg Fin.val (keep₁ 0 (by decide) (by decide))).trans h₀
  have haTwo := (congrArg Fin.val (keep₁ 1 (by decide) (by decide))).trans h₁
  have haN : (a 4).val = n := (congrArg Fin.val (keep₁ 4 (by decide) (by decide))).trans hnat
  have haR : (a 5).val = r := (congrArg Fin.val (keep₁ 5 (by decide) (by decide))).trans hr
  let b := prepare a
  have hmiddle : Flow.Exec pub state product a m (List.replicate 3 .tick) b m :=
    (Flow.once_sound pub state false _ a m rfl).1
  have hbProd : (b 2).val = n * c := by
    change ((a 4).val * (a 3).val) % (2 ^ w) = n * c
    rw [haN, count₁, Nat.mod_eq_of_lt (by change n * c < 2 ^ w; omega)]
  obtain ⟨z, run₂, _, count₂, keep₂⟩ := clogRun pub state m (n*c) b haOne haTwo hbProd
    (show (b 3).val = 0 from Nat.zero_mod _) hprod (by change d < 2 ^ w; omega)
  have hend : Flow.Exec pub state finish z m (List.replicate 8 .tick) (finishRegs z) m :=
    (Flow.once_sound pub state false _ z m rfl).1
  refine ⟨finishRegs z, ?_, finishValues n r hn z ?_ ?_ ?_ ?_ ?_ count₂ hcr hwidth hnum hsum⟩
  · change Flow.Exec pub state _ rs m (List.replicate (4*c+4*d+19) .tick) _ m
    rw [show 4*c+4*d+19 = 6 + ((4*c+1) + (3 + ((4*d+1)+8))) by omega]
    exact seqTicks hstart (seqTicks run₁ (seqTicks hmiddle (seqTicks run₂ hend)))
  · exact (congrArg Fin.val (keep₂ 0 (by decide) (by decide))).trans haOne
  · exact (congrArg Fin.val (keep₂ 1 (by decide) (by decide))).trans haTwo
  · exact (congrArg Fin.val (keep₂ 4 (by decide) (by decide))).trans haN
  · exact (congrArg Fin.val (keep₂ 5 (by decide) (by decide))).trans haR
  · exact (congrArg Fin.val (keep₂ 6 (by decide) (by decide))).trans count₁

private theorem choiceBits_ticks (t : ℕ) : choiceBits (List.replicate t (.tick : Event w)) = [] := by
  induction t with
  | zero => rfl
  | succ t ih => simp [List.replicate_succ, choiceBits, ih]

/-- A linked occurrence transfers control to its continuation with the computed
registers, the same branch bits, and the private and external memories it received. -/
theorem programExecute {p : ℕ} (M : Machine w p 12 k) (pn pr : Fin k) (state : Word w)
    (priv : Word w → Word w) (m : Memory w) (rs : Regs w 12) (B n : ℕ) (hB : 1 ≤ B)
    (hn : 2 ≤ n) (hw : w = (addressWidth B n + 10) ^ 4) (hnat : (M.publicData pn).val = n)
    (hr : (M.publicData pr).val = addressWidth B n) (label : (program pn pr).Label → Fin p)
    (stop bad : Fin p) (hl : Flow.Linked M (program pn pr) label stop bad)
    (hb : M.code bad = .reject) :
    ∃ out, Result n (addressWidth B n) out ∧ ∀ fuel bits,
      execute M.program (ticks n + fuel) ⟨label (program pn pr).entry, state, rs, priv⟩ m bits =
        (execute M.program fuel ⟨stop, state, out, priv⟩ m bits).map
          (Flow.prependEvents (List.replicate (ticks n) .tick)) := by
  obtain ⟨out, run, result⟩ := programRun M.publicData pn pr state m rs B n hB hn hw hnat hr
  refine ⟨out, result, fun fuel bits => ?_⟩
  simpa only [List.length_replicate, choiceBits_ticks, List.nil_append] using run.execute hl hb priv fuel bits

end BurstRAM.VirtualParameters

end VPVNP
end Computability
end OAI
