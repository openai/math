import OAI.Computability.VPVNP.PairNativeGeometryFields
import OAI.Computability.VPVNP.RAMSiteBounds

/-!
# Loading live geometry inside a pair simulation burst

The eleven public words of the pair include the live length and address width
at slots six and seven, and the literal prefix and its length at slots zero
and one. The remaining geometry comes from bounded register arithmetic with
the fixed numerator and denominator chosen for this live evaluator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairNativeGeometry
open BurstRAM PrivateRAM PrimedInputRAM PrimedStackRAM Filter

variable {w : ℕ}

private def setup : Code := straight (.constant 0 1) [.constant 1 2,.publicWord 4 6,.publicWord 5 7,
  .constant 3 0,.publicWord 8 1,.publicWord 9 0]

private def load (pub : Fin 11 → Word w) (rs : Regs w 12) :=
  ([(0,Fin.ofNat (2^w) 1),(1,Fin.ofNat (2^w) 2),(4,pub 6),(5,pub 7),(3,Fin.ofNat (2^w) 0),
    (8,pub 1),(9,pub 0)] : List (Register × Word w)).foldl (fun x j => Function.update x j.1 j.2) rs

/-- Load the live length, address width and literal prefix from the pair's public words, then
compute the word width and rounded bucket size in registers. -/
def program (a b : ℕ) : Code := .seq setup (.seq widthCode
  (.seq (power 2 4 a) (.seq VirtualParameters.clogLoop (bucketCode b))))

/-- Exact tick count for loading the geometry, including the power computation and the
ceiling-logarithm loop on `n^a`. -/
def ticks (a b n : ℕ) := 7 + (17 + ((a+1) + ((4*Nat.clog 2 (n^a)+1)+(b+4))))

theorem clog_power_le (a n : ℕ) : Nat.clog 2 (n^a) ≤ a * Nat.clog 2 n := by
  apply Nat.clog_le_of_le_pow
  rw [Nat.mul_comm, pow_mul]
  exact Nat.pow_le_pow_left (Nat.le_pow_clog Nat.one_lt_two n) a

/-- For fixed ratio the arithmetic takes at most linearly many instructions
in the bit length, including the final loop test. -/
theorem ticks_le (a b n : ℕ) : ticks a b n ≤ 4*a*(n.log2+1) + a+b+30 := by
  have h := (clog_power_le a n).trans (Nat.mul_le_mul_left a (clog_le_log2_succ n))
  have := Nat.mul_le_mul_left 4 h
  unfold ticks
  rw [Nat.mul_assoc]
  omega

/-- Bounds on the power, denominator, rounded numerator and shift count that make the bucket
computation exact in `w`-bit registers. -/
structure Fits (a b n w : ℕ) : Prop where
  power : n^a+1 < 2^w
  denominator : b < 2^w
  numerator : Nat.clog 2 (n^a)+(b-1) < 2^w
  shift : roundedUp a b n < w

/-- All register bounds hold uniformly at every sufficiently large length
for each fixed choice of the two exponents and address multiplier. -/
theorem eventually_fits (a b B : ℕ) (hB : 1 ≤ B) :
    ∀ᶠ n : ℕ in atTop, Fits a b n ((addressWidth B n + 10)^4) := by
  filter_upwards [eventually_polynomial_lt_wordModulus (a+1), eventually_ge_atTop (2^(a+b+2))] with n hp hn
  let r := addressWidth B n
  let w := (r+10)^4
  have htwo : 2 ≤ n := (Nat.pow_le_pow_right (by decide : 0 < 2) (show 1 ≤ a+b+2 by omega)).trans hn
  have hr : n.log2 ≤ r := log2_le_addressWidth hB n
  have hbig := ((Nat.le_log2 (by omega : n ≠ 0)).mpr hn).trans hr
  have hcr : Nat.clog 2 n ≤ r := Nat.le_mul_of_pos_left _ hB
  have hlog := (clog_power_le a n).trans (Nat.mul_le_mul_left a hcr)
  have htop : a*r+b+1 ≤ w := by
    calc
      _ ≤ (r+10)^2 := by nlinarith [Nat.mul_le_mul_right r (show a ≤ r by omega)]
      _ ≤ _ := Nat.pow_le_pow_right (by omega : 0 < r+10) (by decide : 2 ≤ 4)
  have hmod : w < 2^w := Nat.lt_two_pow_self
  have hpow := hp r hr
  have hmono := Nat.mul_le_mul_left (n^a) htwo
  have hpos := Nat.pow_pos (by omega : 0 < n) (n := a)
  change Fits a b n w
  refine ⟨?_,by omega,by omega,?_⟩
  · change n^(a+1) < 2^w at hpow
    rw [pow_succ] at hpow; omega
  · rw [roundedUp,Nat.clog_pow_left]
    exact (Nat.div_le_self _ _).trans_lt (by omega)

/-- Postcondition for the geometry loader. Registers 4 through 7 hold the length, address
width, word width and bucket size, and registers 8 and 9 hold the public prefix length and
word. -/
structure Result (pub : Fin 11 → Word w) (a b n r : ℕ) (out : Regs w 12) : Prop where
  length : (out 4).val = n
  address : (out 5).val = r
  width : (out 6).val = w
  bucket : (out 7).val = 2^roundedUp a b n
  prefixLength : out 8 = pub 1
  prefixWord : out 9 = pub 0

theorem program_run (pub : Fin 11 → Word w) (state : Word w) (m : Memory w) (rs : Regs w 12)
    (a b n r : ℕ) (hb : 0 < b) (hn : 0 < n) (hw : w = (r+10)^4) (hf : Fits a b n w)
    (h6 : (pub 6).val = n) (h7 : (pub 7).val = r) :
    ∃ out, Flow.Exec pub state (program a b) rs m (List.replicate (ticks a b n) .tick) out m ∧
      Result pub a b n r out := by
  let s := load pub rs
  have hstart : Flow.Exec pub state setup rs m (List.replicate 7 .tick) s m :=
    (Flow.once_sound pub state false _ rs m rfl).1
  have hlarge : 10 ≤ w := by
    rw [hw]; exact (show 10 ≤ r+10 by omega).trans (Nat.le_self_pow (by decide) _)
  have hmod : w < 2^w := Nat.lt_two_pow_self
  have hsOne : (s 0).val = 1 := Nat.mod_eq_of_lt (by omega)
  have hsTwo : (s 1).val = 2 := Nat.mod_eq_of_lt (by omega)
  obtain ⟨t,width,hwval,keepT⟩ := width_run pub state m s r h7 hw hsOne
  have htN : (t 4).val = n := (congrArg Fin.val (keepT 4 (by decide) (by decide))).trans h6
  have hp : n^a < 2^w := Nat.lt_trans (Nat.lt_succ_self _) hf.power
  let u := Function.update t (2 : Register) (⟨n^a,hp⟩ : Word w)
  have hpow := power_run pub state m t 2 4 (by decide) n htN hn a hp
  have keepU (j : Register) (h2 : j ≠ 2) : u j = t j := Function.update_of_ne h2 ..
  have uone : (u 0).val = 1 := (congrArg Fin.val ((keepU 0 (by decide)).trans (keepT _ (by decide) (by decide)))).trans hsOne
  have utwo : (u 1).val = 2 := (congrArg Fin.val ((keepU 1 (by decide)).trans (keepT _ (by decide) (by decide)))).trans hsTwo
  have uzero : (u 3).val = 0 := by rw [keepU 3 (by decide),keepT 3 (by decide) (by decide)]; exact Nat.zero_mod _
  have hlog : Nat.clog 2 (n^a) < 2^w := (Nat.le_add_right ..).trans_lt hf.numerator
  obtain ⟨v,run,_,clog,keepV⟩ := VirtualParameters.clogRun pub state m (n^a) u uone utwo
    (by simp [u]) uzero hf.power hlog
  obtain ⟨out,finish,bucket,keep⟩ := bucket_run pub state m v a b n hb
    ((congrArg Fin.val (keepV 0 (by decide) (by decide))).trans uone) clog hf.denominator hf.numerator hf.shift
  have preserved (j : Register) (h2 : j ≠ 2) (h3 : j ≠ 3) (h7 : j ≠ 7) (h10 : j ≠ 10) (h11 : j ≠ 11) :
      out j = t j := ((keep j h7 h10 h11).trans (keepV j h2 h3)).trans (keepU j h2)
  refine ⟨out,seqTicks hstart (seqTicks width (seqTicks hpow (seqTicks run finish))),?_⟩
  constructor
  · exact (congrArg Fin.val (preserved 4 (by decide) (by decide) (by decide) (by decide) (by decide))).trans htN
  · rw [preserved 5 (by decide) (by decide) (by decide) (by decide) (by decide),keepT 5 (by decide) (by decide)]
    exact h7
  · rw [preserved 6 (by decide) (by decide) (by decide) (by decide) (by decide)]; exact hwval
  · exact bucket
  · rw [preserved 8 (by decide) (by decide) (by decide) (by decide) (by decide),keepT 8 (by decide) (by decide)]; rfl
  · rw [preserved 9 (by decide) (by decide) (by decide) (by decide) (by decide),keepT 9 (by decide) (by decide)]; rfl

/-- In any linked occurrence, loading the pair geometry consumes only ticks.
The continuation receives the original memories and choice stream. -/
theorem program_execute {p : ℕ} (M : Machine w p 12 11) (state : Word w)
    (priv : Word w → Word w) (m : Memory w) (rs : Regs w 12) (a b n r : ℕ)
    (hb : 0 < b) (hn : 0 < n) (hw : w = (r+10)^4) (hf : Fits a b n w)
    (h6 : (M.publicData 6).val = n) (h7 : (M.publicData 7).val = r)
    (label : (program a b).Label → Fin p) (stop bad : Fin p)
    (hl : Flow.Linked M (program a b) label stop bad) (hbad : M.code bad = .reject) :
    ∃ out, Result M.publicData a b n r out ∧ ∀ fuel bits,
      execute M.program (ticks a b n + fuel) ⟨label (program a b).entry,state,rs,priv⟩ m bits =
        (execute M.program fuel ⟨stop,state,out,priv⟩ m bits).map
          (Flow.prependEvents (List.replicate (ticks a b n) .tick)) := by
  obtain ⟨out,run,done⟩ := program_run M.publicData state m rs a b n r hb hn hw hf h6 h7
  have choices (t : ℕ) : choiceBits (List.replicate t (.tick : Event w)) = [] := by
    induction t with
    | zero => rfl
    | succ t ih => simp [List.replicate_succ,choiceBits,ih]
  refine ⟨out,done,fun fuel bits => ?_⟩
  simpa only [List.length_replicate,choices,List.nil_append] using run.execute hl hbad priv fuel bits

end PairNativeGeometry

end VPVNP
end Computability
end OAI
