import OAI.Computability.BorderVNP.DiagonalTallyRAMBroadcast

/-!
# Reading report operands through a public address vector

The public vector names one bit address per digit, from high to low. Its elements can
refer to arbitrary words in the cell's report bank. Each instruction iteration reads
the next address, reads that bit, rejects a nonbinary value and doubles the accumulator.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyGather

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

variable {w : ℕ}

/-- Public address vector and the verified Boolean digits it reaches. -/
def DigitsAt (m : Memory w) : ℕ → List Bool → Prop
  | _, [] => True
  | p, b::bs => (m (m p).val).val = b.toNat ∧ DigitsAt m (p+1) bs

/-- Natural accumulation with the most significant digit first. -/
def readDigits (a : ℕ) (bs : List Bool) : ℕ := bs.foldl (fun x b => x+x+b.toNat) a

private theorem le_readDigits (a : ℕ) (bs : List Bool) : a ≤ readDigits a bs := by
  induction bs generalizing a with
  | nil => rfl
  | cons b bs ih =>
    change a ≤ readDigits (a+a+b.toNat) bs
    exact Nat.le_trans (by omega) (ih _)

/-- Reversing an address vector for a little-endian field preserves its specified value. -/
theorem readDigits_reverse (bs : List Bool) : readDigits 0 bs.reverse = VPVNP.TapeWord.value bs := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    simp only [readDigits,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,
      VPVNP.TapeWord.value] at *
    omega

/-- Read one address and bit, and accumulate it only after checking that it is binary. -/
def digitBody : Code := .seq (.load 56 50) (.seq (.load 56 56) (.ifLt 63 56 .reject
  (.block [.binary .add 55 55 55, .binary .add 55 55 56, .binary .add 50 50 63])))

/-- Gather the bits whose addresses occupy the half-open interval in registers 50 and 52.
The value of register 55 is the accumulator. -/
def gather : Code := .whileLt 50 52 digitBody

private theorem body_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (p a : ℕ) (b : Bool)
    (hp : (s 50).val = p) (ha : (s 55).val = a) (h1 : (s 63).val = 1)
    (hb : (m (m p).val).val = b.toNat) (hval : a+a+b.toNat < 2^w) (hptr : p+1 < 2^w) :
    ∃ es t, Runs pub mac digitBody s m es t m ∧ traceCost es ≤ digitBody.slots ∧
      (t 50).val = p+1 ∧ (t 55).val = a+a+b.toNat ∧
      ∀ i : Reg, i ≠ 50 → i ≠ 55 → i ≠ 56 → t i = s i := by
  have hn : ¬ 1 < b.toNat := by cases b <;> decide
  have safe : digitBody.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp [digitBody,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,
      addressOpFits,addressOp,readings,hp,ha,h1,hb,hn,hptr,hval]
    omega
  obtain ⟨es,t,r,hc,ht⟩ := Code.runReadOnly digitBody pub mac m s safe
  have hm : readings t 50 = p+1 ∧ readings t 55 = a+a+b.toNat := by
    rw [ht]
    simp [digitBody,Code.block,Code.evalNat,Function.update,addressOp,readings,hp,ha,h1,hb,hn]
  refine ⟨es,t,r,hc,hm.1,hm.2,?_⟩
  intro i h50 h55 h56
  apply Fin.ext
  change readings t i = readings s i
  rw [ht]
  simp [digitBody,Code.block,Code.evalNat,Function.update,readings,hp,hb,h1,hn,h50,h55,h56]

/-- Genuine execution through an arbitrary address vector. It costs at most eight ticks per
bit and preserves every register outside the pointer, accumulator and bit scratch. -/
theorem gather_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (bs : List Bool) (p a stop : ℕ)
    (hp : (s 50).val = p) (ha : (s 55).val = a) (hstop : (s 52).val = stop)
    (h1 : (s 63).val = 1) (hlen : p+bs.length = stop)
    (hbits : DigitsAt m p bs) (hval : readDigits a bs < 2^w) :
    ∃ es t, Runs pub mac gather s m es t m ∧ traceCost es ≤ 8*bs.length+1 ∧
      (t 50).val = stop ∧ (t 55).val = readDigits a bs ∧
      ∀ i : Reg, i ≠ 50 → i ≠ 55 → i ≠ 56 → t i = s i := by
  induction bs generalizing s p a with
  | nil =>
    simp only [List.length_nil,Nat.add_zero] at hlen
    refine ⟨_,s,.whileDone (by change ¬(s 50).val < (s 52).val; omega), ?_,hp.trans hlen,ha,
      fun _ _ _ _ => rfl⟩
    simp [traceCost,VPVNP.RAMBuckets.cost,tick,TeamTranscript.Action.extra]
  | cons b bs ih =>
    change readDigits (a+a+b.toNat) bs < 2^w at hval
    simp only [List.length_cons] at hlen
    have hlimit : stop < 2^w := hstop ▸ (s 52).isLt
    obtain ⟨a₁,t,r,hc,htp,hta,preserve⟩ := body_runs pub mac s m p a b hp ha h1 hbits.1
      ((le_readDigits _ _).trans_lt hval) (by omega)
    obtain ⟨a₂,z,r₂,hc₂,hzp,hza,preserve₂⟩ := ih t (p+1) (a+a+b.toNat) htp hta
      (by rw [preserve 52 (by decide) (by decide) (by decide),hstop])
      (by rw [preserve 63 (by decide) (by decide) (by decide),h1])
      (by omega) hbits.2 hval
    refine ⟨_,z,.whileStep (by change (s 50).val < (s 52).val; omega) r r₂,?_,hzp,hza,
      fun i h50 h55 h56 => (preserve₂ i h50 h55 h56).trans (preserve i h50 h55 h56)⟩
    change 1+traceCost (a₁++a₂) ≤ _
    rw [show traceCost (a₁++a₂) = traceCost a₁+traceCost a₂ from VPVNP.RAMBuckets.cost_append ..]
    have hslots : digitBody.slots = 7 := by decide
    simp only [List.length_cons]; omega

end DiagonalTallyGather

end BorderVNP
end Computability
end OAI
