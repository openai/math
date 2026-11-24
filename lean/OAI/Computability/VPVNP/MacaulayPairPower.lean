import OAI.Computability.VPVNP.MacaulayPairPack

/-! # Returning the powered-row equality flag on the caller's physical ports -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.PairCall

open RAMTape UniversalCountStack

/-- Radices, scaling factor and marked coordinate for comparing a powered source monomial with
a column monomial. The comparison requests no residual coordinate. -/
def powerParams (d : Inputs) := ExponentISA.params (d.degree false) (d.degree true) d.scale d.mark 0

private def powerSource : PowerBank → Field
  | .reg i => match i.val with
    | 0 => .base false
    | 1 => .base true
    | 2 => .scale
    | 3 => .mark
    | 5 => .arity
    | 6 => .raw false
    | 7 => .raw true
    | 9 | 10 | 13 => .one
    | _ => .zero
  | _ => .zero

private def localPower : FiniteRoutine (CallBank.Port Field PowerBank) :=
  CallBank.machine powerSource (wordPorts 15) exponentRoutine [(.reg 10,.flag)] (wordPorts 15)

/-- Run the exponent comparison on the caller's pair of raw monomial codes and push its
equality flag onto the public flag stack. -/
def powerRaw : FiniteRoutine Port := localPower.onPorts (embed (Sum.inr ∘ Sum.inr))

/-- Instruction allowance for loading the exponent registers, returning the equality flag and
clearing the call bank. -/
def powerWork (w B : ℕ) := CallBank.overhead 16 1 16 B (w+(RAMTape.ISA.prepareBound w 0+3))

/-- Bound on the length of any stack during a powered-row comparison, including the caller's
stacks and the local exponent registers. -/
def powerSpace (w B : ℕ) := B+(w+(RAMTape.ISA.prepareBound w 0+3))+powerWork w B

/-- Tick bound for comparing all `t` coordinates of a powered row, including the transfers to
and from the local call bank. -/
def powerClock (t w B : ℕ) := (16*t+2)*(RAMTape.ISA.prepareBound w 0+3)+powerWork w B

/-- Test whether the column exponents equal the source exponents after incrementing the marked
coordinate, if present, and multiplying every exponent by the scale. -/
def powerMatch (d : Inputs) (a : BoundedMonomial d.arity (d.degree false)) (b : BoundedMonomial d.arity (d.degree true)) :
    Bool := decide (∀ i, ExponentISA.shifted d.scale d.mark a.val i = b.val i)

theorem powerRaw_runs {w B : ℕ} (d : Inputs)
    (a : BoundedMonomial d.arity (d.degree false)) (b : BoundedMonomial d.arity (d.degree true))
    (hfit : ExponentISA.Fits (powerParams d) w) (ht : d.arity < 2^w)
    (ha : (rawCode a).val < 2^w) (hb : (rawCode b).val < 2^w)
    (packed flag : List Bool) (hB : ∀ i, (values w d (keys w a b) packed flag i).length ≤ B) :
    ∃ n ≤ powerClock d.arity w B, powerRaw.BoundedRun (powerSpace w B) n
      (publicBank w d (keys w a b) packed flag)
      (publicBank w d (keys w a b) packed (digits w (powerMatch d a b).toNat ++ flag)) := by
  let x := values w d (keys w a b) packed flag
  let p := powerParams d
  let input : ExponentISA.Work := ⟨d.arity, (rawCode a).val, (rawCode b).val,0,true,true,0,0⟩
  have hin : CallBank.filled powerSource (wordPorts 15) x =
      RegisterTable.bank Fin.elim0 0 (ExponentISA.registers w p input) := by
    funext i
    cases i with
    | reg j =>
      have hm : (RAMTape.ISA.Port.reg j : PowerBank) ∈ wordPorts 15 := by simp [wordPorts]
      simp only [CallBank.filled, ite_eq_left hm]
      fin_cases j <;> rfl
    | persistent => simp [CallBank.filled, wordPorts, x, powerSource, values, RegisterTable.bank,
          RAMTape.ISA.bank, digits]
    | pub j => exact Fin.elim0 j
    | work j => simp [CallBank.filled, wordPorts, RegisterTable.bank, RAMTape.ISA.bank]
    | logPort j => cases j <;> simp [CallBank.filled, wordPorts, RegisterTable.bank, RAMTape.ISA.bank,
        RAMTape.ISA.logStacks, AddressLog.keys, AddressLog.values]
  obtain ⟨m,hm,out,hr,_,heq,_⟩ := exponentRoutine_runs p hfit (rawCode a).val (rawCode b).val ht ha hb
  have pos (i : Fin d.arity) : d.arity-i.rev.val = i.val+1 := by
    rw [Fin.val_rev]; have := i.isLt; omega
  have hs (i : Fin d.arity) :
      ExponentISA.scaledDigit p (d.arity-i.rev.val) ((rawCode a).val/p.sourceBase^i.rev.val) =
        ExponentISA.shifted d.scale d.mark a.val i := by
    change d.scale * ((rawCode a).val/(d.degree false+1)^i.rev.val%(d.degree false+1) +
      if d.arity-i.rev.val = d.mark then 1 else 0) = _
    rw [pos, ExponentPack.raw_digit]; rfl
  have hc (i : Fin d.arity) : (rawCode b).val/p.columnBase^i.rev.val%p.columnBase = b.val i :=
    ExponentPack.raw_digit b i
  have hflag : out.same = powerMatch d a b := by
    apply Bool.eq_iff_iff.mpr
    rw [heq, powerMatch, decide_eq_true_eq]
    constructor
    · intro h i
      simpa only [hs, hc] using h i.rev.val i.rev.isLt
    · intro h k hk
      let i : Fin d.arity := (⟨k,hk⟩ : Fin d.arity).rev
      have h' := (hs i).trans ((h i).trans (hc i).symm)
      simpa only [i, Fin.rev_rev] using h'
  let v := RegisterTable.bank Fin.elim0 0 (ExponentISA.registers w p out)
  obtain ⟨n,hn,hcall⟩ := CallBank.machine_run powerSource (wordPorts 15) exponentRoutine [(.reg 10,.flag)]
    (wordPorts 15) x _ v (wordPorts_nodup _) hB hin hr (register_empty_else _)
  have hsave : CallBank.saved v [(.reg 10,.flag)] x = values w d (keys w a b) packed (digits w (powerMatch d a b).toNat ++ flag) := by
    change Function.update (values w d (keys w a b) packed flag) .flag (digits w out.same.toNat ++ flag) = _
    rw [hflag]; exact update_flag ..
  rw [hsave] at hcall
  have lifted := lift_call (Sum.inr ∘ Sum.inr) (Sum.inr_injective.comp Sum.inr_injective) localPower hcall
  simp only [length_wordPorts, List.length_cons, List.length_nil] at hn lifted
  exact ⟨n,hn.trans (Nat.add_le_add_right hm _),lifted⟩

end RadicalCertificate.MonomialIndex.PairCall

end VPVNP
end Computability
end OAI
