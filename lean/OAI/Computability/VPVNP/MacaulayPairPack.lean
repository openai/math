import OAI.Computability.VPVNP.MacaulayOrdinalCall

/-! # Staging the residual packer with preserved caller inputs -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.PairCall

open RAMTape UniversalCountStack

private def packSource : ExponentPack.Port → Field
  | .inl (.reg i) => match i.val with
    | 0 => .base false
    | 1 => .base true
    | 2 => .raw false
    | 3 => .raw true
    | 4 => .one
    | _ => .zero
  | .inr .marker => .marker
  | _ => .zero

private def packInputs : List ExponentPack.Port := (wordPorts 10).map Sum.inl ++ [.inr .marker]

private def packWipe : List ExponentPack.Port := .inr .packed :: packInputs

private def packOutputs : List (ExponentPack.Port × Field) := [(.inr .packed,.packed), (.inl (.reg 4),.flag)]

private def localPack : FiniteRoutine (CallBank.Port Field ExponentPack.Port) :=
  CallBank.machine packSource packInputs ExponentPack.machine packOutputs packWipe

/-- Run the staged residual-exponent routine on the two raw keys and return the packed
differences and divisibility flag to their caller stacks. -/
def packRaw : FiniteRoutine Port := localPack.onPorts (embed (Sum.inr ∘ Sum.inl))

/-- Tick bound for one comparison and residual-word copy per variable, including the loop
tests. -/
def packTicks (t w : ℕ) := t*(ExponentPack.bodyCost w+1)+1

/-- Private stack-height bound for the residual packer, accounting for register width, the
unary marker and the work of all iterations. -/
def packInnerSpace (t w : ℕ) := max w t + packTicks t w

/-- Copying and cleanup allowance for the packer's twelve input stacks, two returned outputs
and thirteen cleared private stacks. -/
def packWork (t w B : ℕ) := CallBank.overhead 12 2 13 B (packInnerSpace t w)

/-- Stack bound for the whole staged packer call, including the caller, private working space
and copy overhead. -/
def packSpace (t w B : ℕ) := B+packInnerSpace t w+packWork t w B

/-- Tick bound for staging the packer, running all variable iterations and returning the two
outputs. -/
def packClock (t w B : ℕ) := packTicks t w+packWork t w B

/-- The source and column raw graded monomial codes as fixed-width little-endian bit stacks. -/
def keys {t L D : ℕ} (w : ℕ) (a : BoundedMonomial t L) (b : BoundedMonomial t D) : Bool → List Bool
  | false => digits w (rawCode a).val
  | true => digits w (rawCode b).val

/-- Packed exponent vector obtained by coordinatewise truncated subtraction of the source
monomial from the column monomial. -/
def difference {t L D : ℕ} (w : ℕ) (a : BoundedMonomial t L) (b : BoundedMonomial t D) : List Bool :=
  ExponentPack.packed w (List.ofFn (fun i => b.val i - a.val i))

theorem packRaw_runs {w B : ℕ} (d : Inputs)
    (a : BoundedMonomial d.arity (d.degree false)) (b : BoundedMonomial d.arity (d.degree true))
    (fitS : ISA.Fits (ISA.graded d.arity (d.degree false) (d.ordinal false)) w)
    (fitC : ISA.Fits (ISA.graded d.arity (d.degree true) (d.ordinal true)) w)
    (packed flag : List Bool) (hB : ∀ i, (values w d (keys w a b) packed flag i).length ≤ B) :
    ∃ n ≤ packClock d.arity w B, packRaw.BoundedRun (packSpace d.arity w B) n
      (publicBank w d (keys w a b) packed flag)
      (publicBank w d (keys w a b) (difference w a b ++ packed) (digits w (decide (a.val ≤ b.val)).toNat ++ flag)) := by
  let x := values w d (keys w a b) packed flag
  let R₀ := ExponentPack.initial w (d.degree false) (d.degree true) (rawCode a).val (rawCode b).val
  have hin : CallBank.filled packSource packInputs x = ExponentPack.frame R₀ d.arity [] := by
    funext i
    rcases i with i | s
    · cases i with
      | reg j =>
        have hm : (Sum.inl (.reg j) : ExponentPack.Port) ∈ packInputs := by simp [packInputs, wordPorts]
        simp only [CallBank.filled, ite_eq_left hm]
        fin_cases j <;> rfl
      | persistent => simp [CallBank.filled, packInputs, wordPorts, packSource, x, values,
          ExponentPack.frame, RAMTape.ISA.bank, digits]
      | pub j => exact Fin.elim0 j
      | work j => simp [CallBank.filled, packInputs, wordPorts, ExponentPack.frame, RAMTape.ISA.bank]
      | logPort j => cases j <;> simp [CallBank.filled, packInputs, wordPorts, ExponentPack.frame,
          RAMTape.ISA.bank, RAMTape.ISA.logStacks, AddressLog.keys, AddressLog.values]
    · cases s <;> simp [CallBank.filled, packInputs, packSource, x, values, ExponentPack.frame]
  obtain ⟨t,ht,R,hcore,hflag⟩ := ExponentPack.pack_rows_bounded a b fitS.limit_lt.le fitC.limit_lt.le
    fitS.base_lt fitC.base_lt []
  simp only [List.append_nil, List.length_nil, Nat.max_zero] at hcore
  let v := ExponentPack.frame R 0 (difference w a b)
  have hc : ExponentPack.machine.BoundedRun (packInnerSpace d.arity w) t
      (ExponentPack.frame R₀ d.arity []) v := hcore
  have hz (i : ExponentPack.Port) (hi : i ∉ packWipe) : v i = [] := by
    rcases i with i | s
    · apply register_empty_else R
      exact fun he => hi (by simp [packWipe, packInputs, he])
    · cases s <;> simp_all [packWipe, packInputs, v, ExponentPack.frame]
  obtain ⟨n,hn,hr⟩ := CallBank.machine_run packSource packInputs ExponentPack.machine packOutputs packWipe
    x _ v (by decide) hB hin hc hz
  have hsave : CallBank.saved v packOutputs x = values w d (keys w a b) (difference w a b ++ packed)
      (digits w (decide (a.val ≤ b.val)).toNat ++ flag) := by
    change Function.update (Function.update (values w d (keys w a b) packed flag) .packed _) .flag _ = _
    rw [update_packed]
    change Function.update (values w d (keys w a b) (difference w a b ++ packed) flag)
      .flag (BurstRAM.wordBits (R 4) ++ flag) = _
    rw [hflag]
    exact update_flag ..
  rw [hsave] at hr
  have lifted := lift_call (Sum.inr ∘ Sum.inl) (Sum.inr_injective.comp Sum.inl_injective) localPack hr
  simp only [packInputs, packOutputs, packWipe, List.length_append, List.length_map, length_wordPorts,
    List.length_cons, List.length_nil] at hn lifted
  exact ⟨n,hn.trans (Nat.add_le_add_right ht _),lifted⟩

end RadicalCertificate.MonomialIndex.PairCall

end VPVNP
end Computability
end OAI
