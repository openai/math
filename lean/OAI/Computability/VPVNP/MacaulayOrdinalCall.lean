import OAI.Computability.VPVNP.MacaulayPairPorts

/-! # A returning raw-key lookup which preserves the caller's ordinal and advice -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RadicalCertificate.MonomialIndex.PairCall

open RAMTape UniversalCountStack

/-- Between register instructions only the register and persistent ports
can be occupied. The instruction work ports and private log are empty. -/
def wordPorts (r : ℕ) : List (RAMTape.ISA.Port r 0) :=
  .persistent :: (List.finRange r).map .reg

theorem wordPorts_nodup (r : ℕ) : (wordPorts r).Nodup := by
  simp [wordPorts, List.Nodup.map (fun _ _ h => RAMTape.ISA.Port.reg.inj h) (List.nodup_finRange r)]

theorem length_wordPorts (r : ℕ) : (wordPorts r).length = r+1 := by simp [wordPorts]

theorem register_empty_else {r w : ℕ} (R : Fin r → BurstRAM.Word w) (i : RAMTape.ISA.Port r 0)
    (hi : i ∉ wordPorts r) : RegisterTable.bank Fin.elim0 0 R i = [] := by
  cases i with
  | reg j => simp [wordPorts] at hi
  | persistent => simp [wordPorts] at hi
  | pub j => exact Fin.elim0 j
  | work => rfl
  | logPort j => cases j <;> rfl

private def ordinalSource (column : Bool) : OrdBank → Field
  | .reg i => match i.val with
    | 0 => .base column
    | 1 => .arity
    | 2 => .box column
    | 3 => .limit column
    | 4 => .ordinal column
    | 11 => .one
    | _ => .zero
  | _ => .zero

private def singleOrdinal (c : Bool) : FiniteRoutine (CallBank.Port Field OrdBank) :=
  CallBank.machine (ordinalSource c) (wordPorts 13) ordinalRoutine [(.reg 5,.raw c)] (wordPorts 13)

/-- Return the raw key of the requested source or column monomial while preserving the caller's
ordinal and parameter words. -/
def ordinal (c : Bool) : FiniteRoutine Port := (singleOrdinal c).onPorts (embed Sum.inl)

/-- Time allowance for copying the ordinal scan's input words, returning its raw key and
clearing the private scan bank. -/
def ordinalWork (w B : ℕ) := CallBank.overhead 14 1 14 B (w+(RAMTape.ISA.prepareBound w 0+3))

/-- Stack allowance for staging and running one ordinal scan with register width w and caller
stacks bounded by B. -/
def ordinalSpace (w B : ℕ) := B+(w+(RAMTape.ISA.prepareBound w 0+3))+ordinalWork w B

/-- Tick bound for a complete bounded-degree ordinal search, including the private call's input
and output copies. -/
def ordinalClock (w B t D : ℕ) :=
  (rawSize t D*(5*t+10)+2)*(RAMTape.ISA.prepareBound w 0+3) + ordinalWork w B

theorem ordinal_runs {w B : ℕ} (d : Inputs) (c : Bool) (k : Fin (size d.arity (d.degree c)))
    (hk : d.ordinal c = k.val) (fit : ISA.Fits (ISA.graded d.arity (d.degree c) k) w)
    (raw : Bool → List Bool) (packed flag : List Bool) (hB : ∀ i, (values w d raw packed flag i).length ≤ B) :
    let key := (rawCode (enumeration d.arity (d.degree c) k)).val
    ∃ n ≤ ordinalClock w B d.arity (d.degree c), (ordinal c).BoundedRun (ordinalSpace w B) n
      (publicBank w d raw packed flag) (publicBank w d (Function.update raw c (digits w key ++ raw c)) packed flag) := by
  intro key
  let x := values w d raw packed flag
  let p := ISA.graded d.arity (d.degree c) k
  let R := ISA.registers w p {}
  have hin : CallBank.filled (ordinalSource c) (wordPorts 13) x = RegisterTable.bank Fin.elim0 0 R := by
    funext i
    cases i with
    | reg j =>
      have hmem : (RAMTape.ISA.Port.reg j : OrdBank) ∈ wordPorts 13 := by simp [wordPorts]
      simp only [CallBank.filled, ite_eq_left hmem]
      fin_cases j <;> simp [ordinalSource, values, x, RegisterTable.bank, RAMTape.ISA.bank,
        R, ISA.registers, p, ISA.graded, hk, digits, ISA.word]
    | persistent => simp [CallBank.filled, wordPorts, x, ordinalSource, values, RegisterTable.bank, RAMTape.ISA.bank, digits]
    | pub j => exact Fin.elim0 j
    | work j => simp [CallBank.filled, wordPorts, RegisterTable.bank, RAMTape.ISA.bank]
    | logPort j => cases j <;> simp [CallBank.filled, wordPorts, RegisterTable.bank, RAMTape.ISA.bank,
        RAMTape.ISA.logStacks, AddressLog.keys, AddressLog.values]
  obtain ⟨steps,ht,out,hr,hkey,_⟩ := ordinalRoutine_runs k fit
  let post := RegisterTable.bank Fin.elim0 0 (ISA.registers w p out)
  obtain ⟨n,hn,hcall⟩ := CallBank.machine_run (ordinalSource c) (wordPorts 13) ordinalRoutine
    [(.reg 5,.raw c)] (wordPorts 13) x _ post (wordPorts_nodup _) hB hin hr (register_empty_else _)
  have hsave : CallBank.saved post [(.reg 5,.raw c)] x =
      values w d (Function.update raw c (digits w key ++ raw c)) packed flag := by
    change Function.update (values w d raw packed flag) (.raw c) (digits w out.cursor ++ raw c) = _
    rw [hkey]
    exact update_raw ..
  rw [hsave] at hcall
  have hrun := lift_call Sum.inl Sum.inl_injective (singleOrdinal c) hcall
  simp only [length_wordPorts, List.length_cons, List.length_nil] at hn hrun
  refine ⟨n, ?_, hrun⟩
  exact hn.trans (Nat.add_le_add_right ht _)

end RadicalCertificate.MonomialIndex.PairCall

end VPVNP
end Computability
end OAI
