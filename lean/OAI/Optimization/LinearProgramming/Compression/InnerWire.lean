import OAI.Optimization.LinearProgramming.Games.RecoveryMachineWire

/-! Four public control fields for the minor arithmetic service. The two dimensions are
written in unary by the surrounding address RAM and the lookup rank is written in binary. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner

open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

abbrev Input := (ℕ × ℕ) × (Bool × ℕ)

def inputWord (n g : ℕ) (member : Bool) (rank : ℕ) : Word :=
  frame (List.replicate n true) ++ frame (List.replicate g true) ++ [member] ++ encodeNat rank

def inputEncoding (x : Input) := inputWord x.1.1 x.1.2 x.2.1 x.2.2

def inputCode : Input → Word := prodCode (prodCode unaryCode unaryCode) (prodCode boolCode Nat.bits)

def outputWord : Option ℚ → Word := Games.RecoveryMachine.outputWire

@[simp] theorem outputWord_none : outputWord none = [false] := rfl
@[simp] theorem outputWord_some (q : ℚ) : outputWord (some q) = true :: encodeRat q := rfl

noncomputable def readInputP : Procedure inputEncoding inputCode id := by
  let top : Procedure inputEncoding (prodCode unaryCode (prodCode unaryCode (id : Word → Word)))
      (fun x : Input => (x.1.1,x.1.2,[x.2.1] ++ encodeNat x.2.2)) :=
    (identity inputEncoding).result (by
      intro x; simp [inputEncoding,inputWord,prodCode,pairBits,unaryCode,quoteBits_eq_frame,List.append_assoc])
  let n := (first unaryCode (prodCode unaryCode (id : Word → Word))).comp top
  let rest := (second unaryCode (prodCode unaryCode (id : Word → Word))).comp top
  let g := (first unaryCode (id : Word → Word)).comp rest
  let tailBits := (second unaryCode (id : Word → Word)).comp rest
  let found := head.comp tailBits
  let carry : Procedure inputEncoding (prodCode Nat.bits (id : Word → Word)) (fun x : Input => (x.2.2,[])) :=
    (tail.comp tailBits).result (by intro x; simp [prodCode,pairBits,encodeNat,quoteBits_eq_frame])
  let rank := (first Nat.bits (id : Word → Word)).comp carry
  exact ((n.pair g).pair (found.pair rank)).congrFun (by rintro ⟨⟨n,g⟩,b,r⟩; rfl)

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
