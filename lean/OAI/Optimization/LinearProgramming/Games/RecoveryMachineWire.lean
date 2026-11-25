import OAI.Optimization.LinearProgramming.OracleSpec.ArithmeticEncoding
import OAI.Optimization.LinearProgramming.OracleSpec.BitStackDeployment

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Games
namespace RecoveryMachine

open ExactQuantumFactoring.BitStackProgram OracleSpec
open ExactQuantumFactoring.BitStackProgram.Procedure

abbrev Input := ℚ × ℕ

def inputCode : Input → Word := prodCode ratCode Nat.bits

def inputWire (x : Input) : Word := encodeRat x.1 ++ encodeNat x.2

def answerCode : Option ℚ → Word
  | none => [false]
  | some q => true :: ratCode q

def outputWire : Option ℚ → Word
  | none => [false]
  | some q => true :: encodeRat q

/-- Parse one signed framed rational followed by its framed denominator bound. Arithmetic
starts only after the sign and each terminating frame bit have been consumed. -/
noncomputable def readInput : Procedure inputWire inputCode id := by
  let raw := (Procedure.identity (id : Word → Word)).precompose inputWire
  let sign := Procedure.head.comp raw
  let endField := prodCode Nat.bits emptyCode
  let middle := prodCode Nat.bits endField
  let fields := prodCode Nat.bits middle
  let vals (s : Input) := (s.1.num.natAbs,s.1.den,s.2,())
  let decoded : Procedure inputWire fields vals := (Procedure.tail.comp raw).result (by
    rintro ⟨q,A⟩
    simp [inputWire, encodeRat, encodeNat, fields,middle,endField,vals,prodCode,pairBits,
      quoteBits_eq_frame,emptyCode,List.append_assoc])
  let mag := (Procedure.first Nat.bits middle).comp decoded
  let rest := (Procedure.second Nat.bits middle).comp decoded
  let den := (Procedure.first Nat.bits endField).comp rest
  let A := (Procedure.first Nat.bits emptyCode).comp ((Procedure.second Nat.bits endField).comp rest)
  let num : Procedure inputWire intCode (fun s => s.1.num) := (sign.pair mag).result (fun _ => rfl)
  let rat : Procedure inputWire ratCode (fun s => s.1) := (num.pair den).result (fun _ => rfl)
  exact (rat.pair A).congrFun (by rintro ⟨_,_⟩;rfl)

/-- The failure tag and all successful output bits are physically written by the transducer. -/
noncomputable def writeAnswer : Procedure answerCode id outputWire := by
  let fail := Procedure.constant emptyCode (id : Word → Word) [false]
  let win : Procedure ratCode id (fun q => true :: encodeRat q) :=
    ((Procedure.prepend (id : Word → Word) [true]).comp Wire.writeRat).result (by intro _;rfl)
  let cast (q : Option ℚ) : Unit ⊕ ℚ := match q with | none => .inl () | some y => .inr y
  let code := ((fail.casesSum win).precompose cast).congrEncoding (ec := answerCode)
    (fun q => by cases q <;> rfl) (fun _ => rfl)
  exact code.congrFun (fun q => by cases q <;> rfl)

end RecoveryMachine
end Games
end LinearProgramming
end Optimization
end OAI
