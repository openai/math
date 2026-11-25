import OAI.Optimization.LinearProgramming.Compression.InnerVectors
import OAI.Optimization.LinearProgramming.Lattice.BitDriverWire
import OAI.Optimization.LinearProgramming.Contraction.Dyadic

/-! Exact inverses and short length bounds for the finite words shared across the three
arithmetic phases. The physical dispatcher pads an already typed row before serialization. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner

open OracleSpec ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure
open Lattice.Bit

private def decodeFields : ℕ → Word → List ℤ
  | 0,_ => []
  | n+1,w => match Contraction.readSigned w with
    | some (z,tail) => z :: decodeFields n tail
    | none => []

private theorem signedPrefix (z : ℤ) (xs : Word) :
    Contraction.readSigned (Driver.signedField z ++ xs) = some (z,xs) :=
  Contraction.readSigned_word _ _

private theorem decodeFields_packet (xs : List ℤ) (fuel : ℕ) (hf : xs.length ≤ fuel) :
    decodeFields fuel (Driver.signPacket xs)=xs := by
  induction xs generalizing fuel with
  | nil => cases fuel <;> rfl
  | cons z xs ih =>
    cases fuel with
    | zero => simp at hf
    | succ k =>
      change (match Contraction.readSigned (Driver.signedField z ++ Driver.signPacket xs) with
        | some (a,rest) => a::decodeFields k rest | none => []) = _
      rw [signedPrefix]
      exact congrArg (z::·) (ih k (by simpa using hf))

private theorem packet_length (zs : List ℤ) : zs.length ≤ (Driver.signPacket zs).length := by
  induction zs with
  | nil => rfl
  | cons z zs ih =>
    change zs.length+1 ≤ (Driver.signedField z ++ Driver.signPacket zs).length
    simpa only [List.length_append,Driver.signedField,List.length_cons] using
      (show zs.length+1 ≤ (encodeNat z.natAbs).length+1+(Driver.signPacket zs).length by omega)

def unpackRow (w : Word) := decodeFields w.length w

@[simp] theorem unpackRow_packet (z : List ℤ) : unpackRow (Driver.signPacket z)=z :=
  decodeFields_packet z _ (packet_length z)

theorem signPacket_injective : Function.Injective Driver.signPacket := Function.LeftInverse.injective unpackRow_packet

/-- The virtual wire used to transfer epoch request traces. It agrees exactly with the
physical action, which constructs the padded row before it emits a word. -/
def epochWire (packet : Word) := Driver.signPacket (padRow (unpackRow packet))

@[simp] theorem epochWire_packet (z : List ℤ) : epochWire (Driver.signPacket z)=Driver.signPacket (padRow z) := by
  simp [epochWire]

@[simp] theorem epochWire_typed {g : ℕ} (z : Fin (g+1) → ℤ) :
    epochWire (Lattice.signRowWord z) = Lattice.signRowWord (padEpochQuery z) := by
  rw [← Driver.signPacket_pack,epochWire_packet,padRow_pack,Driver.signPacket_pack]

theorem padRow_packet_length (z : List ℤ) :
    (Driver.signPacket (padRow z)).length ≤ (Driver.signPacket z).length+4 := by
  cases h : z.reverse with
  | nil =>
    have hz : z=[] := by simpa using congrArg List.reverse h
    subst z; decide
  | cons a xs =>
    have hz : z=xs.reverse++[a] := by simpa using congrArg List.reverse h
    rw [hz]
    simp [padRow,beforeLast,lastOrZero,Driver.signPacket,Driver.signedField,encodeNat,frame]
    omega

private def splitFrame : Word → Option (Word × Word)
  | false::rest => some ([],rest)
  | true::b::rest => (splitFrame rest).map fun p => (b::p.1,p.2)
  | _ => none

private theorem splitFrame_append (xs rest : Word) : splitFrame (frame xs ++ rest)=some (xs,rest) := by
  induction xs with
  | nil => rfl
  | cons b xs ih =>
    change (splitFrame (frame xs ++ rest)).map (fun p => (b::p.1,p.2)) = _
    simp [ih]

private theorem pairBits_eq {a b c d : Word} (h : pairBits a b = pairBits c d) : a=c ∧ b=d := by
  have he := congrArg splitFrame h
  simpa [pairBits,quoteBits_eq_frame,splitFrame_append] using he

private theorem productCode_injective {A B : Type} {ea : A → Word} {eb : B → Word}
    (ha : Function.Injective ea) (hb : Function.Injective eb) : Function.Injective (prodCode ea eb) := by
  rintro ⟨a,b⟩ ⟨c,d⟩ h
  obtain ⟨h₁,h₂⟩ := pairBits_eq h
  exact Prod.ext (ha h₁) (hb h₂)

private theorem naturalCode_injective : Function.Injective Nat.bits := by
  intro n m h
  have he : Contraction.readMagnitude (encodeNat n ++ [])=Contraction.readMagnitude (encodeNat m ++ []) := by
    rw [encodeNat,encodeNat,h]
  simpa only [Contraction.readMagnitude_encodeNat,Option.some.injEq,Prod.mk.injEq,and_true] using he

private theorem booleanCode_injective : Function.Injective boolCode := by intro a b h; simpa [boolCode] using h

private theorem integerCode_injective : Function.Injective intCode := by
  intro a b h
  have he := productCode_injective booleanCode_injective naturalCode_injective h
  simpa only [intOfSign_data] using congrArg intOfSign he

private theorem rationalCode_injective : Function.Injective ratCode := by
  intro a b h
  have he := productCode_injective integerCode_injective naturalCode_injective h
  simpa only [Rat.mkRat_self] using congrArg (fun p : ℤ × ℕ => mkRat p.1 p.2) he

private theorem listCode_injective {A : Type} {e : A → Word} (he : Function.Injective e) :
    Function.Injective (listCode e) := by
  intro xs
  induction xs with
  | nil => intro ys h; cases ys <;> simp_all [listCode]
  | cons x xs ih =>
    intro ys h
    cases ys with
    | nil => simp [listCode] at h
    | cons y ys =>
      have hp : pairBits (e x) (listCode e xs)=pairBits (e y) (listCode e ys) := (List.cons.inj h).2
      obtain ⟨hx,ht⟩ := pairBits_eq hp
      rw [he hx,ih ht]

theorem graphOutputCode_injective : Function.Injective graphResultCode :=
  productCode_injective booleanCode_injective (productCode_injective (listCode_injective rationalCode_injective) rationalCode_injective)

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
