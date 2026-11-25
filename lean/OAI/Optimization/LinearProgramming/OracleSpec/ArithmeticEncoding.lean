import OAI.Optimization.LinearProgramming.OracleSpec.Arithmetic
import OAI.Optimization.LinearProgramming.OracleSpec.PriceGame
import OAI.Optimization.LinearProgramming.PriceGame.Model

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec

open ExactQuantumFactoring.BitStackProgram

/-- The sibling library's prefix quoting uses exactly the reference's framing. -/
theorem quoteBits_eq_frame (w : Word) : quoteBits w = frame w := by
  induction w with
  | nil => rfl
  | cons b w ih => rw [quoteBits_cons, ih]; rfl

namespace Wire

noncomputable def writeNat : Procedure Nat.bits id encodeNat :=
  (Procedure.quote Nat.bits).result (by intro n; exact quoteBits_eq_frame _)

noncomputable def writeRat : Procedure ratCode id encodeRat := by
  let sg : Procedure ratCode id (fun q => [decide (q.num < 0)]) :=
    (Procedure.intSign.comp Procedure.ratNum).result (by intro q; rfl)
  let mag := writeNat.comp (Procedure.intAbs.comp Procedure.ratNum)
  let den := writeNat.comp Procedure.ratDen
  exact (Procedure.append.comp (sg.pair (Procedure.append.comp (mag.pair den)))).congrFun (by intro q; rfl)

theorem flat_length_le (words : List Word) :
    words.flatten.length ≤ (listCode id words).length := by
  induction words with
  | nil => decide
  | cons a as ih =>
    rw [List.flatten_cons, List.length_append, listCode_length_cons]
    simp only [id_eq]
    omega

/-- A literal polynomial-time stack program for concatenating a serialized list of words. -/
noncomputable def flatten : Procedure (listCode (id : Word → Word)) id List.flatten := by
  let step : Procedure (prodCode (id : Word → Word) id) id (fun p => p.2 ++ p.1) :=
    Procedure.append.comp (Procedure.swap id id)
  let fold := Procedure.foldList [] step Polynomial.X (by
    intro words acc n
    change ((words.take n).foldl (fun x y => x ++ y) acc).length ≤ _
    have hx : (words.take n).foldl (fun x y => x ++ y) acc = acc ++ (words.take n).flatten := by
      simpa using (List.foldl_append_eq_append (l := words.take n) (f := id) (l' := acc))
    rw [hx, List.length_append, Polynomial.eval_X]
    have ha := flat_length_le (words.take n)
    have hb := listCode_length_take_le (id : Word → Word) n words
    simp only [id_eq]
    omega)
  let start := (Procedure.identity (listCode (id : Word → Word))).pair
    (Procedure.constant (listCode (id : Word → Word)) id ([] : Word))
  exact (fold.comp start).congrFun (by
    intro words
    change words.foldl (fun x y => x ++ y) [] = words.flatten
    simpa using (List.foldl_append_eq_append (l := words) (f := id) (l' := [])))

/-- Serialize one natural index and all prices, in order. Lists may have arbitrary length. -/
noncomputable def writeQuery : Procedure (prodCode Nat.bits (listCode ratCode)) id
    (fun z => encodeNat z.1 ++ z.2.flatMap encodeRat) := by
  let index := writeNat.comp (Procedure.first Nat.bits (listCode ratCode))
  let prices := flatten.comp ((Procedure.listMap (0 : ℚ) ([] : Word) writeRat).comp
    (Procedure.second Nat.bits (listCode ratCode)))
  exact (Procedure.append.comp (index.pair prices)).congrFun (by intro z; rfl)

def queryEncoding {N : ℕ} (q : PriceGame.Query N) : Word :=
  prodCode Nat.bits (listCode ratCode) (q.index.val, List.ofFn q.prices)

/-- The output from the internal query encoding agrees byte-for-byte with the challenge. -/
noncomputable def writeTypedQuery (N : ℕ) : Procedure (@queryEncoding N) id
    (fun q => priceQuery q.index q.prices) :=
  writeQuery.precompose (fun q : PriceGame.Query N => (q.index.val, List.ofFn q.prices))

def inputWire (z : ℕ × ℕ × ℕ) : Word := encodeNat z.1 ++ encodeNat z.2.1 ++ encodeNat z.2.2

/-- Transfer the public input (three framed naturals) into the sibling's ordinary nested
binary pair representation. The parser reads the final frame terminator as well. -/
noncomputable def parseInput : Procedure inputWire (prodCode Nat.bits (prodCode Nat.bits Nat.bits)) id := by
  let tail := prodCode Nat.bits emptyCode
  let mid := prodCode Nat.bits tail
  let n := Procedure.first Nat.bits mid
  let rest := Procedure.second Nat.bits mid
  let r := (Procedure.first Nat.bits tail).comp rest
  let a := (Procedure.first Nat.bits emptyCode).comp ((Procedure.second Nat.bits tail).comp rest)
  let triple := n.pair (r.pair a)
  exact ((triple.precompose (fun z : ℕ × ℕ × ℕ => (z.1,z.2.1,z.2.2,()))).congrEncoding
    (by intro z; simp [mid, tail, prodCode, pairBits, quoteBits_eq_frame, encodeNat, emptyCode,
      inputWire, List.append_assoc]) (fun _ => rfl)).congrFun (by intro z; rfl)

end Wire
end OracleSpec
end LinearProgramming
end Optimization
end OAI
