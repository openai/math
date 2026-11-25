import OAI.Computability.BorderVNP.CellPacketReadTags
import OAI.Computability.BorderVNP.CellPacketBinaryCount
import OAI.Computability.BorderVNP.CellDirectoryTyped

/-! # Physical decoder from the team packet to the private compiler's typed input

Ports, routes, factor and record tags, tables and repeated directories are read in their
actual transport order. The three list-counter stacks are reused sequentially and never
alias a live outer list. Final reversal returns the canonical CQF tuple on one clean stack.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Native

open ExactQuantumFactoring.BitStackProgram

private abbrev natRaw (n : ℕ) : List ℕ := [n]

private def natR : TypedReader natRaw Nat.bits ∅ := scalarReader

private theorem wire_pos_cons (n : ℕ) (ns : List ℕ) : 0 < (wire (n::ns)).length := by simp

private def portR : TypedReader port Typed.port ∅ := by
  let p := typedPair natR (typedPair natR natR)
  exact typedReserve (typedOn p Typed.portFields (src' := port) (dst' := Typed.port)
    (fun _ => rfl) (fun _ => rfl)) (by simp)

private def routeR : TypedReader route Typed.route ∅ := by
  let p := typedPair natR (typedPair natR (typedPair portR portR))
  exact typedReserve (typedOn p Typed.routeFields (src' := route) (dst' := Typed.route)
    (fun _ => rfl) (fun _ => rfl)) (by simp)

private abbrev inner : Finset (Fin 3) := {2}
private abbrev mid : Finset (Fin 3) := {1,2}

private def vectorR : TypedReader vector Typed.naturals inner := by
  let p := typedList 2 (binaryCountRoutine 2) natR (by simp) (fun n => wire_pos_cons n [])
  exact typedOn p id (fun xs => by simp [fieldList,vector]) (fun _ => rfl)

private def boolVectorR : TypedReader (fun xs : List Bool => vector (xs.map Bool.toNat)) Typed.booleans inner := by
  let p := typedList 2 (binaryCountRoutine 2) typedBoolean (by simp) (fun b => wire_pos_cons _ [])
  exact typedOn p id (fun xs => by
    simp only [fieldList, vector, List.length_map, List.cons.injEq, true_and, id_eq]
    induction xs with | nil => rfl | cons b bs ih => simp [ih]) (fun _ => rfl)

private def factorR : TypedReader factor Typed.factor inner := by
  let a := typedReserve (typedPair vectorR boolVectorR) (L := inner) (by simp)
  let c := typedReserve (typedPair vectorR vectorR) (L := inner) (by simp)
  let d := typedReserve (typedPair natR portR) (L := inner) (by simp)
  exact typedOn (typedTagged4 a a c d) Typed.factorFields
    (fun f => by cases f <;> simp [Typed.factorFields,tagFields,factor,natRaw])
    (fun _ => rfl)

private def routesR : TypedReader (fieldList route) (listCode Typed.route) inner :=
  typedList 2 (binaryCountRoutine 2) routeR (by simp) (fun r => wire_pos_cons _ _)

private def recordR : TypedReader record Typed.record inner := by
  let a := typedReserve (typedPair natR (typedPair natR portR)) (L := inner) (by simp)
  let b := typedReserve (typedPair natR (typedPair natR (typedPair portR portR))) (L := inner) (by simp)
  let c := typedReserve (typedPair natR (typedPair natR (typedPair natR natR))) (L := inner) (by simp)
  let d := typedReserve (typedPair natR (typedPair portR (typedPair natR (typedPair vectorR routesR))))
    (L := inner) (by simp)
  exact typedOn (typedTagged4 a b c d) Typed.recordFields
    (fun r => by cases r <;> simp [Typed.recordFields,tagFields,record,natRaw,List.append_assoc])
    (fun _ => rfl)

private def boxR : TypedReader (fieldList factor) (listCode Typed.factor) mid :=
  typedList 1 (binaryCountRoutine 1) factorR (by decide) (fun f => by cases f <;> exact wire_pos_cons _ _)

private def boxesR : TypedReader (fieldList (fieldList factor)) (listCode (listCode Typed.factor)) {0,1,2} :=
  typedList 0 (binaryCountRoutine 0) boxR (by decide) (fun fs => wire_pos_cons _ _)

private def recordsR : TypedReader (fieldList record) (listCode Typed.record) mid :=
  typedList 1 (binaryCountRoutine 1) recordR (by decide) (fun r => by cases r <;> exact wire_pos_cons _ _)

private def reportsR : TypedReader (fieldList vector) (listCode Typed.naturals) mid :=
  typedList 1 (binaryCountRoutine 1) vectorR (by decide) (fun ws => wire_pos_cons _ _)

private def directoryFields (d : Directory) :=
  fieldList (fieldList factor) d.boxes ++ fieldList record d.records ++ fieldList vector d.reportedCounts

private def directoryR : TypedReader directoryFields Typed.directory Finset.univ := by
  let p := typedPair boxesR (typedPair recordsR reportsR)
  exact typedReserve (typedOn p (fun d : Directory => (d.boxes,d.records,d.reportedCounts))
    (src' := directoryFields) (dst' := Typed.directory) (fun _ => by simp [directoryFields,List.append_assoc]) (fun _ => rfl))
    (Finset.subset_univ _)

/-- The full packet is read in its literal word order. The output is the canonical typed pair
of private-wire count and directory; all temporary counters are clear after the last field. -/
def packetReader : TypedReader (fun x : ℕ × Directory => words x.2 x.1) Typed.input Finset.univ :=
  typedReserve (typedOn (typedPair natR directoryR) id (src' := fun x : ℕ × Directory => words x.2 x.1)
    (dst' := Typed.input) (fun x => by simp [directoryFields,words,natRaw,List.append_assoc]) (fun _ => rfl))
    (Finset.subset_univ _)

private def physicalReader : Reader (fun x : ℕ × Directory => bits x.2 x.1) Typed.input Finset.univ :=
  (packetReader (fun b => [b])).castCode (fun _ => rfl) (fun _ => by simp)

/-- Explicit quadratic-clock clean-stack decoder, using a single final output reversal. -/
noncomputable def decoder : Procedure (fun x : ℕ × Directory => bits x.2 x.1) Typed.input id where
  K := Register
  finiteK := inferInstance
  decideK := inferInstance
  input := .input
  output := .input
  program := .seq physicalReader.program (reverseMove .output .input)
  bound := Polynomial.C (3*physicalReader.scale+1)*(Polynomial.X+1)^2
  runs x := by
    let src := bits x.2 x.1
    let out := Typed.input x
    let ct : Fin 3 → List Bool := fun _ => []
    obtain ⟨c,hc,hr⟩ := physicalReader.runs x [] [] ct (fun _ _ => rfl)
    simp only [List.append_nil] at hr
    change Runs _ (bank src [] ct) (bank [] out.reverse ct) c at hr
    have hlen := hr.length_le .output
    change out.reverse.length ≤ 0+c at hlen
    simp only [List.length_reverse, Nat.zero_add] at hlen
    have hfinish := reverseMove_runs (Register.output) Register.input (by decide) (bank [] out.reverse ct)
    have h₀ : bank src [] ct = singletonStore Register.input src := by funext k; cases k <;> rfl
    have h₁ : Function.update (Function.update (bank [] out.reverse ct) Register.output []) Register.input
        (out.reverse.reverse ++ []) = singletonStore Register.input out := by
      rw [List.reverse_reverse,List.append_nil]
      funext k; cases k <;> rfl
    change Runs _ _ (Function.update (Function.update (bank [] out.reverse ct) Register.output []) Register.input
      (out.reverse.reverse ++ [])) (2*out.reverse.length+1) at hfinish
    rw [h₁,List.length_reverse] at hfinish
    rw [h₀] at hr
    refine ⟨2*out.length+1+c,?_,Runs.seq hr hfinish⟩
    simp only [Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
      Polynomial.eval_X,Polynomial.eval_one]
    change _ ≤ (3*physicalReader.scale+1)*(src.length+1)^2
    change c ≤ physicalReader.scale*(src.length+1)^2 at hc
    have hp := Nat.one_le_pow 2 (src.length+1) (by omega)
    rw [Nat.add_mul, Nat.one_mul,Nat.mul_assoc]
    omega

/-- The native private parser has a quadratic time polynomial in the public packet length. -/
theorem decoder_quadratic : ∃ C : ℕ, ∀ n : ℕ, decoder.bound.eval n = C*(n+1)^2 := by
  refine ⟨3*physicalReader.scale+1, fun n => ?_⟩
  change (Polynomial.C (3*physicalReader.scale+1)*(Polynomial.X+1)^2).eval n = _
  simp

end CellSparse.Packet.Native

end BorderVNP
end Computability
end OAI
