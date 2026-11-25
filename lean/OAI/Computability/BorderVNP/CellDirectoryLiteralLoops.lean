import OAI.Computability.BorderVNP.CellDirectoryLexical
import OAI.Computability.BorderVNP.CellLiteralLoops

/-! # Literal loop trip counts in the full sparse directory

Copy, lane, flag and term multiplicities are stored in the generator as binary
literals. Runtime arithmetic in reads and conditional guards does not affect
the upper bound on visits arising from loop trip counts.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

private theorem loopLit (n : ℕ) {s : Stmt} (h : s.LiteralLoops) :
    (Stmt.loop (.lit n) s).LiteralLoops := ⟨⟨n,rfl⟩,h⟩

private theorem seqMap {α : Type*} (l : List α) (s : α → Stmt) (h : ∀ a, (s a).LiteralLoops) :
    (sequence (l.map s)).LiteralLoops := by
  apply sequence_literalLoops
  intro t ht
  obtain ⟨a,_,rfl⟩ := List.mem_map.mp ht
  exact h a

/-- The flag-block machinery contributes only the two literal trip counts. -/
theorem localFlags_literalLoops (n : ℕ) {s : Stmt} (hs : s.LiteralLoops) : (localFlags n s).LiteralLoops :=
  ⟨loopLit n trivial, hs, loopLit n ⟨trivial,trivial,trivial⟩⟩

private theorem initLit (base cap : ℕ) : (Prefix.initGen base cap).LiteralLoops :=
  loopLit _ ⟨Term.guard_literalLoops _,Term.guard_literalLoops _⟩

private theorem stepLit (base cap : ℕ) (i : NatExpr) (m : Term) : (Prefix.stepGen base cap i m).LiteralLoops :=
  loopLit _ ⟨Term.guard_literalLoops _,Term.guard_literalLoops _⟩

private theorem generatorLit (base copies cap : ℕ) (m : NatExpr → Term) :
    (Prefix.generator base copies cap m).LiteralLoops :=
  ⟨initLit _ _,loopLit _ (stepLit ..)⟩

/-- All loops in a public profile checker repeat a literal number of times. -/
theorem Profile.profileGen_literalLoops (base off c : ℕ) (s : Port) (w : ℕ) (hist : List ℕ) (rs : List Route) :
    (Profile.profileGen base off c s w hist rs).LiteralLoops :=
  ⟨loopLit _ (Term.guard_literalLoops _),
    seqMap _ _ (fun _ => ⟨generatorLit .., Term.guard_literalLoops _⟩),
    seqMap _ _ (fun _ => ⟨Term.guard_literalLoops _,loopLit _ (loopLit _ (loopLit _ (Term.guard_literalLoops _)))⟩)⟩

private theorem recordLit (boxes : List (List Factor)) (r : Record) : (recordGuard boxes r).LiteralLoops := by
  cases r with
  | zero _ _ _ | equal _ _ _ _ => exact loopLit _ (loopLit _ (Term.guard_literalLoops _))
  | profile _ _ _ _ _ => exact localFlags_literalLoops _ (Profile.profileGen_literalLoops ..)
  | box _ _ _ _ => exact Term.guard_literalLoops _

/-- A box traversal adds one literal-bound loop per descriptor and sequences
the repeated one-copy factor actions without any data-dependent trip counts. -/
theorem sweep_literalLoops (body : FactorBody) (bs : List BoxBlock) (start : ℕ)
    (hb : ∀ f j off i, (body f j off i).LiteralLoops) : (sweep body bs start).LiteralLoops := by
  induction bs generalizing start with
  | nil => trivial
  | cons b bs ih => exact ⟨loopLit _ (seqMap _ _ (fun _ => hb ..)), ih _⟩

private theorem gadgetLit (D : Directory) (id : ℕ) (bits : List ℕ) :
    (Gadget.row D id bits).LiteralLoops := by
  apply localFlags_literalLoops
  exact ⟨initLit .., sweep_literalLoops _ _ _ (fun _ _ _ _ => stepLit ..),
    loopLit _ ⟨Term.guard_literalLoops _,Term.guard_literalLoops _⟩⟩

/-- Every loop in the actual sparse generator, including all box scans and
both branches of each count check, has a literal repetition count. -/
theorem Directory.program_literalLoops (D : Directory) (privateWires : ℕ) :
    (D.program privateWires).LiteralLoops :=
  ⟨loopLit _ trivial, seqMap _ _ (recordLit D.boxes),
    sweep_literalLoops _ _ _ (fun _ _ _ _ => ⟨Term.guard_literalLoops _,Term.emit_literalLoops _ _,trivial⟩),
    sweep_literalLoops _ _ _ (fun _ _ _ _ => Term.guard_literalLoops _),
    seqMap _ _ (fun z => gadgetLit D z.2 z.1)⟩

end CellSparse

end BorderVNP
end Computability
end OAI
