import OAI.Computability.NearSquareRoot.InterchangeROMAddressCommand
import OAI.Computability.NearSquareRoot.InterchangeROMEffectiveCell
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxFold

/-! # Effective generation of variable pivot code

The compiler enumerates the serialized control file of a pivot batch from the
radix, number of slots and ordinary list of pairs of natural ranks.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress

open IntegerMultiplication IntegerMultiplication.Code GeneratorSyntax

variable {X A B : Type} [Primcodable X] [Primcodable A] [Primcodable B]

theorem emit_pair {u v : X → Tree}
    (hu : Effective ltr fun x => Task.prepare 0 (u x))
    (hv : Effective ltr fun x => Task.prepare 0 (v x)) :
    Effective ltr fun x => Task.prepare 0 (.fork (u x) (v x)) :=
  hv.join (hu.join (effective_const ltr (pack 0)))

theorem emit_list [Codec A] {l : X → List A}
    (hl : Computable l) (he : Effective ltr fun a : A => Task.prepare 0 (send a)) :
    Effective ltr fun x => Task.prepare 0 (send (l x)) := by
  let step (_ : X) (s : A × File) :=
    joinFile s.2 (joinFile (file ltr (Task.prepare 0 (send s.1))) (file ltr (pack 0)))
  have hs : Computable₂ step :=
    (primrec_joinFile.to_comp.comp (Computable.snd.comp Computable.snd)
      (primrec_joinFile.to_comp.comp (he.comp (Computable.fst.comp Computable.snd))
        (Computable.const _))).to₂
  have gen := computable_foldr (z:=fun _ => file ltr (Task.prepare 0 (send ([] : List A)))) hl
    (Computable.const _) hs
  apply gen.of_eq
  intro x
  dsimp only
  induction l x with
  | nil => rfl
  | cons a xs ih =>
    rw [List.foldr_cons,ih]
    simp only [step,joinFile_file,send_cons,Task.prepare]

theorem emit_tally : Effective ltr fun t : Tally => Task.prepare 0 (send t) :=
  emit_list Computable.id ((effective_const ltr (Task.prepare 0 (send ()))).of_eq
    (fun ⟨⟩ => rfl))

theorem emit_cuts : Effective ltr fun c : Cuts => Task.prepare 0 (send c) := by
  apply emit_pair (emit_tally.comp Computable.fst)
  apply emit_pair (emit_tally.comp (Computable.fst.comp Computable.snd))
  exact emit_pair (emit_tally.comp (Computable.fst.comp (Computable.snd.comp Computable.snd)))
    (emit_tally.comp (Computable.snd.comp (Computable.snd.comp Computable.snd)))

theorem effective_command (core : Cmd) {sp : X → Spec} (hs : Computable sp) :
    Effective ltr fun x => command core (sp x) := by
  have h := emit_pair (emit_tally.comp (Computable.fst.comp hs))
    (emit_list (Computable.snd.comp hs) emit_cuts)
  have body := (h.join ((effective_const ltr (pack 0)).join (effective_const ltr core))).join
    (effective_const ltr (pack 0))
  have branch : Effective ltr (fun x => prepare core (sp x)) := (InterchangeROM.computable_nodeFile.comp body).of_eq
    (fun x => InterchangeROM.nodeFile_file _)
  exact branch.join (effective_const ltr (InterchangeBatch.batch (.again 1)))

def numericSpec (radix n : ℕ) (pairs : List (ℕ × ℕ)) : Spec :=
  (tally radix,pairs.map fun ⟨x,y⟩ => (tally x,tally (n-x-1),tally y,tally (n-y-1)))

theorem metadata_eq {J : Type} {n : ℕ} (b : ℕ) (ord : J ≃ Fin n) (pairs : List (J × J)) :
    metadata b ord pairs = numericSpec b n (pairs.map fun p => ((ord p.1).val,(ord p.2).val)) := by
  simp [metadata,numericSpec,List.map_map]

theorem computable_tally : Computable tally := by
  apply (Primrec.list_map Primrec.list_range ((Primrec.const ()).to₂)).to_comp.of_eq
  intro n
  simp [tally]

theorem computable_numericSpec {p n : X → ℕ} {pairs : X → List (ℕ × ℕ)}
    (hp : Computable p) (hn : Computable n) (hxy : Computable pairs) :
    Computable fun x => numericSpec (p x) (n x) (pairs x) := by
  have a : Computable fun v : X × ℕ × ℕ => v.2.1 := Computable.fst.comp Computable.snd
  have b : Computable fun v : X × ℕ × ℕ => v.2.2 := Computable.snd.comp Computable.snd
  have afterRank (r : X × ℕ × ℕ → ℕ) (hr : Computable r) :
      Computable fun v => tally (n v.1 - r v - 1) :=
    computable_tally.comp (Primrec.nat_sub.to_comp.comp
      (Primrec.nat_sub.to_comp.comp (hn.comp Computable.fst) hr) (Computable.const 1))
  exact (computable_tally.comp hp).pair (computable_map hxy ((computable_tally.comp a).pair
    ((afterRank _ a).pair ((computable_tally.comp b).pair (afterRank _ b)))).to₂)

theorem effective_pivots (core : Cmd) {p n : X → ℕ} {pairs : X → List (ℕ × ℕ)}
    (hp : Computable p) (hn : Computable n) (hpairs : Computable pairs) :
    Effective ltr fun x => command core (numericSpec (p x) (n x) (pairs x)) :=
  effective_command core (computable_numericSpec hp hn hpairs)

end InterchangeROMAddress

end NearSquareRoot
end Computability
end OAI
