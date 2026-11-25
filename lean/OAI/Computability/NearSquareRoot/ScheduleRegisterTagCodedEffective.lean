import OAI.Computability.NearSquareRoot.ScheduleRegisterTagCoded
import OAI.Computability.NearSquareRoot.ScheduleRegisterTagCodedSpell

/-! # Emitting literal parity-register transition and finalization tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace RegisterTagCoded
open IntegerMultiplication Code KernelComputableAddress
open GeneratorSyntax (ltr Effective)

variable {X : Type*} [Primcodable X]

private theorem primrec_modulus {p : X → P} (hp : Primrec p) : Primrec fun x => modulus (p x) :=
  primrec_pow (Primrec.const 2) (Primrec.fst.comp (Primrec.snd.comp hp))

private theorem primrec_columns {p : X → P} (hp : Primrec p) : Primrec fun x => 2^((p x).1+1) :=
  primrec_pow (Primrec.const 2) (Primrec.succ.comp (Primrec.fst.comp hp))

private theorem primrec_count {p : X → P} (hp : Primrec p) : Primrec fun x => stateCount (p x) :=
  Primrec.nat_mul.comp (Primrec.succ.comp (primrec_columns hp)) (primrec_modulus hp)

theorem primrec_tickRank {p : X → P} {c n : X → ℕ} (hp : Primrec p) (hc : Primrec c) (hn : Primrec n) :
    Primrec fun x => tickRank (p x) (c x) (n x) := by
  have m := primrec_modulus hp
  have ph := Primrec.nat_div.comp hn m
  have acc := Primrec.nat_mod.comp hn m
  exact Primrec.ite (Primrec.eq.comp ph (Primrec.const 0))
    (Primrec.nat_add.comp acc (Primrec.nat_mul.comp (Primrec.succ.comp hc) m))
    (primrec_updateParity (Primrec.fst.comp (Primrec.snd.comp hp))
      ((Primrec.list_getD 0).comp (Primrec.snd.comp (Primrec.snd.comp hp))
        (primrec_pairedRank (Primrec.fst.comp hp) (Primrec.nat_sub.comp ph (Primrec.const 1)) hc)) acc)

def entryWords (p : P) (c n : ℕ) : RegisterTable.Word × RegisterTable.Word :=
  (2 :: (columnWord p.1 c ++ tallyWord n),tallyWord (tickRank p c n))

theorem primrec_entryWords {p : X → P} {c n : X → ℕ} (hp : Primrec p) (hc : Primrec c) (hn : Primrec n) :
    Primrec fun x => entryWords (p x) (c x) (n x) :=
  (Primrec.list_cons.comp (Primrec.const 2)
    (Primrec.list_append.comp (primrec_columnWord (Primrec.fst.comp hp) hc) (primrec_tallyWord.comp hn))).pair
    (primrec_tallyWord.comp (primrec_tickRank hp hc hn))

def words (p : P) : RegisterTable.Table :=
  (List.range (2^(p.1+1))).flatMap fun c => (List.range (stateCount p)).map (entryWords p c)

theorem primrec_words : Primrec words := by
  apply Primrec.list_flatMap (Primrec.list_range.comp (primrec_columns Primrec.id))
  change Primrec fun v : P × ℕ => (List.range (stateCount v.1)).map (entryWords v.1 v.2)
  apply Primrec.list_map (Primrec.list_range.comp (primrec_count Primrec.fst))
  exact (primrec_entryWords (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst) Primrec.snd).to₂

theorem words_eq (p : P) : words p = RegisterTable.encode (table p) := by
  have idx : (List.finRange (2^(p.1+1))).map Fin.val = List.range (2^(p.1+1)) := by
    apply List.ext_getElem <;> simp
  unfold words
  rw [← idx,List.flatMap_map]
  simp only [RegisterTable.encode,table,keys,List.map_map,List.map_flatMap]
  apply List.flatMap_congr
  intro k _
  apply List.map_congr_left
  intro n _
  have col := columnWord_rank p.1 (columnUnrank p.1 k)
  rw [columnRank_unrank] at col
  change (2 :: (columnWord p.1 k.val ++ tallyWord n),tallyWord (tickRank p k.val n)) =
    (((send (columnUnrank p.1 k)).fork (send (tally n))).spell.map ltr,
      (send (tally (tickRank p (columnRank p.1 (columnUnrank p.1 k)) n))).spell.map ltr)
  rw [columnRank_unrank,col,tallyWord_eq,tallyWord_eq]
  simp only [Tree.spell,List.map_cons,List.map_append]
  rfl

theorem effective_step : Effective ltr (fun p => RegisterTable.command (table p)) :=
  RegisterTable.effective (primrec_words.to_comp.of_eq words_eq)

def finalWords (p : P) : RegisterTable.Table :=
  (List.range (stateCount p)).map (fun n => (tallyWord n,tallyWord (n % modulus p)))

theorem primrec_finalWords : Primrec finalWords := by
  apply Primrec.list_map (Primrec.list_range.comp (primrec_count Primrec.id))
  exact ((primrec_tallyWord.comp Primrec.snd).pair
    (primrec_tallyWord.comp (Primrec.nat_mod.comp Primrec.snd (primrec_modulus Primrec.fst)))).to₂

theorem finalWords_eq (p : P) : finalWords p = RegisterTable.encode (finishTable p) := by
  simp [finalWords,RegisterTable.encode,finishTable,List.map_map,Function.comp_def,tallyWord_eq]

theorem effective_finish : Effective ltr (fun p => RegisterTable.command (finishTable p)) :=
  RegisterTable.effective (primrec_finalWords.to_comp.of_eq finalWords_eq)

end RegisterTagCoded

end NearSquareRoot
end Computability
end OAI
