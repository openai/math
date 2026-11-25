import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocalBank
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalEffective

/-! # Effective generation of the five fixed-register bank commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.LocalTable.Lift

open IntegerMultiplication IntegerMultiplication.Code GeneratorSyntax Raw

set_option maxHeartbeats 1200000 in
/-- The modulus and all dimensions can change with the approximation index.
The selected matrix tape may come from an unbounded terminating search. -/
theorem effective_command {X : Type} [Primcodable X] (k : Kind)
    {p l w s m half : X → ℕ} {t : X → Tape} (hp : Computable p) (hl : Computable l)
    (hw : Computable w) (hs : Computable s) (hm : Computable m) (hh : Computable half) (ht : Computable t) :
    Effective ltr fun x => command k (p x) (l x) (w x) (s x) (m x) (half x) (t x) := by
  let Q := ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × Tape
  have h : Effective ltr (fun v : Q => command k v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2.1
      v.2.2.2.2.2.1 v.2.2.2.2.2.2) :=
    effective_command_pr (X:=Q) (p:=fun v => v.1) (l:=fun v => v.2.1) (w:=fun v => v.2.2.1)
      (s:=fun v => v.2.2.2.1) (m:=fun v => v.2.2.2.2.1) (half:=fun v => v.2.2.2.2.2.1)
      (t:=fun v => v.2.2.2.2.2.2) k .fst (Primrec.fst.comp .snd) (Primrec.fst.comp (Primrec.snd.comp .snd))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd))))
      (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))))
      (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp .snd)))))
  let arg (x : X) : Q := (p x,l x,w x,s x,m x,half x,t x)
  have arg_comp : Computable arg := hp.pair (hl.pair (hw.pair (hs.pair (hm.pair (hh.pair ht)))))
  exact Computable.comp
    (f:=fun v : Q => file ltr (command k v.1 v.2.1 v.2.2.1 v.2.2.2.1 v.2.2.2.2.1
      v.2.2.2.2.2.1 v.2.2.2.2.2.2)) (g:=arg) h arg_comp

/-- Generate the complete Hermite command from the searched numerical matrix
tape and the four routed command families. -/
theorem effective_full {X : Type} [Primcodable X] {p l w s m half d : X → ℕ} {t : X → Tape}
    (hp : Computable p) (hl : Computable l) (hw : Computable w) (hs : Computable s)
    (hm : Computable m) (hh : Computable half) (hd : Computable d) (ht : Computable t)
    (routed : X → Leaf → Cmd) (hr : ∀ b, Routed b → Effective ltr (fun x => routed x b)) :
    Effective ltr fun x => Physical.command
      (choose (fun k => command k (p x) (l x) (w x) (s x) (m x) (half x) (t x)) (routed x))
      (steps (l x*w x) (d x)) := by
  let leaves (x : X) := choose (fun k => command k (p x) (l x) (w x) (s x) (m x) (half x) (t x)) (routed x)
  have e (b : Leaf) : Effective ltr (fun x => leaves x b) := by
    cases b with
    | duplicate => exact effective_command .duplicate hp hl hw hs hm hh ht
    | stage => exact hr .stage trivial
    | extract => exact effective_command .extract hp hl hw hs hm hh ht
    | forward => exact hr .forward trivial
    | correct => exact hr .correct trivial
    | backward => exact hr .backward trivial
    | restore => exact effective_command .restore hp hl hw hs hm hh ht
    | copyCube => exact effective_command .copyCube hp hl hw hs hm hh ht
    | finish => exact effective_command .finish hp hl hw hs hm hh ht
  exact Physical.effective_repair (leaf:=leaves) (Physical.effective_dispatch e)
    (Primrec.nat_mul.to_comp.comp hl hw) hd

end InterchangeROMRepair.Physical.LocalTable.Lift

end NearSquareRoot
end Computability
end OAI
