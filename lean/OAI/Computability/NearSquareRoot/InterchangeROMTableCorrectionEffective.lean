import OAI.Computability.NearSquareRoot.InterchangeROMTableCorrection

/-! # Effective control generation for the complete four-slot correction -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMTable

open IntegerMultiplication InterchangeROMRepair GeneratorSyntax
variable {X : Type} [Primcodable X]

private theorem bitNat {b : X → Bool} (h : Computable b) : Computable fun x => (b x).toNat := by
  apply (Computable.cond h (Computable.const 1) (Computable.const 0)).of_eq
  intro x
  cases b x <;> rfl

private theorem computable_checkEntry {p s m z : X → ℕ} {t : X → Raw.Tape} {u v : X → CheckIndex}
    (hp : Computable p) (hs : Computable s) (hm : Computable m) (hz : Computable z)
    (ht : Computable t) (hu : Computable u) (hv : Computable v) :
    Computable fun x => checkEntry (p x) (s x) (m x) (z x) (t x) (u x) (v x) := by
  let add := Primrec.nat_add.to_comp
  let mul := Primrec.nat_mul.to_comp
  have key : Computable (fun x => correctSlot (m x) (z x) (u x).1 (v x).1) :=
    add.comp (add.comp (add.comp (add.comp (Computable.const 3) hm) (mul.comp (Computable.const 4) hz))
      (mul.comp (Computable.const 2) (bitNat (Computable.fst.comp hu)))) (bitNat (Computable.fst.comp hv))
  have blob := (Primrec.list_getD ([] : List ℕ)).to_comp.comp ht key
  have ix := add.comp (mul.comp (Computable.snd.comp (Computable.snd.comp hu)) hs)
    (Computable.snd.comp (Computable.snd.comp hv))
  have residue := Primrec.nat_mod.to_comp.comp ((Primrec.list_getD 0).to_comp.comp blob ix) (Computable.succ.comp hp)
  have test := Primrec.eq.decide.to_comp.comp (Computable.fst.comp (Computable.snd.comp hu))
    (Computable.fst.comp (Computable.snd.comp hv))
  exact (Computable.cond test residue (Computable.const 0)).of_eq fun x => by
    simp [checkEntry,Raw.atSlot,Raw.read]

private theorem computable_checkRows {p s m z : X → ℕ} {t : X → Raw.Tape} {oi ii : X → List CheckIndex}
    (hp : Computable p) (hs : Computable s) (hm : Computable m) (hz : Computable z)
    (ht : Computable t) (ho : Computable oi) (hi : Computable ii) :
    Computable fun x => checkRows (p x) (s x) (m x) (z x) (t x) (oi x) (ii x) := by
  apply computable_map ho
  change Computable fun v : X × CheckIndex =>
    (ii v.1).map fun a => checkEntry (p v.1) (s v.1) (m v.1) (z v.1) (t v.1) v.2 a
  apply computable_map (hi.comp Computable.fst)
  let S := (X × CheckIndex) × CheckIndex
  have hx : Computable (fun v : S => v.1.1) := Computable.fst.comp Computable.fst
  exact (computable_checkEntry (hp.comp hx) (hs.comp hx) (hm.comp hx) (hz.comp hx) (ht.comp hx)
    (Computable.snd.comp Computable.fst) Computable.snd).to₂

theorem computable_spelled_checkTable {p s m : X → ℕ} {t : X → Raw.Tape} {oi ii : X → List CheckIndex}
    (hp : Computable p) (hs : Computable s) (hm : Computable m)
    (ht : Computable t) (ho : Computable oi) (hi : Computable ii) :
    Computable fun x => spelledTable (checkTable (p x) (s x) (m x) (t x) (oi x) (ii x)) := by
  have powers : Primrec (fun m : ℕ => 2^m) :=
    KernelComputableAddress.primrec_pow (Primrec.const 2) Primrec.id
  apply computable_spelled_tagged (enc := fun (_ : X) => numeral)
    (Primrec.list_range.to_comp.comp (powers.to_comp.comp hm)) (primrec_spelling_numeral.to_comp.comp Computable.snd).to₂
  exact (computable_spelled_matrixTable (Computable.succ.comp (hp.comp Computable.fst))
    (Computable.list_length.comp (hi.comp Computable.fst))
    (computable_checkRows (hp.comp Computable.fst) (hs.comp Computable.fst) (hm.comp Computable.fst)
      Computable.snd (ht.comp Computable.fst) (ho.comp Computable.fst) (hi.comp Computable.fst))).to₂

theorem effective_checkCommand {p s m : X → ℕ} {t : X → Raw.Tape} {oi ii : X → List CheckIndex}
    (hp : Computable p) (hs : Computable s) (hm : Computable m)
    (ht : Computable t) (ho : Computable oi) (hi : Computable ii) :
    Effective ltr fun x => checkCommand (p x) (s x) (m x) (t x) (oi x) (ii x) :=
  RegisterTable.effective (computable_spelled_checkTable hp hs hm ht ho hi)

end InterchangeROMTable

end NearSquareRoot
end Computability
end OAI
