import OAI.Computability.NearSquareRoot.InterchangeROMTableCommand

/-! # A sign-indexed matrix lookup in one effective two-register command

A tagged bank word is a pair of its sign code and its complete input stripe.
The command contains a table for each possible sign pattern. It accepts each
physical word in the corresponding correction row, independent of all other
payload positions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMTable

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open InterchangeROMRepair GeneratorSyntax

def tagRows (tag : Tree) (t : List (Tree × Tree)) :=
  t.map fun kv => (Tree.fork tag kv.1, kv.2)

def tagged {A : Type} (tags : List A) (enc : A → Tree) (t : A → List (Tree × Tree)) :=
  tags.flatMap fun a => tagRows (enc a) (t a)

private theorem read_other (x a b : Tree) (e : a ≠ b) (t s : List (Tree × Tree)) :
    RegisterLookup.read (tagRows a t ++ s) (.fork b x) = RegisterLookup.read s (.fork b x) := by
  induction t with
  | nil => rfl
  | cons kv t ih =>
    simp only [tagRows,List.map_cons,List.cons_append,RegisterLookup.read,Tree.fork.injEq,e,
      false_and,ite_false]
    exact ih

private theorem read_same (x y a : Tree) (t s : List (Tree × Tree)) (hm : (x,y) ∈ t) :
    RegisterLookup.read (tagRows a t ++ s) (.fork a x) = RegisterLookup.read t x := by
  induction t with
  | nil => cases hm
  | cons kv t ih =>
    simp only [tagRows,List.map_cons,List.cons_append,RegisterLookup.read,Tree.fork.injEq,
      true_and]
    by_cases e : kv.1 = x
    · simp [e]
    · simp only [e,ite_false]
      apply ih
      exact (List.mem_cons.mp hm).resolve_left (fun h => e (congrArg Prod.fst h).symm)

theorem tagged_correct {A : Type} (tags : List A) (enc : A → Tree) (he : Function.Injective enc)
    (t : A → List (Tree × Tree)) (a : A) (x y : Tree) (ha : a ∈ tags)
    (h : RegisterLookup.read (t a) x = y ∧ (x,y) ∈ t a) :
    RegisterLookup.read (tagged tags enc t) (.fork (enc a) x) = y ∧
      (.fork (enc a) x,y) ∈ tagged tags enc t := by
  refine ⟨?_, List.mem_flatMap.mpr ⟨a,ha,List.mem_map.mpr ⟨(x,y),h.2,rfl⟩⟩⟩
  induction tags with
  | nil => cases ha
  | cons b l ih =>
    change RegisterLookup.read (tagRows (enc b) (t b) ++ tagged l enc t) _ = _
    by_cases e : a = b
    · subst b
      exact (read_same x y (enc a) (t a) _ h.2).trans h.1
    · rw [read_other x _ _ (he.ne (Ne.symm e))]
      exact ih ((List.mem_cons.mp ha).resolve_left e)

variable {X A : Type} [Primcodable X] [Primcodable A]

theorem computable_spelled_tagged {tags : X → List A} {enc : X → A → Tree}
    {t : X → A → List (Tree × Tree)} (ht : Computable tags)
    (he : Computable₂ fun x a => spelling (enc x a))
    (hm : Computable₂ fun x a => spelledTable (t x a)) :
    Computable fun x => spelledTable (tagged (tags x) (enc x) (t x)) := by
  let row (v : X × A) (w : List ℕ × List ℕ) := (2 :: spelling (enc v.1 v.2) ++ w.1, w.2)
  have hr : Computable₂ row :=
    (Computable.pair (Computable.list_cons.comp (Computable.const 2) (Computable.list_append.comp
      (he.comp (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.fst))
      (Computable.fst.comp Computable.snd))) (Computable.snd.comp Computable.snd)).to₂
  have piece : Computable fun v : X × A => (spelledTable (t v.1 v.2)).map (row v) :=
    computable_map hm hr
  have gen := Primrec.list_flatten.to_comp.comp (computable_map ht piece.to₂)
  apply gen.of_eq
  intro x
  simp [row,spelledTable,tagged,tagRows,List.flatMap_def,Function.comp_def]

def correctSlot (m mask : ℕ) (out inp : Bool) : ℕ := 3+m+4*mask+2*out.toNat+inp.toNat

def correctionTable (p s m : ℕ) (out inp : Bool) (tape : Raw.Tape) (outIdx inIdx : List ℕ) :=
  tagged (List.range (2^m)) numeral fun z => slotTable p s (correctSlot m z out inp) tape outIdx inIdx

theorem correctionTable_correct {p w s m : ℕ} (η : Fin m → Bool) (out inp : Bool) (tape : Raw.Tape)
    (input output : Series (Fin s)) (x : Fin s → ZMod (p+1)) :
    let t := correctionTable p s m out inp tape (output.tab Fin.val) (input.tab Fin.val)
    let K := (Raw.decode p w s m tape).correct η out inp
    let u := Tree.fork (numeral (Raw.mask η).val) (stripe input fun j => numeral (x j).val)
    let v := stripe output (fun i => numeral (K.mulVec x i).val)
    RegisterLookup.read t u = v ∧ (u,v) ∈ t :=
  tagged_correct _ _ numeral_injective _ (Raw.mask η).val _ _ (List.mem_range.mpr (Raw.mask η).isLt)
    (slotTable_correct p _ tape input output x)

private theorem computable_toNat {s : X → Bool} (hs : Computable s) :
    Computable fun x => (s x).toNat := by
  apply (Computable.cond hs (Computable.const 1) (Computable.const 0)).of_eq
  intro x
  cases s x <;> rfl

theorem effective_correctionCommand {p s m : X → ℕ} {out inp : X → Bool}
    {tape : X → Raw.Tape} {outIdx inIdx : X → List ℕ} (hp : Computable p)
    (hs : Computable s) (hm : Computable m) (ho : Computable out) (hi : Computable inp)
    (ht : Computable tape) (hout : Computable outIdx) (hin : Computable inIdx) :
    Effective ltr (fun x => RegisterTable.command
      (correctionTable (p x) (s x) (m x) (out x) (inp x) (tape x) (outIdx x) (inIdx x))) := by
  apply RegisterTable.effective
  have powers : Primrec (fun m : ℕ => 2^m) :=
    KernelComputableAddress.primrec_pow (Primrec.const 2) Primrec.id
  change Computable fun x => spelledTable (tagged (List.range (2^(m x))) numeral
    (fun z => slotTable (p x) (s x) (correctSlot (m x) z (out x) (inp x)) (tape x) (outIdx x) (inIdx x)))
  apply computable_spelled_tagged (enc := fun (_ : X) => numeral) (Primrec.list_range.to_comp.comp (powers.to_comp.comp hm))
    (primrec_spelling_numeral.to_comp.comp Computable.snd).to₂
  apply computable_spelled_slotTable (hp.comp Computable.fst) (hs.comp Computable.fst) _
    (ht.comp Computable.fst) (hout.comp Computable.fst) (hin.comp Computable.fst)
  let add := (@Primrec.nat_add).to_comp
  let mul := (@Primrec.nat_mul).to_comp
  exact add.comp (add.comp (add.comp (add.comp (Computable.const 3) (hm.comp Computable.fst))
    (mul.comp (Computable.const 4) Computable.snd))
    (mul.comp (Computable.const 2) ((computable_toNat ho).comp Computable.fst)))
    ((computable_toNat hi).comp Computable.fst)

theorem correctionCommand_run {p w s m : ℕ} (η : Fin m → Bool) (out inp : Bool)
    (tape : Raw.Tape) (input output : Series (Fin s)) (x : Fin s → ZMod (p+1))
    (env : Env) (r : Deck) :
    let t := correctionTable p s m out inp tape (output.tab Fin.val) (input.tab Fin.val)
    let K := (Raw.decode p w s m tape).correct η out inp
    let u := Tree.fork (numeral (Raw.mask η).val) (stripe input fun j => numeral (x j).val)
    let v := stripe output (fun i => numeral (K.mulVec x i).val)
    Fits env (RegisterTable.command t) (pile 0 u r) (pile 0 v r) (RegisterTable.cost t) := by
  have h := correctionTable_correct (w := w) η out inp tape input output x
  exact RegisterTable.run_lookup _ _ _ h.2 h.1 env r

end InterchangeROMTable

end NearSquareRoot
end Computability
end OAI
