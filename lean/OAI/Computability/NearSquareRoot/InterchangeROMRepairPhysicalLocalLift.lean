import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalLocal
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalBounded
import OAI.Computability.NearSquareRoot.InterchangeROMTableDecode
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoomROM
import OAI.Computability.NearSquareRoot.InterchangeTable

/-! # Packed execution of the five local Hermite matrices

Each input lane carries a full address stream. Every address may have a
different number of payload positions. The numeric matrix is applied to the
residue vector at every such position in one P192 program.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical.LocalTable.Lift

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  InterchangeROM InterchangeROMTable LoomRegisters CommonRegisters Space GeneratorSyntax Raw

def coefficients (p rows cols : ℕ) (f : Raw.Mat) :=
  gatherRows p (List.range rows) (List.range cols) f

private theorem range_ofFn (n : ℕ) (f : ℕ → ℕ) :
    (List.range n).map f = List.ofFn (fun j : Fin n => f j.val) := by
  apply List.ext_getElem
  · simp
  · intro i hi h'
    simp

private theorem coefficient_rows (p n c : ℕ) (f : Raw.Mat) :
    coefficients p n c f = List.ofFn (fun i => residues (Raw.interpret p n c f i)) := by
  unfold coefficients gatherRows
  apply List.ext_getElem
  · simp
  · intro i hi h'
    simp only [List.getElem_map,List.getElem_range,List.getElem_ofFn]
    simpa only [Raw.interpret,residues,ZMod.val_natCast] using range_ofFn c (fun j => f i j % (p+1))

def bytes (p r c : ℕ) (f : Raw.Mat) : SpellingTable :=
  spelledTable (matrixTable (p+1) c (coefficients p r c f))

def matrixCommand (p r c : ℕ) (f : Raw.Mat) : Cmd :=
  underHeader (romPayload 0 r (bytes p r c f))

theorem matrixCommand_within (p r c : ℕ) (f : Raw.Mat) : Within 4 (matrixCommand p r c f) :=
  underHeader_within (by decide) (romPayload_within ..)

abbrev Vector {A : Type} (P : A → Type) (p n : ℕ) := (a : A) → P a → Fin n → ZMod (p+1)

def render {A : Type} {P : A → Type} {p n : ℕ} (rows : Series A) (pay : (a : A) → Series (P a))
    (x : Vector P p n) : List Tree :=
  List.ofFn fun i => stripe rows fun a => stripe (pay a) fun j => numeral (x a j i).val

theorem render_length {A : Type} {P : A → Type} {p n : ℕ} (rows : Series A) (pay : (a : A) → Series (P a))
    (x : Vector P p n) : (render rows pay x).length = n := List.length_ofFn

private theorem stripe_render {A : Type} {P : A → Type} {p n : ℕ} (rows : Series A)
    (pay : (a : A) → Series (P a)) (x : Vector P p n) :
    Task.forest id (render rows pay x) =
      stripe (Series.natural n) (fun i => stripe rows fun a => stripe (pay a) fun j => numeral (x a j i).val) := by
  simp only [render,List.ofFn_eq_map,stripe,Series.tab,Series.natural,Series.fixed]

def applyMatrix {A : Type} {P : A → Type} {p c : ℕ} (r : ℕ) (f : Raw.Mat)
    (x : Vector P p c) : Vector P p r := fun a j => act r c f (x a j)

def charge (p r c : ℕ) (f : Raw.Mat) (H : Tree) (addresses width : ℕ) (bank : List Tree) : Allowance :=
  let D := romPayloadFactor c r (bytes p r c f) * (addresses*(width+1)+1)
  let time := 84*H.count + D + 11
  ⟨time, (packet H bank).count+time, time⟩

theorem matrixCommand_bounded {p r c : ℕ} (hc : 0 < c) (f : Raw.Mat) (H : Tree)
    {A : Type} {P : A → Type} (rows : Series A) (pay : (a : A) → Series (P a)) (width : ℕ)
    (hw : ∀ a, (pay a).count ≤ width) (x : Vector P p c) (env : Env) (deck : Deck) (base : ℕ)
    (hd : DeckCap base deck) :
    let v := render rows pay x
    let a := charge p r c f H rows.count width v
    BoundedFits env (matrixCommand p r c f) (pile 0 (packet H v) deck)
      (pile 0 (packet H (render rows pay (applyMatrix r f x))) deck) a.time (base+a.cap) a.depth := by
  let D := romPayloadFactor c r (bytes p r c f) * (rows.count*(width+1)+1)
  let d := pile 1 H deck
  have leaf :
      Fits env (romPayload 0 r (bytes p r c f)) (pile 0 (Task.forest id (render rows pay x)) d)
        (pile 0 (Task.forest id (render rows pay (applyMatrix r f x))) d) D := by
    have h := (romMatrix_bounded (⟨0,hc⟩ : Fin c) (Raw.interpret p r c f) rows pay width hw x env d _ (hd.pile 1 H)).fits
    simpa only [D,bytes,coefficient_rows,stripe_render,applyMatrix,act] using h
  let u := Task.forest id (render rows pay x)
  let v := Task.forest id (render rows pay (applyMatrix r f x))
  have mv := fits_move (i:=0) (j:=1) (u:=2) (by decide) (by decide) H env (pile 0 u deck)
  have back := fits_move (i:=1) (j:=0) (u:=2) (by decide) (by decide) H env (pile 0 v deck)
  rw [pile_comm 1 _ deck 0 _ (by decide)] at mv back
  have full : Fits env (matrixCommand p r c f) (pile 0 (.fork H u) deck) (pile 0 (.fork H v) deck)
      (84*H.count+D+11) := (fits_pair (mv.join (leaf.join
        (back.join (fits_pack _ _ _ _ _))))).mono (by omega)
  exact BoundedFits.of_fits full (fun i => by
    have := hd.pile 0 (packet H (render rows pay x)) i
    change (letters (pile 0 (packet H (render rows pay x)) deck) i).length + (84*H.count+D+11) ≤
      base+((packet H (render rows pay x)).count + (84*H.count+D+11))
    omega) le_rfl

abbrev inputs (k : Kind) (l w s : ℕ) := input k (l*w) (l*s)
abbrev outputs (k : Kind) (l w s : ℕ) := output k (l*w) (l*s)

def command (k : Kind) (p l w s m half : ℕ) (t : Tape) : Cmd :=
  matrixCommand p (outputs k l w s) (inputs k l w s) (matrix k p l w s m half t)

/-- The coefficient of the local linear scan is part of the arithmetic ROM
and can be evaluated before any address stream is opened. -/
def factor (k : Kind) (p l w s m half : ℕ) (t : Tape) : ℕ :=
  let r := outputs k l w s
  let c := inputs k l w s
  romPayloadFactor c r (bytes p r c (matrix k p l w s m half t))

theorem primrec_factor {X : Type} [Primcodable X] (k : Kind)
    {p l w s m half : X → ℕ} {t : X → Tape} (hp : Primrec p) (hl : Primrec l)
    (hw : Primrec w) (hs : Primrec s) (hm : Primrec m) (hh : Primrec half) (ht : Primrec t) :
    Primrec fun x => factor k (p x) (l x) (w x) (s x) (m x) (half x) (t x) := by
  have ni := pr_input k (Primrec.nat_mul.comp hl hw) (Primrec.nat_mul.comp hl hs)
  have no := pr_output k (Primrec.nat_mul.comp hl hw) (Primrec.nat_mul.comp hl hs)
  exact primrec_romPayloadFactor ni no (primrec_spelled_matrixTable (Primrec.succ.comp hp) ni
    (primrec_gatherRows hp (Primrec.list_range.comp no) (Primrec.list_range.comp ni) (pr_matrix k hp hl hw hs hm hh ht)))

theorem command_within (k : Kind) (p l w s m half : ℕ) (t : Tape) :
    Within 4 (command k p l w s m half t) := matrixCommand_within ..

theorem effective_command_pr {X : Type} [Primcodable X] (k : Kind)
    {p l w s m half : X → ℕ} {t : X → Tape} (hp : Primrec p) (hl : Primrec l)
    (hw : Primrec w) (hs : Primrec s) (hm : Primrec m) (hh : Primrec half) (ht : Primrec t) :
    Effective ltr fun x => command k (p x) (l x) (w x) (s x) (m x) (half x) (t x) := by
  have ni := pr_input k (Primrec.nat_mul.comp hl hw) (Primrec.nat_mul.comp hl hs)
  have no := pr_output k (Primrec.nat_mul.comp hl hw) (Primrec.nat_mul.comp hl hs)
  have nf := pr_matrix k hp hl hw hs hm hh ht
  exact effective_underHeader (effective_romMatrix (Primrec.succ.comp hp).to_comp ni.to_comp no.to_comp
    (.const 0) (primrec_gatherRows hp (Primrec.list_range.comp no) (Primrec.list_range.comp ni) nf).to_comp)

open private stripe_symbols_injective from OAI.Computability.NearSquareRoot.InterchangeTable

variable {A : Type} {P : A → Type} (rows : Series A) (pay : (a : A) → Series (P a))

theorem render_injective {p n : ℕ} : Function.Injective (render (p:=p) (n:=n) rows pay) := by
  intro x y h
  have hi := List.ofFn_inj.mp h
  funext a j i
  have hrow := congrFun hi i
  have H : (fun a => stripe (pay a) (fun j => numeral (x a j i).val)) =
      (fun a => stripe (pay a) (fun j => numeral (y a j i).val)) :=
    stripe_symbols_injective rows (symbol:=id) Function.injective_id hrow
  have Hj : (fun j => (x a j i).val) = (fun j => (y a j i).val) :=
    stripe_symbols_injective (pay a) numeral_injective (congrFun H a)
  exact ZMod.val_injective _ (congrFun Hj j)

def catVec {p n q : ℕ} (x : Vector P p n) (y : Vector P p q) : Vector P p (n+q) :=
  fun a j => cat (x a j) (y a j)

@[simp] theorem render_cat {p n q : ℕ} (x : Vector P p n) (y : Vector P p q) :
    render rows pay (catVec x y) = render rows pay x ++ render rows pay y := by
  have left (i : Fin n) (a : A) (j : P a) :
      Fin.addCases (x a j) (y a j) (i.castLE (Nat.le_add_right n q)) = x a j i := Fin.addCases_left _
  simp only [render,catVec,cat,List.ofFn_add,left,Fin.addCases_right]

/-- The ordinary list semantics on a well-formed packed bank. The actual
command runs directly on the tape, including all changes of row order. -/
noncomputable def eval (k : Kind) (p l w s m half : ℕ) (t : Tape) (xs : List Tree) : List Tree :=
  let x : Vector P p (inputs k l w s) := Function.invFun (render rows pay) xs
  render rows pay (applyMatrix (outputs k l w s) (matrix k p l w s m half t) x)

def domain (p n : ℕ) (xs : List Tree) : Prop := xs ∈ Set.range (render (p:=p) (n:=n) rows pay)

theorem eval_render (k : Kind) (p l w s m half : ℕ) (t : Tape) (x : Vector P p (inputs k l w s)) :
    eval rows pay k p l w s m half t (render rows pay x) =
      render rows pay (applyMatrix (outputs k l w s) (matrix k p l w s m half t) x) := by
  unfold eval
  rw [Function.leftInverse_invFun (render_injective ..)]

theorem bounded (k : Kind) {p l w s m half : ℕ} (t : Tape) (hn : 0 < l*w) (H : Tree)
    (width : ℕ) (hw : ∀ a, (pay a).count ≤ width) (xs : List Tree)
    (hx : domain rows pay p (inputs k l w s) xs) (env : Env) (r : Deck) (base : ℕ) (hd : DeckCap base r) :
    let z := charge p (outputs k l w s) (inputs k l w s) (matrix k p l w s m half t) H rows.count width xs
    BoundedFits env (command k p l w s m half t) (pile 0 (packet H xs) r)
      (pile 0 (packet H (eval rows pay k p l w s m half t xs)) r) z.time (base+z.cap) z.depth := by
  obtain ⟨x, rfl⟩ := hx
  rw [eval_render]
  apply matrixCommand_bounded _ _ H rows pay width hw x env r base hd
  cases k <;> simp only [inputs,input] <;> omega

end InterchangeROMRepair.Physical.LocalTable.Lift

end NearSquareRoot
end Computability
end OAI
