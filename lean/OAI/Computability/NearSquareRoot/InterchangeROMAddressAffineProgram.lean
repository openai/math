import OAI.Computability.NearSquareRoot.InterchangeROMAddressDescriptor
import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineLanes
import OAI.Computability.NearSquareRoot.InterchangeROMAddressMirrorCompile
import OAI.Computability.NearSquareRoot.InterchangeROMAffineModulus
import OAI.Computability.NearSquareRoot.InterchangeROMAffineStatic

/-! # Effective affine controls on one native interchange layout -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress.Affine

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry IntegerMultiplication.Bits
  IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims IntegerMultiplication.Port
  IntegerMultiplication.Loom IntegerMultiplication.Adic CommonRegisters RegisterWitness GeneratorSyntax
  Space AffineAddress InterchangeROMAddress

noncomputable def core : Cmd := (controller InterchangeAffineMask.modulus_poly).choose

noncomputable def time (K d e : ℕ) (x : Input InterchangeAffineMask.modulus) :=
  K * ((size x.static + (input x).count + 1) + (size (x.static,x.layout)+1)^e +
    BankInput.total tag (Comparison.budget d) x.toBankInput + 1)

theorem compiled : ∃ K d e : ℕ, ∀ (x : Input InterchangeAffineMask.modulus) env deck base, DeckCap base deck →
    BoundedFits env (compile core x.static) (pile 0 (input x) deck) (pile 0 x.rows.answer deck)
      (time K d e x) (base + (input x).count + time K d e x) (time K d e x) := by
  obtain ⟨K,d,e,h⟩ := (controller InterchangeAffineMask.modulus_poly).choose_spec
  refine ⟨K,d,e,fun x env deck base hc => ?_⟩
  exact BoundedFits.of_fits (h x env deck) (fun i => Nat.add_le_add_right (hc.pile 0 (input x) i) _) le_rfl

theorem uniform_registers : ∃ R, ∀ s, Within R (compile core s) := by
  obtain ⟨R,hR,hc⟩ := ((Filter.eventually_gt_atTop (0 : ℕ)).and (RegisterSelect.within_eventually core)).exists
  exact ⟨R,fun s => ⟨(prepare_within (R:=R) (i:=0) (send s)).mpr hR,hR,hc⟩⟩

def spec {J : Type} {n : ℕ} (ord : J ≃ Fin n) (b : ℕ) (x y : Spot J) (A B : InterchangeAffineMask.Row ℕ) : Template :=
  ((location ord b x,location ord b y),InterchangeAffineMask.template A B)

private theorem emit_location {X : Type} [Primcodable X] {l : X → Location} (hl : Computable l) :
    Effective ltr fun x => Task.prepare 0 (send (l x)) := by
  have atom : Effective ltr (fun a : Bool => Task.prepare 0 (send a)) := by
    apply (Computable.cond Computable.id (Computable.const (file ltr (Task.prepare 0 (send true))))
      (Computable.const (file ltr (Task.prepare 0 (send false))))).of_eq
    intro b
    cases b <;> rfl
  exact emit_pair (atom.comp (Computable.fst.comp hl)) (emit_cuts.comp (Computable.snd.comp hl))

theorem effective {X : Type} [Primcodable X] {p n : X → ℕ} {x y : X → Bool × ℕ}
    {A B : X → InterchangeAffineMask.Row ℕ} (hp : Computable p) (hn : Computable n) (hx : Computable x) (hy : Computable y)
    (ha : Computable A) (hb : Computable B) :
    Effective ltr fun i => compile core
      ((InterchangeROMMirror.numericLocation (p i) (n i) (x i),InterchangeROMMirror.numericLocation (p i) (n i) (y i)),
        InterchangeAffineMask.template (A i) (B i)) := by
  have locs := emit_pair (emit_location (InterchangeROMMirror.computable_location hp hn hx))
    (emit_location (InterchangeROMMirror.computable_location hp hn hy))
  exact (emit_pair locs (InterchangeAffineMask.effective_literal ha hb)).join
    ((effective_const ltr (pack 0)).join (effective_const ltr core))

variable {J : Type} [DecidableEq J] {n b f : ℕ} [NeZero b] (ord : J ≃ Fin n)
  (P G S : Tape) (hp : solid P) (hg : solid G) (hs : solid S) (hb : 2 ≤ b)

omit [NeZero b] in
theorem describes (x y : Spot J) (A B : InterchangeAffineMask.Row ℕ) :
    send (build InterchangeAffineMask.modulus (spec ord b x y A B,header f P G S)) =
      Task.forest (pairDesc tag)
        ((InterchangeAffineMask.colors A B).map (nativeFaces (f:=f) ord P G S hp hg hs hb x y A B)) := by
  have head (k : InterchangeAffineMask.Class ℕ) :
      send (comparisons ((((born (b^f),InterchangeAffineMask.encoded A,InterchangeAffineMask.encoded B),
        projection (location ord b x,header f P G S),projection (location ord b y,header f P G S)),
        born k.1,born k.2))) =
      pairDesc tag (nativeFaces (f:=f) ord P G S hp hg hs hb x y A B k) := by
    simp only [nativeFaces,pairDesc,tag,AffineAddress.input,comparisons,InterchangeAffineMask.literal,Prod.swap,send_prod]
  unfold build spec InterchangeAffineMask.template
  change send (((InterchangeAffineMask.colors A B).map _).map (fun k => comparisons ((((InterchangeAffineMask.modulus (tally b,tally f),
    InterchangeAffineMask.encoded A,InterchangeAffineMask.encoded B),projection (location ord b x,header f P G S),
    projection (location ord b y,header f P G S)),k)))) = _
  rw [InterchangeAffineMask.modulus_tally,List.map_map]
  induction InterchangeAffineMask.colors A B with
  | nil => rfl
  | cons k l ih =>
    simp only [List.map_cons,send_cons,Task.forest_cons,ih,Function.comp_apply,head]

noncomputable def width (x : Spot J) (a : Span b) (v : Keys P G S J (Block b f) → Tree) :
    Input InterchangeAffineMask.modulus where
  toBankInput := widthBank ord P G S hp hg hs hb x a v
  static := spec ord b x x (InterchangeAffineMask.widthRows a.neg a.top.count a.down.count).1
    (InterchangeAffineMask.widthRows a.neg a.top.count a.down.count).2
  layout := header f P G S
  describes := describes ord P G S hp hg hs hb x x _ _

noncomputable def gather (x y : Spot J) (h : Lag.early (ranking ord) x y) (a : Pinpoint b)
    (v : Keys P G S J (Block b f) → Tree) : Input InterchangeAffineMask.modulus where
  toBankInput := gatherBank ord P G S hp hg hs hb x y h a v
  static := spec ord b x y (InterchangeAffineMask.pinRows a).1 (InterchangeAffineMask.pinRows a).2
  layout := header f P G S
  describes := describes ord P G S hp hg hs hb x y _ _

end InterchangeROMAddress.Affine

end NearSquareRoot
end Computability
end OAI
