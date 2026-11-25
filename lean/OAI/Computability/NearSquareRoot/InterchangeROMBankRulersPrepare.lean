import OAI.Computability.NearSquareRoot.InterchangeROMExpose
import OAI.Computability.NearSquareRoot.InterchangeBatchIndices

/-! # Preparing the compact dimensions of a center-stage bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBankRulers

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Loom
  IntegerMultiplication.Adic IntegerMultiplication.Staff NearSquareRoot.InterchangeROMAddress

abbrev Raw := (Tally × Tally × Tally) × Header
abbrev Support := Tally × Tally × Header

private def uncons {A : Type} (l : List A) := (cutLists (tally 1,l)).2

@[fun_prop] private theorem uncons_easy {A : Type} [Codec A] : Easy (uncons (A:=A)) :=
  (easy_cut (show Easy (fun l : List A => (tally 1,l)) from by fun_prop)).sndCompose

private def before (x : Raw) := (uncons x.2.2.1.reverse).reverse

@[fun_prop] private theorem before_poly : Poly before := by
  apply Easy.poly
  unfold before
  fun_prop

private def group (x : Raw) := (quot (uncons (x.1.2.1 ++ x.1.1),x.1.1)).1

private theorem glue {X A : Type} [Codec X] [Codec A] {f g : X → List A}
    (hf : Poly f) (hg : Poly g) : Poly (fun x => f x ++ g x) :=
  (hf.pair hg).compose Easy.append.poly

attribute [local fun_prop] glue

@[fun_prop] private theorem group_poly : Poly group := by
  let cut := ((Easy.append (X:=Unit)).compose uncons_easy).poly
  have u := (show Poly (fun x : Raw => (x.1.2.1,x.1.1)) from by fun_prop).compose cut
  exact (u.pair (by fun_prop)).compose stable_q |>.fstCompose

private def rack (x : Raw) := copies (x.1.2.2,x.2.1.map fun _ => x.1.2.1)

@[fun_prop] private theorem rack_poly : Poly rack := by
  have pack := (show Poly (fun x : Raw => (x.2.1,x.1.2.1)) from by fun_prop).compose
    (Packed.chamber (X:=Tally))
  exact ((by fun_prop : Poly (fun x : Raw => x.1.2.2)).pair pack).compose copies_poly

/-- Both dimension words to be expanded to tally rulers, plus the two radix
sizes and the compact layout of the grouped array. -/
def prepare (x : Raw) : (List Tally × List Tally) × Support :=
  ((before x, rack x ++ x.2.2.2.1 ++ rack x ++ x.2.2.2.2),
    x.1.2.1,group x,x.2.1,before x ++ [group x],x.2.2.2)

@[fun_prop] theorem prepare_poly : Poly prepare := by
  unfold prepare
  fun_prop (disch := assumption)

theorem prepare_exact (W b n f : ℕ) (P G S : Tape) :
    prepare ((tally W,tally b,tally n),header f (P ++ [b]) G S) =
      ((shape P,shape (Rack (field b f) n ++ G ++ Rack (field b f) n ++ S)),
        tally b,tally (BatchRows.groups b W),header f (P ++ [BatchRows.groups b W]) G S) := by
  let x : Raw := ((tally W,tally b,tally n),header f (P ++ [b]) G S)
  have hbefore : before x = shape P := by simp [x,before,uncons,cutLists,header,shape]
  have hgroup : group x = tally (BatchRows.groups b W) := by
    change (quot (uncons (tally b ++ tally W),tally W)).1 = _
    rw [mergeTally]
    have h : uncons (tally (b+W)) = tally (b+W-1) := by simp [uncons,cutLists,tally,List.drop_replicate]
    rw [h,quot_r,BatchRows.groups,Nat.ceilDiv_eq_add_pred_div]
  have hrack : rack x = shape (Rack (field b f) n) := by
    change copies (tally n,(tally f).map fun _ => tally b) = _
    rw [shape_field,copy_shape]
  change prepare x = _
  simp only [prepare,hbefore,hgroup,hrack]
  simp [x,header,shape]

open InterchangeROMExpose in
theorem prepare_center (i : Input) (W : ℕ) :
    prepare ((tally W,tally i.b,tally i.n),centerHeader i) =
      ((shape i.req.before,shape (Rack (field i.b (f i)) i.n ++
        InterchangeFrame.gap i.b 1 (rem i) i.req.between ++ Rack (field i.b (f i)) i.n ++
        InterchangeFrame.post i.b (rem i) i.req.after_)),
        tally i.b,tally (BatchRows.groups i.b W),header (f i) (i.req.before ++ [BatchRows.groups i.b W])
          (InterchangeFrame.gap i.b 1 (rem i) i.req.between)
          (InterchangeFrame.post i.b (rem i) i.req.after_)) := prepare_exact ..

end InterchangeROMBankRulers

end NearSquareRoot
end Computability
end OAI
