import OAI.Computability.IntegerMultiplication.Spindle.Silver

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Spindle
open Loom Strip Dims Adic Code
variable (p m j : ℕ) (P G B : Tape)
noncomputable section
private theorem Fieldplus :
    Nonempty (Adopt ((line p m).cart (line p j)) (line p (m+j))) := by
  suffices t : field p (m+j)=field p m++field p j by
    -- transport
    let u := unite (field p m) (field p j)
    unfold line
    rw [t]; exact ⟨u⟩
  induction m with
  | zero => simp [field]
  | succ m ih => rw [Nat.add_right_comm, field,ih,field,List.cons_append]
def fPlus := Classical.choice (Fieldplus p m j)
abbrev part := (line p m).cart (line p j)
abbrev Bundle := Block p m × Block p j
abbrev Flats := SpanKey P G B (Bundle p m j)
abbrev Lays := Path P (part p m j) G (part p m j) B

def closed : Adopt (Lays p m j P G B) (stock p P G B (m+j)) :=
  let a := fPlus p m j
  (Adopt.same _).split (a.split ((Adopt.same _).split (a.split (Adopt.same _))))
theorem closed_keep (z : Flats p m j P G B) :
    (closed p m j P G B).cast (swapper P G B z)=swapper P G B ((closed p m j P G B).cast z) := rfl

def outside : Adopt (Lays p m j P G B) (stock p P (field p j++G) (field p j++B) m) :=
  let g := layout G
  let b := layout B
  let M := line p m; let J := line p j
  -- ((M×J) × B) to M × (J++ B)
  let tail := (Adopt.rotate M J b).thenDo ((Adopt.same M).split (unite _ _))
  -- ((M × J) × (g × ((M×J)×b))) to M× ((J++g) × tail)
  let d := g.cart (M.cart (layout (field p j++B)))
  ⟨(((Adopt.same (layout P)).split (((Adopt.same (M.cart J)).split ((Adopt.same g).split tail)).thenDo
    ((Adopt.rotate M J d).thenDo ((Adopt.same M).split
      ((Adopt.rotate J g _).back.thenDo ((unite _ _).split (Adopt.same _)))))))).cast,
    (((Adopt.same (layout P)).split (((Adopt.same (M.cart J)).split ((Adopt.same g).split tail)).thenDo
    ((Adopt.rotate M J d).thenDo ((Adopt.same M).split
      ((Adopt.rotate J g _).back.thenDo ((unite _ _).split (Adopt.same _)))))))).route⟩
def opA (z : Flats p m j P G B) : Flats p m j P G B :=
  (z.1,(z.2.2.2.1.1,z.2.1.2),z.2.2.1,(z.2.1.1,z.2.2.2.1.2),z.2.2.2.2)
theorem out_keep (z : Flats p m j P G B) :
    (outside p m j P G B).cast (opA _ _ _ _ _ _ z) =
      swapper _ _ _ ((outside p m j P G B).cast z) := rfl

def inside : Adopt (Lays p m j P G B) (stock p (P++field p m) (G++field p m) B j) :=
  let _g := layout G
  let b := layout B
  let l := layout P
  let M := line p m; let J := line p j
  let a (Q:Tape) {I : Type} (s : Series I) :
      Adopt ((layout Q).cart ((M.cart J).cart s)) ((layout (Q++field p m)).cart (J.cart s)) :=
    ((Adopt.same _).split (Adopt.rotate M J s)).thenDo
      ((Adopt.rotate (layout Q) M _).back.thenDo ((unite _ _).split (Adopt.same _)))
  ((Adopt.same l).split ((Adopt.same (M.cart J)).split (a G b))).thenDo (a P _)
def opB (z : Flats p m j P G B) : Flats p m j P G B :=
  (z.1,(z.2.1.1,z.2.2.2.1.2),z.2.2.1,(z.2.2.2.1.1,z.2.1.2),z.2.2.2.2)
theorem in_keep (z : Flats p m j P G B) :
    (inside p m j P G B).cast (opB _ _ _ _ _ _ z) =
      swapper _ _ _ ((inside p m j P G B).cast z) := rfl
theorem two (z : Flats p m j P G B) :
    opA p m j P G B (opB p m j P G B z)=swapper _ _ _ z := rfl

end
end Spindle

end IntegerMultiplication
end Computability
end OAI
