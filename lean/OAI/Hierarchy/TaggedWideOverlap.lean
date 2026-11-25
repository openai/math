import OAI.Hierarchy.TaggedBinaryBarrelTurns

namespace OAI
/-! # Physical equality on the overlapping passive portions of two named rows -/

noncomputable section
namespace Hierarchy.Tagged.PassiveWindow
open ThreeFlat Routing
open scoped Classical

/-- Original ordinal prefix, original width, and total low active length on
this chord, before taking the high passive suffix of the tensor product. -/
structure Slice where
  start : ℕ
  width : ℕ
  low : ℕ

def lo (l r : Slice) := max (l.start-l.low) (r.start-r.low)
def hi (l r : Slice) := min (l.start+l.width-l.low) (r.start+r.width-r.low)
def span (l r : Slice) := hi l r-lo l r
def offset (l r : Slice) (i : Bool) := let a := if i then r else l; lo l r+a.low-a.start

theorem span_bound (l r : Slice) : span l r ≤ l.width ∧ span l r ≤ r.width := by
  simp only [span,hi,lo]
  omega

theorem offsets (l r : Slice) {j : ℕ} (used : j<span l r) :
    j+offset l r false<l.width ∧ j+offset l r true<r.width ∧
    (l.start+(j+offset l r false)=lo l r+j+l.low) ∧
    (r.start+(j+offset l r true)=lo l r+j+r.low) := by
  simp only [span,hi,lo,offset,Bool.false_eq_true,↓reduceIte] at *
  omega

theorem live_at (l r : Slice) {t a b : ℕ} (aFit : a<l.width) (bFit : b<r.width)
    (left : l.start+a=t+l.low) (right : r.start+b=t+r.low) :
    ∃j,j<span l r ∧ a=j+offset l r false ∧ b=j+offset l r true := by
  refine ⟨t-lo l r,?_⟩
  simp only [span,hi,lo,offset,Bool.false_eq_true,↓reduceIte] at *
  omega

def data {W : ℕ} (x y : Bits W) : Bool → Bits W := fun b=>if b then y else x

def header (W : ℕ) (l r : Slice) (same : Bool) : Fin (W+1) :=
  ⟨if same then min W (span l r) else 0,by split <;> omega⟩

def heads (W : ℕ) (l r : Slice) : Bool → Fin (W+1) :=
  fun b=>⟨min W (offset l r b),by omega⟩

private theorem shift_head {W : ℕ} (l r : Slice) (side : Bool) (word : Bits W)
    (j : Fin W) (inside : j.val + offset l r side < W) :
    Barrel.shift word (heads W l r side).val j = word ⟨_,inside⟩ := by
  have bounded : offset l r side ≤ W := by omega
  simp only [heads,Nat.min_eq_right bounded,Barrel.shift,dite_eq_left inside]

/-- Both raw words are hardwired physical role slots. Only live length and
the two head offsets are read from the native router. -/
theorem value {F : Type*} [Field F] {W : ℕ} (l r : Slice) (same : Bool)
    (left : l.width ≤ W) (right : r.width ≤ W) (x y : Bits W) :
    TypedWiring.value (BinaryBarrelTurns.fixed F W)
      (BinaryBarrelTurns.pins ((addressEquiv _).symm (BinaryBarrelTurns.address (header W l r same)))
        (fun b=>(addressEquiv _).symm (BinaryBarrelTurns.address (heads W l r b))) (data x y)) =
      if ∀t (a : Fin l.width) (b : Fin r.width),same=true → l.start+a.val=t+l.low → r.start+b.val=t+r.low→
        x (a.castLE left)=y (b.castLE right) then 1 else 0 := by
  rw [BinaryBarrelTurns.fixed_value]
  apply ite_congr ?_ (fun _=>rfl) (fun _=>rfl)
  apply propext
  cases same with
  | false=>simp [header]
  | true=>
    have bound := (span_bound l r).1.trans left
    simp only [header,↓reduceIte,Nat.min_eq_right bound,true_implies]
    constructor
    · intro checks t a b atLeft atRight
      obtain ⟨j,live,eqA,eqB⟩ := live_at l r a.isLt b.isLt atLeft atRight
      have both := offsets l r live
      have chk := checks ⟨j,live.trans_le bound⟩ live
      have lx := both.1.trans_le left
      have rx := both.2.1.trans_le right
      rw [shift_head l r false _ _ lx,shift_head l r true _ _ rx] at chk
      change x ⟨_,lx⟩ = y ⟨_,rx⟩ at chk
      have ia : (⟨_,lx⟩ : Fin W) = a.castLE left := Fin.ext eqA.symm
      have ib : (⟨_,rx⟩ : Fin W) = b.castLE right := Fin.ext eqB.symm
      simpa only [ia,ib] using chk
    · intro consistent j live
      have both := offsets l r live
      rw [shift_head l r false _ _ (both.1.trans_le left),shift_head l r true _ _ (both.2.1.trans_le right)]
      exact consistent (lo l r+j.val) ⟨_,both.1⟩ ⟨_,both.2.1⟩ both.2.2.1 both.2.2.2

end Hierarchy.Tagged.PassiveWindow

end
end OAI
