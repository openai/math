import OAI.Computability.NearSquareRoot.InterchangeROMAffineLag
import OAI.Computability.NearSquareRoot.InterchangeROMAddressEffective

/-! # Effective ROM generation of affine coefficients and carry classes -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeAffineMask

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry IntegerMultiplication.Bits
  GeneratorSyntax InterchangeROMAddress

abbrev Static := (Row Word × Row Word) × List (Class Word)

/-- Static geometry and carry classes are independent of the live
address width. The modulus is supplied by the runtime header program. -/
def template (A B : Row ℕ) : Static :=
  ((encoded A,encoded B),(colors A B).map fun k => (born k.1,born k.2))

def rowWeight (A : Row ℕ) := A.1+A.2.1+A.2.2

theorem colors_length (A B : Row ℕ) :
    (colors A B).length=(rowWeight A+1)*(rowWeight B+1) := by
  change (List.range (rowWeight A+1) ×ˢ List.range (rowWeight B+1)).length=_
  simp [List.length_product]

private theorem encoded_size (A : Row ℕ) : size (encoded A) ≤ 2*rowWeight A+5 := by
  simp only [encoded,rowWeight,size_prod,size_word]
  have ha := birthLen A.1
  have hb := birthLen A.2.1
  have hc := birthLen A.2.2
  omega

private theorem catalog_size {α β : Type} [Codec β] (f : α → β) (xs : List α) (C : ℕ)
    (h : ∀ x∈xs, size (f x)+1≤C) : size (xs.map f) ≤ xs.length*C+1 := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have e := h x List.mem_cons_self
    have t := ih (fun y hy => h y (List.mem_cons_of_mem _ hy))
    simp only [List.map_cons,size_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

/-- A cubic numerical majorant for the ROM's complete literal coefficient
and carry catalog, independent of the live row and address width. -/
theorem template_size (A B : Row ℕ) : size (template A B) ≤ 20*(rowWeight A+rowWeight B+1)^3 := by
  let C := 2*(rowWeight A+rowWeight B)+4
  let ids (k : Class ℕ) := (born k.1,born k.2)
  have h := catalog_size ids (colors A B) C (by
    rintro ⟨x,y⟩ hin
    obtain ⟨hx,hy⟩ := List.mem_product.mp hin
    change x∈List.range (rowWeight A+1) at hx
    change y∈List.range (rowWeight B+1) at hy
    have a := List.mem_range.mp hx
    have b := List.mem_range.mp hy
    have u := birthLen x
    have v := birthLen y
    simp only [ids,size_prod,size_word,C]
    omega)
  rw [colors_length] at h
  have u := encoded_size A
  have v := encoded_size B
  change size (encoded A)+size (encoded B)+1+size ((colors A B).map ids)+1 ≤ _
  change _ ≤ (rowWeight A+1)*(rowWeight B+1)*(2*(rowWeight A+rowWeight B)+4)+1 at h
  let W := rowWeight A+rowWeight B+1
  have ha : rowWeight A+1≤W := by dsimp only [W]; omega
  have hb : rowWeight B+1≤W := by dsimp only [W]; omega
  have hc : 2*(rowWeight A+rowWeight B)+4≤4*W := by dsimp only [W]; omega
  have cat := Nat.mul_le_mul (Nat.mul_le_mul ha hb) hc
  have normalization : W*W*(4*W)=4*W^3 := by ring
  rw [normalization] at cat
  have wpos : 1≤W := Nat.succ_pos _
  have lift : W≤W^3 := by simpa only [pow_one] using (Nat.pow_le_pow_right wpos (by decide : 1≤3))
  change _ ≤ 20*W^3
  dsimp only [W] at lift ⊢
  dsimp only [W] at cat
  omega

/-- Binary numeral formation is effective even when the schedule and its
alphabet size vary. -/
theorem primrec_born : Primrec born := by
  let expand (_ : Unit) (l : List Word) : Option Word :=
    some (if l.length=0 then [] else parity l.length :: l.getD (l.length/2) [])
  have h : Primrec₂ expand := by
    have len : Primrec (fun p : Unit × List Word => p.2.length) := Primrec.list_length.comp .snd
    have dig : Primrec (fun p : Unit × List Word => parity p.2.length) :=
      (Primrec.eq.comp (Primrec.nat_mod.comp len (Primrec.const 2)) (Primrec.const 1)).decide
    exact (Primrec.option_some.comp (Primrec.ite (Primrec.eq.comp len (Primrec.const 0)) (Primrec.const [])
      (Primrec.list_cons.comp dig ((Primrec.list_getD []).comp .snd
        (Primrec.nat_div.comp len (Primrec.const 2)))))).to₂
  have hb := Primrec.nat_strong_rec (fun (_ : Unit) => born) h (by
    intro a n
    simp only [expand,List.length_map,List.length_range]
    by_cases hn : n=0
    · simp [hn]
    have hn' : 0<n := by omega
    have ht : n/2<n := Nat.div_lt_self hn' (by decide)
    rw [ite_eq_right hn,birth hn']
    simp [List.getD_eq_getElem?_getD, ht])
  exact hb.comp (Primrec.const ()) Primrec.id

private theorem primrec_row : Primrec encoded :=
  (primrec_born.comp Primrec.fst).pair ((primrec_born.comp (Primrec.fst.comp Primrec.snd)).pair
    (primrec_born.comp (Primrec.snd.comp Primrec.snd)))

private def edge (a : Row ℕ) := a.1+a.2.1+a.2.2+1

private theorem primrec_edge : Primrec edge :=
  Primrec.succ.comp (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp Primrec.snd))
    (Primrec.snd.comp Primrec.snd))

theorem primrec_colors : Primrec₂ colors := by
  let X := Row ℕ × Row ℕ
  have initial : Primrec (fun v : X => List.range (edge v.1)) := Primrec.list_range.comp (primrec_edge.comp .fst)
  have other : Primrec (fun v : X × ℕ => List.range (edge v.1.2)) :=
    Primrec.list_range.comp (primrec_edge.comp (Primrec.snd.comp .fst))
  have each : Primrec₂ (fun v : X => fun (k : ℕ) => (List.range (edge v.2)).map fun l => (k,l)) :=
    (Primrec.list_map other (((Primrec.snd.comp Primrec.fst).pair Primrec.snd).to₂)).to₂
  exact (Primrec.list_flatMap initial each).to₂

set_option maxHeartbeats 900000 in
theorem primrec_template : Primrec₂ template := by
  let f := fun v : (Row ℕ × Row ℕ) × Class ℕ => (born v.2.1,born v.2.2)
  have each : Primrec f := (primrec_born.comp (Primrec.fst.comp Primrec.snd)).pair
    (primrec_born.comp (Primrec.snd.comp Primrec.snd))
  exact (((primrec_row.comp Primrec.fst).pair (primrec_row.comp Primrec.snd)).pair
    (Primrec.list_map (primrec_colors.comp Primrec.fst Primrec.snd) each.to₂)).to₂

theorem primrec_widthRows : Primrec (fun p : Bool × ℕ × ℕ => widthRows p.1 p.2.1 p.2.2) := by
  have top : Primrec (fun p : Bool × ℕ × ℕ => p.2.1) := Primrec.fst.comp .snd
  have den : Primrec (fun p : Bool × ℕ × ℕ => p.2.2) := Primrec.snd.comp .snd
  simpa only [widthRows,Bool.cond_eq_ite] using (top.pair ((Primrec.const 0).pair (Primrec.cond Primrec.fst top (Primrec.const 0)))).pair
    (den.pair (Primrec.const (0,0)))

theorem primrec_gatherRows : Primrec (fun p : Bool × ℕ × ℕ => gatherRows p.1 p.2.1 p.2.2) := by
  have top : Primrec (fun p : Bool × ℕ × ℕ => p.2.1) := Primrec.fst.comp .snd
  have den : Primrec (fun p : Bool × ℕ × ℕ => p.2.2) := Primrec.snd.comp .snd
  simpa only [gatherRows,Bool.cond_eq_ite] using (den.pair ((Primrec.cond Primrec.fst (Primrec.const 0) top).pair (Primrec.const 0))).pair
    (den.pair ((Primrec.cond Primrec.fst top (Primrec.const 0)).pair (Primrec.const 0)))

private theorem emit_word : Effective ltr fun w : Word => Task.prepare 0 (send w) := by
  apply emit_list Computable.id
  apply (Computable.cond (Computable.id (α:=Bool)) (Computable.const (file ltr (Task.prepare 0 (send true))))
    (Computable.const (file ltr (Task.prepare 0 (send false))))).of_eq
  intro b
  cases b <;> rfl

private theorem emit_binary_row : Effective ltr fun r : Row Word => Task.prepare 0 (send r) :=
  emit_pair (emit_word.comp Computable.fst)
    (emit_pair (emit_word.comp (Computable.fst.comp Computable.snd)) (emit_word.comp (Computable.snd.comp Computable.snd)))

theorem effective_static : Effective ltr fun s : Static => Task.prepare 0 (send s) := by
  apply emit_pair
  · exact emit_pair (emit_binary_row.comp (Computable.fst.comp Computable.fst))
      (emit_binary_row.comp (Computable.snd.comp Computable.fst))
  · exact emit_list Computable.snd (emit_pair (emit_word.comp Computable.fst) (emit_word.comp Computable.snd))

theorem effective_literal {X : Type} [Primcodable X] {A B : X → Row ℕ} (ha : Computable A) (hb : Computable B) :
    Effective ltr fun x => Task.prepare 0 (send (template (A x) (B x))) :=
  effective_static.comp (primrec_template.to_comp.comp ha hb)

end InterchangeAffineMask

end NearSquareRoot
end Computability
end OAI
