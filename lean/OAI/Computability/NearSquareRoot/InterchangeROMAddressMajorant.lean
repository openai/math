import OAI.Computability.NearSquareRoot.InterchangeROMAddressPivot
import OAI.Computability.NearSquareRoot.KernelComputableAddress

/-! # Freezing mixed-word routing prices at template generation time -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace OpcodeProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Port InterchangeROMAddress
  InterchangeAffineMask KernelComputableAddress

/-- Both weighted sums used for a width or a gather have total coefficient
weight bounded by this numerical function of the opcode. -/
def coeffWeight (o : Opcode.Op) := 2*(Opcode.numerator o + Opcode.denominator o)+1

def ranksWeight (b n : ℕ) (o : Opcode.Op) :=
  2*b + 4*n + 2*((Opcode.target o).2+(Opcode.source o).2) + 12

def literalWeight (b n : ℕ) (o : Opcode.Op) :=
  2*ranksWeight b n o + 20*(coeffWeight o)^3 + 20

/-- Computable coefficient for a single opcode and any valid live geometry. -/
def perOp (M C K j b n : ℕ) (o : Opcode.Op) :=
  (M*((coeffWeight o)^2+1)*(C+1)+K+1)*(literalWeight b n o+2)^j

def geometry (j : ℕ) (h : Header) (N : ℕ) (source dest : Tree) :=
  source.count + dest.count + 1 + (N+1)*(size h+1)^j

def perWord (M C K j b n : ℕ) (ops : Opcode.Word) :=
  (ops.map (perOp M C K j b n)).sum

def affineRows (gather : Bool) (o : Opcode.Op) :=
  let coeff := bif gather then gatherRows else widthRows
  coeff (Opcode.negative o) (Opcode.numerator o) (Opcode.denominator o)

def affineLiteral (b n : ℕ) (gather : Bool) (o : Opcode.Op) : Affine.Template :=
  let s := InterchangeROMMirror.numericLocation b n
  let rows := affineRows gather o
  ((s (bif gather then Opcode.source o else Opcode.target o),s (Opcode.target o)),template rows.1 rows.2)

def pivotLiteral (b n : ℕ) (o : Opcode.Op) := numericSpec b n [((Opcode.target o).2,(Opcode.source o).2)]

private theorem rows_le (g : Bool) (o : Opcode.Op) :
    rowWeight (affineRows g o).1+rowWeight (affineRows g o).2+1 ≤ coeffWeight o := by
  cases g <;> cases q : Opcode.negative o <;> simp only [affineRows,widthRows,gatherRows,
    Bool.cond_true,Bool.cond_false,q,ite_true,ite_false,Bool.false_eq_true,rowWeight,coeffWeight] <;> omega

theorem classes_le (g : Bool) (o : Opcode.Op) :
    (colors (affineRows g o).1 (affineRows g o).2).length ≤ (coeffWeight o)^2 := by
  rw [colors_length,pow_two]
  have bound := rows_le g o
  exact Nat.mul_le_mul (by omega) (by omega)

private theorem location_size (b n : ℕ) (s : Bool × ℕ) :
    size (InterchangeROMMirror.numericLocation b n s) ≤ 2*b + 4*n + 2*s.2 + 12 := by
  simp only [InterchangeROMMirror.numericLocation,size_prod,size_bit,size_tally,tally_length]
  omega

theorem affineLiteral_le (b n : ℕ) (g : Bool) (o : Opcode.Op) :
    size (affineLiteral b n g o) ≤ literalWeight b n o := by
  have h := rows_le g o
  have q := (template_size (affineRows g o).1 (affineRows g o).2).trans
    (Nat.mul_le_mul_left 20 (Nat.pow_le_pow_left h 3))
  have a := location_size b n (Opcode.target o)
  have m := location_size b n (Opcode.source o)
  change size (InterchangeROMMirror.numericLocation b n (bif g then Opcode.source o else Opcode.target o)) +
    size (InterchangeROMMirror.numericLocation b n (Opcode.target o)) + 1 +
    size (template (affineRows g o).1 (affineRows g o).2) + 1 ≤ _
  unfold literalWeight ranksWeight
  cases g <;> simp only [Bool.cond_false,Bool.cond_true] at q ⊢ <;> omega

theorem pivotLiteral_le (b n : ℕ) (o : Opcode.Op) :
    size (pivotLiteral b n o) ≤ literalWeight b n o := by
  simp only [pivotLiteral,numericSpec,List.map_cons,List.map_nil,size_prod,size_tally,tally_length,
    size_cons,size_nil,literalWeight,ranksWeight]
  omega

private theorem pairPower {α β : Type} [Codec α] [Codec β] (x : α) (h : β) {s d j : ℕ}
    (hx : size x ≤ s) (hd : d ≤ j) : (size (x,h)+1)^d ≤ (s+2)^j*(size h+1)^j := by
  have split_ : size (x,h)+1 ≤ (s+2)*(size h+1) := by
    change size x + size h + 1 + 1 ≤ (s+2)*(size h+1)
    rw [Nat.mul_add,Nat.add_mul,Nat.mul_one]
    omega
  rw [← Nat.mul_pow]
  exact (Nat.pow_le_pow_right (by omega) hd).trans (Nat.pow_le_pow_left split_ _)

private theorem scan_factor {V N H F A D : ℕ} (hf : 1 ≤ F) (hD : D ≤ A*F*H) :
    V+N*D ≤ ((A+1)*F)*(V+N*H) := by
  have bound := Nat.mul_le_mul_left N hD
  have rearr : N*(A*F*H) = A*F*(N*H) := by ac_rfl
  rw [rearr] at bound
  have own : V ≤ F*V := Nat.le_mul_of_pos_left _ hf
  rw [Nat.add_mul,Nat.one_mul,Nat.add_mul,Nat.mul_add F]
  have expand : A*F*(V+N*H) = A*F*V + A*F*(N*H) := Nat.mul_add ..
  omega

theorem scan_le_perOp {M₀ C₀ d M C K j : ℕ} (hm : M₀ ≤ M) (hc : C₀ ≤ C) (hd : d ≤ j)
    (b n : ℕ) (g : Bool) (o : Opcode.Op) (h : Header) (N : ℕ) (source dest : Tree) :
    Affine.scanPrice M₀ C₀ d (colors (affineRows g o).1 (affineRows g o).2).length
      (affineLiteral b n g o) h N source dest ≤ perOp M C K j b n o * geometry j h N source dest := by
  let F := (literalWeight b n o+2)^j
  let H := (size h+1)^j
  have power := pairPower _ h (affineLiteral_le b n g o) hd
  have D : C₀*(size (affineLiteral b n g o,h)+1)^d ≤ C*F*H := by
    rw [Nat.mul_assoc]; exact Nat.mul_le_mul hc power
  have inner := scan_factor (V:=source.count+dest.count+1) (N:=N+1) (F:=F)
    (Nat.one_le_pow _ _ (by omega)) D
  have mm := Nat.mul_le_mul hm (Nat.succ_le_succ (classes_le g o))
  have all := Nat.mul_le_mul mm inner
  refine all.trans ?_
  change M*((coeffWeight o)^2+1)*((C+1)*F*geometry j h N source dest) ≤ _
  have re : M*((coeffWeight o)^2+1)*((C+1)*F*geometry j h N source dest) =
      M*((coeffWeight o)^2+1)*(C+1)*F*geometry j h N source dest := by ac_rfl
  rw [re]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right F (by omega))

theorem pivot_le_perOp {K₀ e M C K j : ℕ} (hk : K₀ ≤ K) (he : e ≤ j)
    (b n : ℕ) (o : Opcode.Op) (h : Header) (N : ℕ) (source dest : Tree) :
    pivotPrice K₀ e (pivotLiteral b n o) h source dest ≤ perOp M C K j b n o * geometry j h N source dest := by
  let F := (literalWeight b n o+2)^j
  let G := geometry j h N source dest
  have hH : (size h+1)^j ≤ G := by
    have q := Nat.le_mul_of_pos_left ((size h+1)^j) (show 0<N+1 by omega)
    dsimp only [G,geometry]; omega
  have pow := pairPower _ h (pivotLiteral_le b n o) he
  have D : K₀*(size (pivotLiteral b n o,h)+1)^e ≤ K*F*G := by
    rw [Nat.mul_assoc]
    exact Nat.mul_le_mul hk (pow.trans (Nat.mul_le_mul_left F hH))
  have own := Nat.le_mul_of_pos_left G (Nat.pow_pos (a:=literalWeight b n o+2) (n:=j) (by omega))
  have lower : source.count+dest.count ≤ G := by dsimp [G,geometry]; omega
  have cap : (K+1)*F*G ≤ perOp M C K j b n o*G := Nat.mul_le_mul_right _
    (Nat.mul_le_mul_right _ (by omega))
  rw [Nat.add_mul,Nat.one_mul,Nat.add_mul] at cap
  change K₀*(size (pivotLiteral b n o,h)+1)^e+source.count+dest.count ≤ perOp M C K j b n o*G
  change G ≤ F*G at own
  omega

/-- All input parameters, including the exponents and the opcode, may be
computed by the template generator. -/
theorem computable_perOp {X : Type} [Primcodable X] {M C K j b n : X → ℕ} {o : X → Opcode.Op}
    (hm : Computable M) (hc : Computable C) (hk : Computable K) (hj : Computable j)
    (hb : Computable b) (hn : Computable n) (ho : Computable o) :
    Computable fun x => perOp (M x) (C x) (K x) (j x) (b x) (n x) (o x) := by
  have tar := Computable.snd.comp (Computable.fst.comp (Computable.snd.comp ho))
  have src := Computable.snd.comp (Computable.fst.comp (Computable.snd.comp (Computable.snd.comp ho)))
  have coeff := Computable.snd.comp (Computable.snd.comp (Computable.snd.comp (Computable.snd.comp ho)))
  have top := Computable.fst.comp coeff
  have den := Computable.snd.comp coeff
  have pow : Computable₂ (fun x y : ℕ => x^y) := (primrec_pow Primrec.fst Primrec.snd).to_comp.to₂
  have add {f g : X → ℕ} (a : Computable f) (b : Computable g) : Computable (fun x => f x + g x) := Primrec.nat_add.to_comp.comp a b
  have mul {f g : X → ℕ} (a : Computable f) (b : Computable g) : Computable (fun x => f x * g x) := Primrec.nat_mul.to_comp.comp a b
  have q : Computable fun x => coeffWeight (o x) :=
    add (mul (.const 2) (add top den)) (.const 1)
  have r : Computable fun x => ranksWeight (b x) (n x) (o x) :=
    add (add (add (mul (.const 2) hb) (mul (.const 4) hn)) (mul (.const 2) (add tar src))) (.const 12)
  have lit : Computable fun x => literalWeight (b x) (n x) (o x) :=
    add (add (mul (.const 2) r) (mul (.const 20) (pow.comp q (.const 3)))) (.const 20)
  exact mul (add (add (mul (mul hm (add (pow.comp q (.const 2)) (.const 1))) (add hc (.const 1))) hk)
    (.const 1)) (pow.comp (add lit (.const 2)) hj)

theorem computable_perWord {X : Type} [Primcodable X] {M C K j b n : X → ℕ} {ops : X → Opcode.Word}
    (hm : Computable M) (hc : Computable C) (hk : Computable K) (hj : Computable j)
    (hb : Computable b) (hn : Computable n) (hw : Computable ops) :
    Computable fun x => perWord (M x) (C x) (K x) (j x) (b x) (n x) (ops x) := by
  let step (x : X) (p : Opcode.Op × ℕ) := perOp (M x) (C x) (K x) (j x) (b x) (n x) p.1 + p.2
  have hs : Computable₂ step := (Primrec.nat_add.to_comp.comp
    (computable_perOp (hm.comp .fst) (hc.comp .fst) (hk.comp .fst) (hj.comp .fst)
      (hb.comp .fst) (hn.comp .fst) (Computable.fst.comp .snd)) (Computable.snd.comp .snd)).to₂
  apply (GeneratorSyntax.computable_foldr hw (Computable.const 0) hs).of_eq
  intro x
  unfold perWord
  induction ops x with
  | nil => rfl
  | cons o tail ih => simp only [List.foldr_cons,List.map_cons,List.sum_cons,step,ih]

/-- Any bound on the live costs throughout the execution can be factored
out of the compiled word's local work, even when the payloads change. -/
theorem word_le {M C K j b n G : ℕ} (ops : Opcode.Word) (charge : Opcode.Op → ℕ)
    (h : ∀ o ∈ ops, charge o ≤ perOp M C K j b n o*G) :
    (ops.map charge).sum ≤ perWord M C K j b n ops * G := by
  induction ops with
  | nil => simp [perWord]
  | cons o os ih =>
    have hh := h o List.mem_cons_self
    have ht := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    simpa only [perWord,List.map_cons,List.sum_cons,Nat.add_mul] using Nat.add_le_add hh ht

theorem geometry_source (j : ℕ) (h : Header) (N : ℕ) (src dst : Tree) :
    src.count ≤ geometry j h N src dst := by unfold geometry; omega

theorem geometry_dest (j : ℕ) (h : Header) (N : ℕ) (src dst : Tree) :
    dst.count ≤ geometry j h N src dst := by unfold geometry; omega

theorem geometry_header {j : ℕ} (hj : 1 ≤ j) (h : Header) (N : ℕ) (src dst : Tree) :
    size h + 1 ≤ geometry j h N src dst := by
  have p := Nat.pow_le_pow_right (show 0<size h+1 by omega) hj
  rw [pow_one] at p
  have q := Nat.le_mul_of_pos_left ((size h+1)^j) (show 0<N+1 by omega)
  unfold geometry
  omega

theorem word_le_of_forall₂ {M C K j b n G : ℕ} {ops : Opcode.Word} {charges : List ℕ}
    (h : List.Forall₂ (fun o u => u ≤ perOp M C K j b n o*G) ops charges) :
    charges.sum ≤ perWord M C K j b n ops * G := by
  induction h with
  | nil => simp [perWord]
  | cons h _ ih =>
    simpa only [perWord,List.map_cons,List.sum_cons,Nat.add_mul] using Nat.add_le_add h ih

@[simp] theorem width_literal {b n : ℕ} (x : Spot (Fin n)) (a : Span b) :
    affineLiteral b n false (Opcode.encode (.width x a)) =
      Affine.spec (Equiv.refl _) b x x (widthRows a.neg a.top.count a.down.count).1
        (widthRows a.neg a.top.count a.down.count).2 := rfl

@[simp] theorem gather_literal {b n : ℕ} (x y : Spot (Fin n)) (a : Pinpoint b) :
    affineLiteral b n true (Opcode.encode (.gather x y a)) =
      Affine.spec (Equiv.refl _) b y x (pinRows a).1 (pinRows a).2 := by cases a <;> rfl

@[simp] theorem pivot_literal {b n : ℕ} (x y : Fin n) :
    pivotLiteral b n (Opcode.encode (b:=b) (.pivot x y)) = metadata b (Equiv.refl _) [(x,y)] := rfl

@[simp] theorem width_rows {b n : ℕ} (x : Spot (Fin n)) (a : Span b) :
    affineRows false (Opcode.encode (.width x a)) = widthRows a.neg a.top.count a.down.count := rfl

@[simp] theorem gather_rows {b n : ℕ} (x y : Spot (Fin n)) (a : Pinpoint b) :
    affineRows true (Opcode.encode (.gather x y a)) = pinRows a := by cases a <;> rfl

end OpcodeProgram

end NearSquareRoot
end Computability
end OAI
