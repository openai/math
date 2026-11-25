import OAI.Computability.IntegerMultiplication.Thin.Rank
import OAI.Computability.NearSquareRoot.InterchangeBQuestLocal
import OAI.Computability.NearSquareRoot.BoundedBranch

/-! # A fixed three-ruler carve and its header-free flattening machine

Both scans treat each record as an arbitrary tree. The input and output
represent the same sequence of records with different list boundaries.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBankCarve

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Thin Space InterchangeSpace

structure Grid where
  p : ℕ
  d : ℕ
  t : ℕ
  hp : 1 ≤ p
  hd : 1 ≤ d
  ht : 1 ≤ t
  v : (Fin p × Fin d) × Fin t → Tree

namespace Grid

def pre (x : Grid) := Series.natural x.p
def mid (x : Grid) := Series.natural x.d
def tail_ (x : Grid) := Series.natural x.t
def wide_ (x : Grid) := x.pre.cart x.mid
def flat (x : Grid) := stripe (x.wide_.cart x.tail_) x.v
def nested (x : Grid) := stripe x.pre fun i => stripe x.mid fun j => stripe x.tail_ fun k => x.v ((i,j),k)
def header (x : Grid) := (tally x.p,tally x.d,tally x.t)
def query (x : Grid) := (send x.header).fork x.flat

private theorem cells (x : Grid) : x.p*x.d*x.t ≤ x.flat.count := by
  rw [flat,stripe_simple,Task.forest_count]
  change _ ≤ (x.wide_.cart x.tail_).count+_+1
  simp only [wide_,pre,mid,tail_,Series.count_cart,Series.count_natural]
  omega

end Grid

private theorem rectangle (a b w : ℕ) (ha : 1≤a) (hb : 1≤b) (hv : a*b≤w) :
    ((a:ℝ)+1)*((b:ℝ)+1) ≤ 4*(w:ℝ) := by
  exact_mod_cast (show (a+1)*(b+1) ≤ 4*w from calc
    _ ≤ (2*a)*(2*b) := Nat.mul_le_mul (by omega) (by omega)
    _ = 4*(a*b) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ hv)

theorem carve_task : BoundedTask (fun x : Grid => x.query.count+1) (fun x => x.query.count+1)
    Grid.query Grid.nested := by
  let w (x : Grid) : ℝ := ((x.query.count+1 : ℕ) : ℝ)
  have pos : ∀ i, 1 ≤ w i := by intro i; dsimp only [w]; exact_mod_cast Nat.le_add_left 1 _
  have vol : Volume w Grid.query := ⟨1,fun i => by simp [w]⟩
  have head := Carries.dropRight (p:=fun i : Grid => send i.header) (r:=Grid.flat) pos
    (Volume.left vol) (Volume.right vol)
  have raw := Carries.dropLeft (p:=fun i : Grid => send i.header) (r:=Grid.flat) pos
    (Volume.left vol) (Volume.right vol)
  have fst := head.chain (Carries.func pos head.out (Prod.fst : Tally × Tally × Tally → _) Easy.fst)
  have sec := head.chain (Carries.func pos head.out (fun z : Tally × Tally × Tally => z.2.1) (by fun_prop))
  have third := head.chain (Carries.func pos head.out (fun z : Tally × Tally × Tally => z.2.2) (by fun_prop))
  have query : (fun x : Grid => (send x.header).fork x.flat) = Grid.query := rfl
  rw [query] at fst sec third
  have rims : Rim w Grid.query Grid.pre := ⟨by simpa only [Roll,Grid.pre,Series.count_natural,Grid.header] using fst, by
    intro i; simpa only [Grid.pre,Series.count_natural] using i.hp⟩
  have rimd : Rim w Grid.query Grid.mid := ⟨by simpa only [Roll,Grid.mid,Series.count_natural,Grid.header] using sec, by
    intro i; simpa only [Grid.mid,Series.count_natural] using i.hd⟩
  have rimt : Roll w Grid.query Grid.tail_ := by simpa only [Roll,Grid.tail_,Series.count_natural,Grid.header] using third
  have pd (x : Grid) : x.p*x.d ≤ x.query.count+1 := by
    have num := Nat.le_mul_of_pos_right (x.p*x.d) x.ht
    have all := x.cells
    dsimp only [Grid.query,Tree.count]
    omega
  have area (x : Grid) : x.p*x.d*x.t ≤ x.query.count+1 := by
    have all := x.cells
    dsimp only [Grid.query,Tree.count]
    omega
  have wide := Rim.mulR Grid.pre Grid.mid rims rimd ⟨1,fun x => by
    rw [Grid.pre,Grid.mid,Series.count_natural,Series.count_natural]
    simp only [Nat.cast_one,one_mul,w]
    exact_mod_cast pd x⟩
  let inner (x : Grid) (z : Fin x.p × Fin x.d) := stripe x.tail_ fun k => x.v (z,k)
  have outer := Strip.carve Grid.wide_ Grid.tail_ Grid.v raw (wide.pay.twice rimt) ⟨4,fun x => by
    simp only [Grid.wide_,Series.count_cart,Grid.pre,Grid.mid,Grid.tail_,Series.count_natural,Nat.cast_mul]
    simpa only [Nat.cast_mul,Nat.cast_ofNat,w] using rectangle (x.p*x.d) x.t (x.query.count+1)
      (Nat.mul_pos x.hp x.hd) x.ht (area x)⟩
  have last := Strip.carve Grid.pre Grid.mid inner outer (rims.pay.twice rimd.pay) ⟨4,fun x => by
    simp only [Grid.pre,Grid.mid,Series.count_natural]
    exact rectangle x.p x.d (x.query.count+1) x.hp x.hd (pd x)⟩
  exact (carries_bounded last).conform (fun x => Nat.ceil_natCast _) (fun x => Nat.ceil_natCast _)
    (fun _ => rfl) (fun _ => rfl)

theorem flatten_task : BoundedTask (fun x : Grid => x.nested.count+1) (fun x => x.nested.count+1)
    Grid.nested Grid.flat := by
  let w (x : Grid) : ℝ := ((x.nested.count+1 : ℕ) : ℝ)
  have pos : ∀ i, 1 ≤ w i := by intro i; dsimp only [w]; exact_mod_cast Nat.le_add_left 1 _
  have vol : Volume w Grid.nested := ⟨1,fun i => by simp [w]⟩
  have inner := Strip.flatten Grid.pre Grid.mid
    (fun x z => stripe x.tail_ fun k => x.v (z,k)) (Carries.idles pos vol)
  have flat := Strip.flatten Grid.wide_ Grid.tail_ Grid.v inner
  exact (carries_bounded flat).conform (fun x => Nat.ceil_natCast _) (fun x => Nat.ceil_natCast _)
    (fun _ => rfl) (fun _ => rfl)

noncomputable def carveCommand : Cmd := carve_task.choose
noncomputable def flattenCommand : Cmd := flatten_task.choose

private noncomputable def rank {A : Type} (s : Series A) : Adopt (Series.natural s.count) s where
  cast := s.index.symm
  route {O} f := by
    apply List.ext_getElem (by simp)
    intro i hi hj
    have h : i<s.count := by simpa using hi
    rw [s.get f ⟨i,h⟩ hi, (Series.natural s.count).get _ ⟨i,by simpa using h⟩ hj]
    simp only [Series.index_symm,Function.comp_apply]
    rw [Series.get_natural _ (⟨i,h⟩ : Fin s.count)]

private def model {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (hp : 0 < p.count) (hd : 0 < d.count) (ht : 0 < t.count) (v : (A × D) × T → Tree) : Grid :=
  ⟨p.count,d.count,t.count,hp,hd,ht,fun z => v ((p.follow z.1.1,d.follow z.1.2),t.follow z.2)⟩

private theorem model_flat {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (hp hd ht) (v : (A × D) × T → Tree) :
    (model p d t hp hd ht v).flat = stripe ((p.cart d).cart t) v :=
  (((rank p).split (rank d)).split (rank t)).packet v |>.symm

private theorem model_nested {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (hp hd ht) (v : (A × D) × T → Tree) :
    (model p d t hp hd ht v).nested = stripe p (fun i => stripe d fun j => stripe t fun k => v ((i,j),k)) := by
  simp only [Grid.nested,Grid.pre,Grid.mid,Grid.tail_,model]
  rw [(rank p).packet]
  apply congrArg (stripe (Series.natural p.count))
  funext i
  dsimp only [Function.comp_apply]
  rw [(rank d).packet]
  apply congrArg (stripe (Series.natural d.count))
  funext j
  dsimp only [Function.comp_apply]
  exact ((rank t).packet (fun k => v ((p.follow i,d.follow j),k))).symm

/-- Uniform physical carve with arbitrary native series and arbitrary trees. -/
theorem carve_bounded : ∃ C : ℕ, ∀ {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (_ : 0 < p.count) (_ : 0 < d.count) (_ : 0 < t.count) (v : (A × D) × T → Tree) env deck base,
    DeckCap base deck →
    let input := Tree.fork (send (tally p.count,tally d.count,tally t.count)) (stripe ((p.cart d).cart t) v)
    let w := C*(input.count+2)
    BoundedFits env carveCommand (pile 0 input deck)
      (pile 0 (stripe p fun i => stripe d fun j => stripe t fun k => v ((i,j),k)) deck) w (base+w) w := by
  obtain ⟨C,run⟩ := carve_task.choose_spec
  refine ⟨C,?_⟩
  intro A D T p d t hp hd ht v env deck base htape
  have h := run (model p d t hp hd ht v) env deck base htape
  simp only [Grid.query,model_flat,model_nested] at h
  change BoundedFits env carveCommand _ _ _ _ _
  exact h

theorem flatten_bounded : ∃ C : ℕ, ∀ {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (_ : 0 < p.count) (_ : 0 < d.count) (_ : 0 < t.count) (v : (A × D) × T → Tree) env deck base,
    DeckCap base deck →
    let input := stripe p fun i => stripe d fun j => stripe t fun k => v ((i,j),k)
    let w := C*(input.count+2)
    BoundedFits env flattenCommand (pile 0 input deck) (pile 0 (stripe ((p.cart d).cart t) v) deck)
      w (base+w) w := by
  obtain ⟨C,run⟩ := flatten_task.choose_spec
  refine ⟨C,?_⟩
  intro A D T p d t hp hd ht v env deck base htape
  have h := run (model p d t hp hd ht v) env deck base htape
  simpa only [model_flat,model_nested,flattenCommand,Nat.add_assoc] using h

private theorem list_boundaries {X : Type} [Codec X] (l : List (List X)) :
    size l = size l.flatten+2*l.length := by
  induction l with
  | nil => simp
  | cons x l ih =>
    have cat := costSum_le_length_size (x++l.flatten)
    rw [List.length_append,costSum_cat] at cat
    have a := costSum_le_length_size x
    have b := costSum_le_length_size l.flatten
    simp only [size_cons,List.flatten_cons,List.length_cons]
    omega

private theorem two_boundaries {A D : Type} (p : Series A) (d : Series D) (v : A × D → Tree) :
    (stripe p fun i => stripe d fun j => v (i,j)).count =
      (stripe (p.cart d) v).count+2*p.count := by
  let l := p.tab fun i => d.tab fun j => v (i,j)
  have e : (stripe p fun i => stripe d fun j => v (i,j)) = send l := by
    simp_rw [stripe_eq]
    simp only [l,Series.tab,← Task.forest_send,Task.forest_map]
    rfl
  rw [e,cart_eq]
  change size l = size l.flatten+2*p.count
  simpa only [l,Series.card] using list_boundaries l

/-- Every new subgroup contributes one cons node and one list terminator. -/
theorem nested_count {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (v : (A × D) × T → Tree) :
    (stripe p fun i => stripe d fun j => stripe t fun k => v ((i,j),k)).count =
      (stripe ((p.cart d).cart t) v).count+2*(p.count*d.count)+2*p.count := by
  rw [two_boundaries p d (fun z => stripe t fun k => v (z,k)),two_boundaries (p.cart d) t v,
    Series.count_cart]

theorem flat_le_nested {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (v : (A × D) × T → Tree) :
    (stripe ((p.cart d).cart t) v).count ≤
      (stripe p fun i => stripe d fun j => stripe t fun k => v ((i,j),k)).count := by
  rw [nested_count]
  omega

private theorem record_count {A : Type} (s : Series A) (v : A → Tree) : s.count ≤ (stripe s v).count := by
  rw [stripe_simple,Task.forest_count]
  change s.count ≤ s.count+_+1
  omega

theorem nested_le_flat {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (hd : 0 < d.count) (ht : 0 < t.count) (v : (A × D) × T → Tree) :
    (stripe p fun i => stripe d fun j => stripe t fun k => v ((i,j),k)).count ≤
      5*(stripe ((p.cart d).cart t) v).count := by
  rw [nested_count]
  have volume := record_count ((p.cart d).cart t) v
  simp only [Series.count_cart] at volume
  have mid := Nat.le_mul_of_pos_right p.count hd
  have last := Nat.le_mul_of_pos_right (p.count*d.count) ht
  omega

theorem rulers_le_flat {A D T : Type} (p : Series A) (d : Series D) (t : Series T)
    (hp : 0 < p.count) (hd : 0 < d.count) (ht : 0 < t.count) (v : (A × D) × T → Tree) :
    (send (tally p.count,tally d.count,tally t.count)).count ≤
      6*((stripe ((p.cart d).cart t) v).count+1) := by
  change size _ ≤ _
  simp only [size_prod,size_tally,tally_length]
  have volume := record_count ((p.cart d).cart t) v
  simp only [Series.count_cart] at volume
  have pp := Nat.le_mul_of_pos_right p.count hd
  have pd := Nat.le_mul_of_pos_left d.count hp
  have pt := Nat.le_mul_of_pos_left t.count (Nat.mul_pos hp hd)
  have last := Nat.le_mul_of_pos_right (p.count*d.count) ht
  omega

end InterchangeROMBankCarve

end NearSquareRoot
end Computability
end OAI
