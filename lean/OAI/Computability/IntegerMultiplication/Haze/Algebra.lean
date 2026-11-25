import OAI.Computability.IntegerMultiplication.Haze.Padding

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Haze
open Code Loom Strip Strip.Optic Strip.Dims Net Net.Walsh Net.Tensor Phase Packed Dusk IntegerMultiplication.Packed
open Finset Matrix
variable {P T : Tape} {A C F R : Type} [CommRing R]
variable {h g m n : ℕ}
noncomputable section
variable (s : Series A) [Fintype A] -- Finite, Pin lengths
-- define layer apply function product, using direct sums; conj with auth
private def cell (M : Mat Walsh.B R) : Mat (Chunk h g) R := Phase.grid Phase.pulse M -- requires DecidableEq Glow incl
-- operate over full Screen coordinates via grid_batch
abbrev screens := Screen h g (Fin n)
def rectangle (P V : Tape) (s : Series F) := order P V s

-- our full-layer support leaves outer keys unchanged; rewrite as operate by tensor on screens.
def walls (P V : Tape) (I : Type) : Lens (Base P V I) I (Pin P × Pin V) where
  toFun a := (a.2.1,a.1,a.2.2)
  invFun x := (x.2.1,x.1,x.2.2)
  left_inv _ := rfl
  right_inv _ := rfl
private theorem sameMat (M : Fin n → Mat Walsh.B R) :
    Strip.Optic.operate (target P T h g (Fin n)) (mat M) =
    Strip.Optic.operate (walls P T (screens (h:=h) (g:=g) (n:=n))) (mat (fun i : Fin n => cell (M i))) := by
  unfold cell
  rw [grid_batch,Phase.beneath]
  apply same_on
  · exact fun _=>rfl
  · intro x y e
    have et : (x.1,(fun i : Fin n => (pulse (x.2.1 i)).2), x.2.2) = (y.1,(fun i : Fin n => (pulse (y.2.1 i)).2), y.2.2) := e
    change ((fun i=> (pulse _).2),x.1,x.2.2)=((fun i=> (pulse _).2),y.1,y.2.2)
    have ⟨u,v,z⟩ := (show _ ∧ _ ∧ _ from ⟨(Prod.ext_iff.mp et).1,Prod.ext_iff.mp (Prod.ext_iff.mp et).2⟩)
    dsimp only at v z u; rw [u,v,z]
-- splice screens, turn the combined width to independent per half
omit [Fintype A] in
private theorem spireMat (M : Mat A R)
    (x y : (Fin m→A) × (Fin n→A)) :
    let a := Loom.spire s n m
    mat (fun _=>M) (a.cast x) (a.cast y) =
      mat (fun _=>M) x.1 y.1 * mat (fun _=>M) x.2 y.2 := by
  obtain ⟨x,v⟩ := x; obtain ⟨y,w⟩ := y
  simp only [Tensor.app]
  let a := Loom.spire s n m
  let f i := M (a.cast (x,v) i) (a.cast (y,w) i)
  let e : Fin m ⊕ Fin n ≃ Fin (m+n) := finSumFinEquiv
  change ∏ i,f i=_
  rw [← e.prod_comp f, Fintype.prod_sum_type]
  have p i : f (e (Sum.inl i))=M (x i) (y i) := by
    change M (a.cast (x,v) (Fin.castAdd n i)) (a.cast (y,w) (Fin.castAdd n i)) = _
    unfold a; rw [(spire_n s x v).1,(spire_n s y w).1]
  have q i : f (e (Sum.inr i))=M (v i) (w i) := by
    change M (a.cast (x,v) (Fin.natAdd m i)) (a.cast (y,w) (Fin.natAdd m i)) = _
    unfold a; rw [(spire_n s x v).2,(spire_n s y w).2]
  simp only [p,q]
abbrev screen h g n := Screen h g (Fin n)
abbrev levels h g n := Track (chunks h g) n
def hatch (p t : Tape) (h g m n : ℕ) :
    Adopt (Loom.Board p ((levels h g m).cart (levels h g n)) t) (plain p t h g (m+n)) :=
  (Adopt.same _).split ((Loom.spire (chunks h g) n m).split (Adopt.same _))
abbrev focusA (h g m n : ℕ) := screen h g m × screen h g n
abbrev hall p t h g m n := Base p t (focusA h g m n)
abbrev look h g n (M : Mat Walsh.B R) := mat (fun _ : Fin n=> cell (h:=h) (g:=g) M)

-- split desired addresses against unmodified tail
def liftA (M : Mat Walsh.B R)
    (x : hall P T h g m n→R) : hall P T h g m n→R :=
  fun i=> ((look h g m M) *ᵥ fun a:screen h g m=> x (i.1,(a,i.2.1.2),i.2.2)) i.2.1.1
def liftB (M : Mat Walsh.B R)
    (x : hall P T h g m n→R) : hall P T h g m n→R :=
  fun i=> ((look h g n M) *ᵥ fun a:screen h g n=> x (i.1,(i.2.1.1,a),i.2.2)) i.2.1.2

def spectrum h g k (x : Matrix Walsh.B Walsh.B R) (P T : Tape) :=
  Strip.Optic.operate (target P T h g (Fin k)) (mat (fun (_:Fin k)=> x))
-- dense separated tensor (over full chunks!), cycle C occupancy
theorem mosaic (M : Mat Walsh.B R)
    (x : Base P T (screen h g (m+n))→R) (i) :
    let q := hatch P T h g m n
    spectrum h g (m+n) M P T x (q.cast i) =
      liftB M (liftA M (x ∘ q.cast)) i := by
  unfold spectrum
  rw [sameMat]
  dsimp only
  let t := Loom.spire (chunks h g) n m
  let a := hatch P T h g m n
  let u := look h g m M
  let v := look h g n M
  let f z := look h g (m+n) M (t.cast i.2.1) z * x (i.1,z,i.2.2)
  change ∑ w,f w = ∑ j, v i.2.1.2 j * (∑ k, u i.2.1.1 k * x (a.cast (i.1,(k,j),i.2.2)))
  rw [← t.cast.sum_comp f,Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  change (look h g (m+n) M) (t.cast i.2.1) (t.cast (k,j)) * x (a.cast (i.1,(k,j),i.2.2)) = _
  rw [show (look h g (m+n) M) (t.cast i.2.1) (t.cast (k,j)) = u i.2.1.1 k * v i.2.1.2 j from spireMat ..]
  ring

-- first call, tails folded into Spectator
abbrev dust (h g n : ℕ) := Adic.field 2 (n*width h g)
def haul (h g n : ℕ) : Seal (levels h g n) (dust h g n) :=
  Packed.wound 2 (width h g) (chunks h g) (chord h g) n -- args?
def enrol (P T : Tape) (h g m n : ℕ) :
    Adopt (Loom.Board P ((levels h g m).cart (levels h g n)) T)
      (plain P (dust h g n++T) h g m) :=
  let x := levels h g m
  (Adopt.same _).split ((Adopt.rotate x (levels h g n) (layout T)).thenDo
    ((Adopt.same x).split (((haul h g n).split (Adopt.same _)).thenDo (Loom.unite _ _))))
def send2 (P T : Tape) (h g m n : ℕ) :
    Adopt (Loom.Board P ((levels h g m).cart (levels h g n)) T)
      (plain (P++dust h g m) T h g n) :=
  let _u := levels h g m
  let a := (levels h g n).cart (layout T)
  (((Adopt.same _).split (Adopt.rotate _ _ _)).thenDo (Adopt.rotate _ _ a).back).thenDo
    ((((Adopt.same _).split (haul h g m)).thenDo (Loom.unite _ _)).split (Adopt.same a))

theorem framed_l (x : hall P T h g m n → R) (M : Mat Walsh.B R) (i) :
    let a := enrol P T h g m n
    (spectrum h g m M P _ (x ∘ a.cast.symm)) (a.cast i) = liftA M x i := by
  dsimp only
  unfold spectrum
  rw [sameMat]
  let a := enrol P T h g m n
  change ((look h g m M) *ᵥ
    fun j=> x (a.cast.symm (a.cast (i.1,(j,i.2.1.2),i.2.2)))) i.2.1.1=_
  simp only [Equiv.symm_apply_apply,liftA]
theorem framed_r (x : hall P T h g m n → R) (M : Mat Walsh.B R) (i) :
    let a := send2 P T h g m n
    (spectrum h g n M _ T (x ∘ a.cast.symm)) (a.cast i) = liftB M x i := by
  dsimp only
  unfold spectrum
  rw [sameMat]
  let a := send2 P T h g m n
  change ((look h g n M) *ᵥ
    fun j=> x (a.cast.symm (a.cast (i.1,(i.2.1.1,j),i.2.2)))) i.2.1.2=_
  simp only [Equiv.symm_apply_apply,liftB]
theorem nil_r (x : Base P T (screen h g 0) → R) (M : Mat Walsh.B R) :
    spectrum h g 0 M P T x=x := by
  unfold spectrum; rw [sameMat]
  have e : (fun i:Fin 0=> cell (h:=h) (g:=g) M) = fun _=>1 := funext fun i=>i.elim0
  rw [e,Tensor.unit,Optic.one,id_eq]
end
end Haze

end IntegerMultiplication
end Computability
end OAI
