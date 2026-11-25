import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reads
import OAI.LinearAlgebra.MatrixExponent.Assembly.Group.ChildPaths
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Assembly.AppendAddress
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Guard
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Length

/-!
# A short dictionary input at a child occurrence

An interval code and group index specify the occurrence within the
parent. Equality tests on the surrounding addresses are encoded in
the common mask. No global host name enters the dictionary.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Window.Tile
open Coloring

abbrev radius (d : ℕ) := (d + 1) * 8
abbrev mask (d n k : ℕ) := Format.vec (radius d + (n + 1)) (.vec k (.vec (radius d + (n + 1)) .bit))
abbrev word (d a n k : ℕ) (A : Format) :=
  Format.pair .bit (.pair .bit (.pair (.addr a)
    (.pair (.addr (n + 1)) (.pair (mask d n k) (.vec (radius d) A)))))

abbrev incoming (m d a n k : ℕ) (A : Format) :=
  Format.pair (.vec (m + (n + 1)) .bit) (.pair .bit
    (.pair (.vec m (mask d n k)) (Fmt.groups m d a (.vec (radius d) A))))

variable {m d a n k : ℕ} {A : Format}

def tile (x : (incoming m d a n k A).obj) (v : B (m + (n + 1))) (b : B a) : (word d a n k A).obj :=
  let p := Match.rowIndex m (n + 1) v
  (x.1 v, x.2.1, b, p.2, x.2.2.1 p.1, (x.2.2.2 p.1).2 b)

def bank (live : B (m + (n + 1)) → Bool) (col : Bool) (nav : (Neighborhood.Rows (m + (n + 1)) k).obj)
    (x : (Fmt.groups m d a A).obj) : (incoming m d a n k A).obj :=
  (live, col, Child.mask (Neighborhood.walks 8 (fun v => (x v).1)) nav, reads 8 x)

theorem width : (word d a n k A).width = 2 + a + (n + 1) +
    2 ^ (radius d + (n + 1)) * (2 ^ k * 2 ^ (radius d + (n + 1))) + 2 ^ (radius d) * A.width := by
  simp only [word, mask, Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit, Format.width_addr (n + 1)]
  ring

def atHost (p : B m × B a) (label : B (n + 1)) : B (m + (n + 1)) :=
  (Match.rowIndex m (n + 1)).symm (p.1, label)

theorem tile_at (x : (incoming m d a n k A).obj) (p : B m × B a) (label : B (n + 1)) :
    tile x (atHost p label) p.2 =
      (x.1 (atHost p label), x.2.1, p.2, label, x.2.2.1 p.1, (x.2.2.2 p.1).2 p.2) := by
  simp only [tile, atHost, Equiv.apply_symm_apply]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Window.Tile
end

/-! # One shared dictionary gate per child and group -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Window.Tile
open Coloring
open scoped Classical

variable {F : Type} [Field F] {u m d a n k : ℕ} {A H : Format} {L : Set (Table F)}

theorem project_const {f : A.obj → H.obj}
    (hf : ∀ i, (∃ j, ∀ x, H.code (f x) i = A.code x j) ∨ ∃ b, ∀ x, H.code (f x) i = b) :
    Circuit F A H f (A.width + 34 * H.width) := by
  have h : Install.Depends (H.code ∘ f ∘ A.code.symm) 1 := by
    intro i
    rcases hf i with ⟨j, hj⟩ | ⟨b, hb⟩
    · refine ⟨{j}, by simp, fun x y e => ?_⟩
      simpa only [Function.comp_apply, hj, Equiv.apply_symm_apply] using e j (by simp)
    · exact ⟨∅, by simp, fun x y _ => (hb _).trans (hb _).symm⟩
  exact h.bnet F

abbrev output (m a n : ℕ) (H : Format) := Format.vec (m + (n + 1)) (.vec a H)

private theorem prepare :
    Circuit F (incoming m d a n k A) (output m a n (word d a n k A)) tile
      ((incoming m d a n k A).width + 34 * (output m a n (word d a n k A)).width) := by
  apply project_const
  rintro ⟨v, b, i | i | i | i | i | i⟩
  · exact .inl ⟨.inl (v, i), fun _ => rfl⟩
  · exact .inl ⟨.inr (.inl i), fun _ => rfl⟩
  · exact .inr ⟨(Format.addr a).code b i, fun _ => rfl⟩
  · exact .inr ⟨(Format.addr (n + 1)).code (Match.rowIndex m (n + 1) v).2 i, fun _ => rfl⟩
  · exact .inl ⟨.inr (.inr (.inl ((Match.rowIndex m (n + 1) v).1, i))), fun _ => rfl⟩
  · exact .inl ⟨.inr (.inr (.inr ((Match.rowIndex m (n + 1) v).1, .inr (b, i)))), fun _ => rfl⟩

def cost (m d a n k : ℕ) (A H : Format) :=
  4 * (incoming m d a n k A).width +
    2 ^ (m + (n + 1)) * 2 ^ a * (1 + 137 * (word d a n k A).width + H.width)

def gate (F : Type) [Field F] (g : (word d a n k A).obj → H.obj) :=
  lookup F (word d a n k A) H (fun x y => if g x = y then 1 else 0)

theorem computes (hu : 3 ≤ u) (g : (word d a n k A).obj → H.obj)
    (fit : (word d a n k A).width + H.width ≤ u) (allowed : gate F g ∈ L) :
    Map F u L (incoming m d a n k A) (output m a n H)
      (fun x v b => g (tile x v b)) (cost m d a n k A H) := by
  have one : Map F u L (word d a n k A) H g (1 + (word d a n k A).width + H.width) :=
    Kernel.lookup fit allowed
  have run := Map.vec _ (fun _ : B (m + (n + 1)) => Map.vec _ (fun _ : B a => one))
  refine ((Map.circuit hu prepare).comp run).mono ?_
  simp only [cost, output, Format.width_vec]
  exact le_of_eq (by ring)

end OAI.LinearAlgebra.MatrixExponent.Assembly.Window.Tile
end

/-!
# Printing child records from their parent bank

The walk table and the mask of address coincidences are computed once
per host. Eight grouped reads share the long addresses across all groups.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Window.Tile

open Coloring

abbrev raw (m d a n k : ℕ) (A : Format) :=
  Format.pair (.vec (m + (n + 1)) .bit) (.pair .bit
    (.pair (Neighborhood.Rows (m + (n + 1)) k) (Fmt.groups m d a A)))

def bankCost (m d a n k : ℕ) (A : Format) (v N t : ℕ) :=
  24 * (raw m d a n k A).width +
    4 * (2 ^ m * (100 + (m + 2 ^ radius d)) ^ 20 + 2 ^ (m + (n + 1)) * (100 + t) ^ 40) + 9 * readCost m d v N

variable {F : Type} [Field F] {u m d a n k v N t : ℕ} {L : Set (Table F)} {A H : Format}

def fill (x : (raw m d a n k A).obj) : (incoming m d a n k A).obj :=
  bank x.1 x.2.1 x.2.2.1 x.2.2.2

variable {I : Type*} (hu : 3 ≤ u) (ht : Access F u L (m + d) v N)
    (cap : 2 ^ a * (Walks 8 d A).width ≤ v)
    (hm : m + (n + 1) ≤ t) (hq : 2 ^ (radius d + (n + 1)) ≤ t) (hk : 2 ^ k ≤ t)
    (X : I → (raw m d a n k A).obj)
    (recip : ∀ i, Fmt.Reciprocal (.vec a A) (X i).2.2.2)

include hu ht cap hm hq hk recip

theorem bank_net :
    Computes F u L (raw m d a n k A) (incoming m d a n k A) X (fill ∘ X) (fun _ => 1)
      (bankCost m d a n k A v N t) := by
  let R := raw m d a n k A
  let T := Format.vec (m + (n + 1)) .bit
  let W := Neighborhood.Rows m d
  let C := Neighborhood.Rows (m + (n + 1)) k
  let G := Fmt.groups m d a A
  let M := Format.pair T (.pair .bit (.pair (.pair W C) G))
  let nav (x : R.obj) : W.obj := fun i => (x.2.2.2 i).1
  let prepare (x : R.obj) : M.obj := (x.1, x.2.1, (nav x, x.2.2.1), x.2.2.2)
  have pre : Circuit F R M prepare (R.width + 2 * M.width) := by
    let idx : M.pins → R.pins
      | .inl i => .inl i
      | .inr (.inl i) => .inr (.inl i)
      | .inr (.inr (.inl (.inl (i, j)))) => .inr (.inr (.inr (i, .inl j)))
      | .inr (.inr (.inl (.inr i))) => .inr (.inr (.inl i))
      | .inr (.inr (.inr i)) => .inr (.inr (.inr i))
    exact Circuit.project idx (by rintro x (i | i | (⟨i, j⟩ | i) | i) <;> rfl)
  obtain ⟨s, hs, h₁⟩ := Neighborhood.cheap_walks F m d 8 (by decide)
  obtain ⟨p, hp, h₂⟩ := Child.cheap_mask F hm hq hk
  have run := (hs.par (Circuit.id F C)).comp hp
  have moves := reads_net hu ht (fun i => (X i).2.2.2) recip cap
  have mask := Computes.of_map (x := fun i => (nav (X i), (X i).2.2.1))
    (Map.circuit (L := L) hu run) (fun _ => rfl)
  have live := Computes.of_map (x := fun i => (X i).1)
    (Map.circuit (L := L) hu (Circuit.id F T)) (fun _ => rfl)
  have col := Computes.of_map (x := fun i => (X i).2.1)
    (Map.circuit (L := L) hu (Circuit.id F .bit)) (fun _ => rfl)
  have post := live.par (col.par (mask.par moves))
  have done := (Computes.of_map (x := X) (Map.circuit hu pre) (fun _ => rfl)).comp post
  simp only [one_mul] at done
  refine done.mono ?_
  have hr : R.width = T.width + Format.bit.width + C.width + G.width := by
    simp only [R, raw, T, C, G, Format.width_pair]
    omega
  have hd : M.width = R.width + W.width := by
    simp only [M, Format.width_pair, hr]
    omega
  have hv : W.width ≤ G.width := by
    unfold W G Neighborhood.Rows Fmt.groups Fmt.bank
    simp only [Format.width_vec, Format.width_pair]
    exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
  change _ ≤ 24 * R.width + 4 * (2 ^ m * (100 + (m + 2 ^ ((d + 1) * 8))) ^ 20 +
    2 ^ (m + (n + 1)) * (100 + t) ^ 40) + 9 * readCost m d v N
  omega

theorem print_net (g : (word d a n k A).obj → H.obj)
    (fit : (word d a n k A).width + H.width ≤ u) (ok : gate F g ∈ L) :
    Computes F u L (raw m d a n k A) (output m a n H) X
      (fun i w j => g (tile (fill (X i)) w j)) (fun _ => 1)
      (bankCost m d a n k A v N t + cost m d a n k A H) := by
  have b := bank_net hu ht cap hm hq hk X recip
  have p := Computes.of_map (x := fill ∘ X) (y := fun i w j => g (tile (fill (X i)) w j))
    (computes hu g fit ok) (fun _ => rfl)
  simpa only [mul_one] using b.comp p

end OAI.LinearAlgebra.MatrixExponent.Assembly.Window.Tile
end

/-! # Comparing local windows from gathered records and child masks -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Window

open Coloring

variable {V W X : Type} {A : Format} {d h e ℓ a m m' k t r : ℕ}

/-- The group coordinate stays fixed along each walk. The record
decoders are common to all host names and both environments. -/
structure View (α : Env V X d h e ℓ) (loc : V ↪ B m × B a) (T : (Fmt.groups m d a A).obj)
    (D : A.obj → (Match.Input d h e e ℓ).obj) (R : A.obj → B h → B e → Option (B d))
    (Z : A.obj → X) : Prop where
  nav : ∀ v j, loc (α.nav v j) = ((T (loc v).1).1 j, (loc v).2)
  data : ∀ v, α.data v = D ((T (loc v).1).2 (loc v).2)
  recv : ∀ v, α.recv v = R ((T (loc v).1).2 (loc v).2)
  extra : ∀ v, α.extra v = Z ((T (loc v).1).2 (loc v).2)

variable {α : Env V X d h e ℓ} {β : Env W X d h e ℓ} {loc : V ↪ B m × B a} {loc' : W ↪ B m' × B a}
  {T : (Fmt.groups m d a A).obj} {T' : (Fmt.groups m' d a A).obj}
  {D : A.obj → (Match.Input d h e e ℓ).obj} {R : A.obj → B h → B e → Option (B d)} {Z : A.obj → X}
  (H : View α loc T D R Z) (H' : View β loc' T' D R Z)

include H in
theorem View.node (p : List (B d)) :
    loc (α.node p) = (visit (fun v => (T v).1) (loc α.root).1 p, (loc α.root).2) := by
  induction p with
  | nil => rfl
  | cons j p ih => rw [show α.node (j :: p) = α.nav (α.node p) j from rfl, H.nav, ih]; rfl

variable {b : (Neighborhood.Rows (m + t) k).obj} {b' : (Neighborhood.Rows (m' + t) k).obj}
  (hmask : Child.mask (Neighborhood.walks r (fun v => (T v).1)) b (loc α.root).1 =
    Child.mask (Neighborhood.walks r (fun v => (T' v).1)) b' (loc' β.root).1)

include H H' hmask

theorem View.index_agree {v v' : V} {w w' : W} (hv : Related α β r v w)
    (hv' : Related α β r v' w') (i j : B t) :
    Child.index b ((Match.rowIndex m t).symm ((loc v).1, i)) ((Match.rowIndex m t).symm ((loc v').1, j)) =
      Child.index b' ((Match.rowIndex m' t).symm ((loc' w).1, i))
        ((Match.rowIndex m' t).symm ((loc' w').1, j)) := by
  obtain ⟨p, hp, rfl, rfl⟩ := hv
  obtain ⟨q, hq, rfl, rfl⟩ := hv'
  simp only [H.node, H'.node]
  exact Child.index_agree hmask hp hq i j

theorem View.agree (hself : ∀ i, b i 0 = i) (hself' : ∀ i, b' i 0 = i)
    (hr : (reads r T (loc α.root).1).2 (loc α.root).2 =
      (reads r T' (loc' β.root).1).2 (loc' β.root).2) : Agree α β r := by
  have recs (p : List (B d)) (hp : p.length ≤ r) :
      (T (loc (α.node p)).1).2 (loc (α.node p)).2 =
      (T' (loc' (β.node p)).1).2 (loc' (β.node p)).2 := by
    obtain ⟨i, hi⟩ := Child.visit_slot p hp
    simpa only [reads, hi, H.node, H'.node] using congrFun hr i
  refine ⟨fun p q hp hq => ?_, fun p hp => ?_, fun p hp => ?_, fun p hp => ?_⟩
  · rw [← loc.injective.eq_iff, ← loc'.injective.eq_iff]
    simp only [H.node, H'.node, Prod.mk.injEq, and_true]
    exact Child.visit_agree hmask hp hq hself hself'
  · rw [H.data, H'.data, recs p hp]
  · rw [H.recv, H'.recv, recs p hp]
  · rw [H.extra, H'.extra, recs p hp]

end OAI.LinearAlgebra.MatrixExponent.Assembly.Window
end

/-!
# The window input for a grouped contraction

The host record keeps the original pattern codes, the local selectors
and one matching input. The latter contains the neighboring interval
labels, with no long host name in a block record.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Window
open Coloring Packing

variable {F : Type} (S : Scheme F) (a n b : ℕ)

abbrev Tags := Format.vec S.m (.vec a (.vec n (.addr (n + 1))))
abbrev Fields := Format.pair S.format
  (.pair (Tags S a n) (.pair (.vec n .bit) (Branches.format S.m a (n + S.e) b)))

abbrev Source := Format.pair (.vec n (.addr S.ℓ)) (.pair (.vec (n + S.e) (.addr b))
  (Match.Input S.d n S.e S.e (n + 1)))

def gather (order : B a → B n → B S.h) (x : (Fields S a n b).obj) :
    (Fmt.groups S.m S.d a (Source S n b)).obj :=
  fun v =>
    let nav := (x.1 v).1
    (nav, fun i =>
      let atom j := (x.1 v).2 (order i j)
      (atom, fun j => x.2.2.2 ((v, i), j), x.2.2.1,
       fun j => (x.2.1 v i j, (S.decode (atom j)).outgoing),
       fun j w => x.2.1 (nav w) i j))

variable {n b}

def matching (x : (Source S n b).obj) := x.2.2

def receiving (x : (Source S n b).obj) (j : B n) (i : B S.e) :=
  ((S.decode (x.1 j)).peer 0 i).map Prod.fst

def detail [Field F] (P : Gadget F) (x : (Source S n b).obj) :
    Scheme.Posting.Detail S (ChoiceTag P) n :=
  (x.1, fun j => Branches.read P (x.2.1 j))

end OAI.LinearAlgebra.MatrixExponent.Assembly.Window
end

/-!
# Forming the grouped window records

Use one exchange for all neighboring labels. Pattern decoding is local
to one old occurrence. The other operations only copy or permute bits.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Window
open Coloring
open scoped Classical

variable {F : Type} (S : Scheme F) (a n b : ℕ)

abbrev Outgoing := Format.vec S.e (.pair .bit (.pair (.addr S.d) (.addr S.e)))
abbrev LabelSet := Format.vec a (.vec n (.addr (n + 1)))
private abbrev ByBlock (A : Format) := Format.vec S.m (.vec a (.vec n A))
private abbrev Remote := Format.vec S.m (.vec S.d (LabelSet a n))

def labelBank (x : (Fields S a n b).obj) : (Fmt.bank S.m S.d (LabelSet a n)).obj :=
  fun i => ((x.1 i).1, x.2.1 i)

def collectCost (v N p : ℕ) :=
  gatherCost S.m S.d v N + 100 * ((Fields S a n b).width + (Fmt.groups S.m S.d a (Source S n b)).width)
    + 2 ^ S.m * 2 ^ a * 2 ^ n * p

variable [Field F] {u v N p : ℕ} {L : Set (Table F)} {I : Type*}

def outgoingGate : Table F :=
  letI : DecidableEq (Outgoing S).obj := Classical.typeDecidableEq _
  lookup F (.addr S.ℓ) (Outgoing S) (fun i y => if (S.decode i).outgoing = y then 1 else 0)

theorem map_outgoing (fit : S.ℓ + (Outgoing S).width ≤ u) (ok : outgoingGate S ∈ L) :
    Map F u L (.addr S.ℓ) (Outgoing S) (fun i => (S.decode i).outgoing)
      (1 + S.ℓ + (Outgoing S).width) := by
  have hw : (Format.addr S.ℓ).width + (Outgoing S).width ≤ u := by rwa [Format.width_addr]
  have hg := Kernel.lookup hw ok
  rw [Format.width_addr] at hg
  exact hg

/-- The arbitrary function in the hypothesis is evaluated on one old
pattern code, independently of the number of hosts and blocks. -/
theorem computes_gather (hu : 3 ≤ u) (ht : Access F u L (S.m + S.d) v N)
    (cap : (LabelSet a n).width ≤ v)
    (out : Map F u L (.addr S.ℓ) (Outgoing S) (fun i => (S.decode i).outgoing) p)
    (order : B a → B n → B S.h) (X : I → (Fields S a n b).obj)
    (recip : ∀ i, Fmt.Reciprocal (LabelSet a n) (labelBank S a n b (X i))) :
    Computes F u L (Fields S a n b) (Fmt.groups S.m S.d a (Source S n b))
      X (gather S a n b order ∘ X) (fun _ => 1) (collectCost S a n b v N p) := by
  let A := Fields S a n b
  let H := Fmt.bank S.m S.d (LabelSet a n)
  let C := ByBlock S a n (.addr S.ℓ)
  let O := ByBlock S a n (Outgoing S)
  let R := Remote S a n
  let D := Fmt.groups S.m S.d a (Source S n b)
  have label : Circuit F A H (labelBank S a n b) (A.width + 2 * H.width) := by
    let pins : H.pins → A.pins
      | (i, .inl t) => .inl (i, .inl t)
      | (i, .inr t) => .inr (.inl (i, t))
    apply Circuit.project pins
    rintro x ⟨i, t|t⟩ <;> rfl
  let pattern (x : A.obj) : C.obj := fun i j k => (x.1 i).2 (order j k)
  have locate : Circuit F A C pattern (A.width + 2 * C.width) :=
    Circuit.project (fun z => .inl (z.1, .inr (order z.2.1 z.2.2.1, z.2.2.2))) (fun _ _ => rfl)
  have expand : Map F u L C O (fun x i j k => (S.decode (x i j k)).outgoing)
      (2 ^ S.m * (2 ^ a * (2 ^ n * p))) :=
    Map.vec _ fun _ => Map.vec _ fun _ => Map.vec _ fun _ => out
  let Y := labelBank S a n b ∘ X
  have relay := (Computes.of_map (x := X) (y := Y) (Map.circuit (L := L) hu label) (fun _ => rfl)).comp
    (gather_neighbors (LabelSet a n) hu ht cap Y recip)
  have keep := Computes.of_map (x := X) (y := X) (Map.circuit (L := L) hu (Circuit.id F A)) (fun _ => rfl)
  have localMap := (Map.circuit hu locate).comp expand
  have middle := keep.pair hu ((Computes.of_map (x := X) localMap (fun _ => rfl)).pair hu relay)
  let W := Format.pair A (.pair O R)
  let join (x : W.obj) : D.obj := fun i =>
    ((x.1.1 i).1, fun j =>
      (pattern x.1 i j, fun t => x.1.2.2.2 ((i, j), t), x.1.2.2.1,
       fun k => (x.1.2.1 i j k, x.2.1 i j k), fun k w => x.2.2 i w j k))
  have post : Circuit F W D join (W.width + 2 * D.width) := by
    let pins : D.pins → W.pins
      | (i, .inl s) => .inl (.inl (i, .inl s))
      | (i, .inr (j, .inl (k, s))) => .inl (.inl (i, .inr (order j k, s)))
      | (i, .inr (j, .inr (.inl (t, s)))) => .inl (.inr (.inr (.inr ⟨((i, j), t), s⟩)))
      | (_, .inr (_, .inr (.inr (.inl s)))) => .inl (.inr (.inr (.inl s)))
      | (i, .inr (j, .inr (.inr (.inr (.inl (k, .inl s)))))) => .inl (.inr (.inl (i, j, k, s)))
      | (i, .inr (j, .inr (.inr (.inr (.inl (k, .inr s)))))) => .inr (.inl (i, j, k, s))
      | (i, .inr (j, .inr (.inr (.inr (.inr (k, w, s)))))) => .inr (.inr (i, w, j, k, s))
    apply Circuit.project pins
    rintro x ⟨i, s | ⟨j, ⟨k, s⟩ | ⟨t, s⟩ | s | ⟨k, s | s⟩ | ⟨k, w, s⟩⟩⟩ <;> rfl
  have H' := middle.comp (Computes.of_map (Map.circuit hu post) (y := gather S a n b order ∘ X)
    (fun _ => rfl))
  simp only [one_mul] at H'
  refine H'.mono ?_
  have hsize : H.width + C.width + O.width + R.width ≤ D.width := by
    simp only [H, C, O, R, D, Remote, LabelSet, ByBlock, Fmt.groups, Fmt.bank, Source,
      Match.Input, Fmt.occ, Outgoing, Format.width_vec, Format.width_pair]
    ring_nf
    omega
  change _ ≤ gatherCost _ _ _ _ + 100 * (A.width + D.width) + _
  rw [show W.width = A.width + (O.width + R.width) by simp only [W, Format.width_pair]]
  simp only [mul_assoc, A]
  omega

end OAI.LinearAlgebra.MatrixExponent.Assembly.Window
end

/-!
# Reading a state from its window tape

The block permutation and the letter decoders are common to all terms.
The state supplies the chosen grouping, color and selectors.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing Window
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k b : ℕ} {B' : ℝ}
  (u : State S P a h z Δ D k B')
  (order : B a → B (h - a) → B S.h) (x : (Fields S a (h - a) b).obj)

structure Supplied : Prop where
  old : x.1 = u.r
  closed : ∀ v j, (u.r (u.p.host v)).1 j ∈ Set.range u.p.host
  index : ∀ v i, order (cellIndex a v) i = u.p.block ((splitCell a u.ha).symm (v, (cellIndex _).symm i))
  label : ∀ v i j, x.2.1 (u.p.host v) (cellIndex a i) j =
    Scheme.Posting.label a u.g (v, i) ((cellIndex _).symm j)
  color : ∀ i, x.2.2.1 i = decide (thick u.m.color ((cellIndex _).symm i))
  choice : ∀ v i, Branches.read P (x.2.2.2 (u.p.placeGroup a v, i)) = u.selector (v, i)

variable {u order x} (hs : u.Supplied order x)
include hs

theorem Supplied.navigate (v : u.G.V) (j : B S.d) :
    u.p.host (u.p.nav v j) = (u.r (u.p.host v)).1 j := by
  have h : ∃ w, u.p.host w = (u.r (u.p.host v)).1 j := hs.closed v j
  rw [Scheme.Posting.nav, dite_eq_left h]
  exact h.choose_spec

theorem Supplied.view :
    Window.View u.env (u.p.placeGroup a) (Window.gather S a (h - a) b order x)
      (Window.matching S) (Window.receiving S) (Window.detail S P) := by
  let tape := Window.gather S a (h - a) b order x
  have layer v i j : ((tape (u.p.host v)).2 (cellIndex a i)).1 j =
      (u.r (u.p.host v)).2 (u.p.block ((splitCell a u.ha).symm (i, (cellIndex _).symm j))) := by
    change (x.1 (u.p.host v)).2 (order (cellIndex a i) j) = _
    rw [hs.old, hs.index]
  constructor
  · rintro ⟨v, i⟩ j
    change (u.p.host (u.p.nav v j), cellIndex a i) = ((x.1 (u.p.host v)).1 j, cellIndex a i)
    rw [hs.old, hs.navigate]
  · rintro ⟨v, i⟩
    change u.p.records a u.ha u.g u.m.color (v, i) =
      (x.2.2.1, fun j => (x.2.1 (u.p.host v) (cellIndex a i) j,
        (S.decode (((tape (u.p.host v)).2 (cellIndex a i)).1 j)).outgoing),
      fun j w => x.2.1 ((x.1 (u.p.host v)).1 w) (cellIndex a i) j)
    simp only [layer, hs.old, ← hs.navigate, hs.label, show x.2.2.1 = _ from funext hs.color]
    rfl
  · rintro ⟨v, i⟩
    funext j t
    change _ = ((S.decode (((tape (u.p.host v)).2 (cellIndex a i)).1 j)).peer 0 t).map Prod.fst
    rw [layer]
    rfl
  · rintro ⟨v, i⟩
    exact Prod.ext (funext fun j => (layer v i j).symm) (funext fun j => (hs.choice (v, i) j).symm)

end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # The short inputs that determine a local contraction record -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing Window
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k b : ℕ} {B' : ℝ}
  (u : State S P a h z Δ D k B')

/-- A parent-group record may include additional counters along with
the source packet. The last field allows the long host names to be
compared using short masks. -/
structure Board (d : ℕ) (A : Format) (read : A.obj → (Source S (h - a) b).obj) where
  parent : (Fmt.groups S.m S.d a A).obj
  child : (Neighborhood.Rows (S.m + ((h - a) + 1)) d).obj
  live : B (S.m + ((h - a) + 1)) → Bool
  self : ∀ i, child i 0 = i
  view : Window.View u.env (u.p.placeGroup a) parent
    (matching S ∘ read) (receiving S ∘ read) (detail S P ∘ read)

variable {u} {v : State S P a h z Δ D k B'} {d : ℕ} {A : Format}
  {read : A.obj → (Source S (h - a) b).obj}

namespace Board
variable (p : u.Board d A read)

abbrev tape := Tile.bank p.live u.col p.child p.parent

def childAt (t : Site (u.G.V × Cell a) (h - a)) :=
  Child.host u.p.host (h - a) (t.1.1, t.2)

def look := Tile.tile p.tape (childAt u.v) (cellIndex a u.v.1.2)

private theorem look_eq :
    p.look = (p.live (childAt u.v), u.col, cellIndex a u.v.1.2, intervalCode _ u.v.2,
      Child.mask (Neighborhood.walks 8 (fun w => (p.parent w).1)) p.child (u.p.host u.v.1.1),
      (reads 8 p.parent (u.p.host u.v.1.1)).2 (cellIndex a u.v.1.2)) :=
  Tile.tile_at p.tape (u.p.placeGroup a u.v.1) (intervalCode _ u.v.2)

variable {p} {q : v.Board d A read}

theorem agrees (he : p.look = q.look) : u.Same v 8 ∧ u.v.1.2 = v.v.1.2 := by
  rw [look_eq, look_eq] at he
  simp only [Prod.mk.injEq] at he
  obtain ⟨_, hc, hg, hl, hm, hr⟩ := he
  exact ⟨⟨p.view.agree q.view hm p.self q.self hr, hc, hl⟩, (cellIndex a).injective hg⟩

theorem index_eq (he : p.look = q.look)
    (x : Site (u.G.V × Cell a) (h - a)) (y : Site (v.G.V × Cell a) (h - a))
    (hr : Related u.env v.env 4 x.1 y.1) (hk : intervalCode _ x.2 = intervalCode _ y.2) :
    Child.index p.child (childAt u.v) (childAt x) = Child.index q.child (childAt v.v) (childAt y) := by
  rw [look_eq, look_eq] at he
  simp only [Prod.mk.injEq] at he
  obtain ⟨_, _, _, hl, hm, _⟩ := he
  have hi := p.view.index_agree q.view hm (related_root.widen (by decide)) (hr.widen (by decide))
    (intervalCode _ u.v.2) (intervalCode _ x.2)
  exact hi.trans (congrArg₂ (fun i j => Child.index q.child (Tile.atHost (v.p.placeGroup a v.v.1) i)
    (Tile.atHost (v.p.placeGroup a y.1) j)) hl hk)

end Board
end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # Canonical host, block, and span addresses for a contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State.Board
open Coloring Packing History Window
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k b : ℕ} {B' : ℝ}
  {u : State S P a h z Δ D k B'} {d : ℕ} {A : Format}
  {read : A.obj → (Source S (h - a) b).obj}
  (p : u.Board d A read)

def recenter (v : Site (u.G.V × Cell a) (h - a)) : (u.recenter v).Board d A read :=
  ⟨p.parent, p.child, p.live, p.self, ⟨p.view.nav, p.view.data, p.view.recv, p.view.extra⟩⟩

def Live : Prop := ∀ i, p.live i = true ↔ i ∈ Set.range (Child.host u.p.host (h - a))

variable {hz : 0 < z} {e : ℕ} (M : Book S P z hz) (room : u.Room e) (cap : ℕ) (le : Δ ≤ D)

abbrev assign : u.Assignment le (M.scheme (S.m + ((h - a) + 1)) d a e cap) :=
  let address := Child.host u.p.host (h - a)
  ⟨address, (cellIndex a).toEmbedding, fun v w => Child.index p.child (address v) (address w),
    fun v => (room.recenter v).visible⟩

theorem look_at (v : Site (u.G.V × Cell a) (h - a)) :
    Tile.tile p.tape ((p.assign M room cap le).vertex v).1 ((p.assign M room cap le).vertex v).2.1 =
      (p.recenter v).look := rfl

theorem live_at (live : p.Live) (i : B (S.m + ((h - a) + 1))) (j : B a) :
    p.live i = true ↔ (i, j, 0) ∈ Set.range (p.assign M room cap le).vertex := by
  rw [live]
  constructor
  · rintro ⟨⟨v, w⟩, rfl⟩
    obtain ⟨b, rfl⟩ := (cellIndex a).surjective j
    exact ⟨((v, b), w), rfl⟩
  · rintro ⟨v, hv⟩
    exact ⟨(v.1.1, v.2), congrArg Prod.fst hv⟩

end OAI.LinearAlgebra.MatrixExponent.Assembly.State.Board
end

/-!
# Transport of charges to a contracted occurrence

Agreement on the local records identifies the contributors to an
occurrence, counting each host once even if several walks reach it.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State
open Coloring Packing Window Finset
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k b : ℕ} {B' : ℝ}
    {u v : State S P a h z Δ D k B'}

theorem Same.route_iff (e : u.Same v 8) {i : u.H.V} {j : v.H.V}
    (hr : Related u.env v.env 2 i j) (t : Cell (h - a)) :
    u.g.route u.m u.col i t = u.v ↔ v.g.route v.m v.col j t = v.v := by
  let w := e.agree.restrict (by decide : 4 ≤ 8)
  have center : Names u.env v.env (u.c.site u.v) (v.c.site v.v) :=
    ⟨related_root.widen (by decide), e.key⟩
  have move : Names u.env v.env
      (u.c.site (u.g.route u.m u.col i t)) (v.c.site (v.g.route v.m v.col j t)) := by
    have hm := w.motion hr u.col (cellIndex _ t)
    have hv := v.c.moved v.col j t
    rw [← e.layout] at hv
    rw [← e.layout]
    exact (u.c.moved u.col i t) ▸ hv ▸ hm
  simpa only [u.c.site.injective.eq_iff, v.c.site.injective.eq_iff] using w.identical move center

namespace Board
variable {d : ℕ} {A : Format} {read : A.obj → (Source S (h - a) b).obj}
    {p : u.Board d A read} {q : v.Board d A read}

/-- Agreement preserves the complete parent record, including any counters
in addition to the fields consumed by the history decoder. -/
theorem source_eq (he : p.look = q.look) {i : u.H.V} {j : v.H.V}
    (hr : Related u.env v.env 2 i j) :
    (p.parent (u.p.placeGroup a i).1).2 (u.p.placeGroup a i).2 =
      (q.parent (v.p.placeGroup a j).1).2 (v.p.placeGroup a j).2 := by
  obtain ⟨path, hp, rfl, rfl⟩ := hr
  have ha := Tile.tile_at p.tape (u.p.placeGroup a u.v.1) (intervalCode _ u.v.2)
  have hb := Tile.tile_at q.tape (v.p.placeGroup a v.v.1) (intervalCode _ v.v.2)
  have hrec := congrArg (fun z => z.2.2.2.2.2) (ha.symm.trans (he.trans hb))
  change (reads 8 p.parent (u.p.placeGroup a u.env.root).1).2 (u.p.placeGroup a u.env.root).2 =
    (reads 8 q.parent (v.p.placeGroup a v.env.root).1).2 (v.p.placeGroup a v.env.root).2 at hrec
  obtain ⟨t, ht⟩ := Child.visit_slot path (hp.trans (by decide : 2 ≤ 8))
  simpa only [reads, ht, p.view.node, q.view.node] using congrFun hrec t

private def inbound (u : State S P a h z Δ D k B') :=
  univ.filter fun t : u.H.V × Cell (h - a) => u.g.route u.m u.col t.1 t.2 = u.v

private theorem inbound_eq (u : State S P a h z Δ D k B') (l : u.H.V × Cell (h - a) → ℝ) :
    push (Function.uncurry (u.g.route u.m u.col)) l u.v = ∑ i ∈ inbound u, l i := by
  unfold Packing.push inbound
  rw [sum_filter]
  apply sum_congr rfl
  rintro ⟨i, b⟩ _
  by_cases he : u.g.route u.m u.col i b = u.v <;> simp [he]

private theorem counterpart (e : u.Same v 8) (i : u.H.V × Cell (h - a)) (hi : i ∈ inbound u) :
    ∃ j ∈ inbound v, Related u.env v.env 2 i.1 j.1 ∧ i.2 = j.2 := by
  have hloc := (mem_filter.mp hi).2
  have place : (u.g.route u.m u.col i.1 i.2).1 = u.v.1 := congrArg Prod.fst hloc
  have win : i.1 ∈ u.env.issuers :=
    (congrArg (fun x => i.1 ∈ u.q.neighborhood x) place).mp (u.q.window_move u.g u.m u.col i.1 i.2)
  obtain ⟨j, _, hj⟩ := Related.issuers (β := v.env) win
  exact ⟨(j, i.2), mem_filter.mpr ⟨mem_univ _, (e.route_iff hj _).mp hloc⟩, hj, rfl⟩

/-- Pushforward adds the charges on the entire fiber of the receiving site. -/
theorem push_eq (he : p.look = q.look) (l : u.H.V × Cell (h - a) → ℝ) (r : v.H.V × Cell (h - a) → ℝ)
    (agree : ∀ i j, Related u.env v.env 2 i j → ∀ t, l (i, t) = r (j, t)) :
    push (Function.uncurry (u.g.route u.m u.col)) l u.v =
      push (Function.uncurry (v.g.route v.m v.col)) r v.v := by
  have e := (agrees he).1
  have same {i i' : u.H.V} {j j' : v.H.V}
      (hi : Related u.env v.env 2 i j) (hj : Related u.env v.env 2 i' j') :
      i = i' ↔ j = j' := (e.agree.restrict (by decide : 2 ≤ 8)).equal hi hj
  choose f hf hrel hblk using counterpart e
  rw [inbound_eq, inbound_eq]
  apply sum_bij f hf
  · intro i hi j hj eq
    exact Prod.ext ((same (hrel _ hi) (hrel _ hj)).mpr (congrArg Prod.fst eq))
      ((hblk _ hi).trans ((congrArg Prod.snd eq).trans (hblk _ hj).symm))
  · intro j hj
    obtain ⟨i, hi, ⟨path, hs, hj', hi'⟩, hb⟩ := counterpart e.symm j hj
    have h : Related u.env v.env 2 i.1 j.1 := ⟨path, hs, hi', hj'⟩
    exact ⟨i, hi, Prod.ext ((same (hrel _ hi) h).mp rfl) ((hblk _ hi).symm.trans hb.symm)⟩
  · intro i hi
    exact (agree _ _ (hrel i hi) i.2).trans (congrArg (fun b => r ((f i hi).1, b)) (hblk i hi))

end Board
end OAI.LinearAlgebra.MatrixExponent.Assembly.State
end

/-! # One local lookup table for every reachable contraction branch -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State.Board
open Coloring Packing History Window
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k b : ℕ} {B' : ℝ}
  {d : ℕ} {A : Format} {read : A.obj → (Source S (h - a) b).obj}
  {hz : 0 < z} {e : ℕ} (M : Book S P z hz) (cap : ℕ) (le : Δ ≤ D)
  {I : Type*} (U : I → State S P a h z Δ D k B')
  (board : ∀ i, (U i).Board d A read) (room : ∀ i, (U i).Room e)
  {Y : Type} (blank : Y)
  (post : I → B (S.m + ((h - a) + 1)) → B a → (Post.record d e M.d (.addr cap)).obj → Y)

theorem print_table (live : ∀ i, (board i).Live)
    (agree : ∀ i j t u, ((board i).recenter t).look = ((board j).recenter u).look →
      ∀ v, post i (childAt t) (cellIndex a t.1.2) v = post j (childAt u) (cellIndex a u.1.2) v)
    (vacant : ∀ i x y, (board i).live x = false → post i x y Post.vacant = blank) :
    ∃ f : (Tile.word S.d a (h - a) d A).obj → Y, ∀ i x y,
      f (Tile.tile (board i).tape x y) =
        post i x y ((U i).records M (room i) cap ((board i).assign M (room i) cap le) x y) := by
  let g i := (board i).assign M (room i) cap le
  have ranked (i : I) : (U i).Ranked (g i) :=
    fun v j => visible_index ((room i).recenter v) j
  let J := Σ i : I, Site ((U i).G.V × Cell a) (h - a)
  let key (x : J) := ((board x.1).recenter x.2).look
  let value (x : J) := post x.1 (childAt x.2) (cellIndex a x.2.1.2)
    (((U x.1).recenter x.2).localRecord M ((room x.1).recenter x.2) cap (g x.1))
  have eqn : Function.FactorsThrough value key := by
    rintro ⟨i, t⟩ ⟨j, u⟩ he
    change ((board i).recenter t).look = ((board j).recenter u).look at he
    have H := (agrees he).1.localRecord (le_refl 8) M ((room i).recenter t) ((room j).recenter u)
      cap (g i) (g j) (index_eq he) (ranked i) (ranked j)
    exact (congrArg _ H).trans (agree i j t u he _)
  let f := Function.extend key value (fun _ => blank)
  refine ⟨f, fun i x y => ?_⟩
  have ht := (board i).live_at M (room i) cap le (live i) x y
  by_cases hl : (board i).live x = true
  · obtain ⟨t, he⟩ := ht.mp hl
    have h₁ : ((g i).vertex t).1 = x := congrArg Prod.fst he
    have h₂ : ((g i).vertex t).2.1 = y := congrArg (fun z => z.2.1) he
    rw [← h₁, ← h₂]
    exact (eqn.extend_apply (fun _ => blank) ⟨i, t⟩).trans
      (congrArg _ ((U i).record_at M (room i) cap (g i) t).symm)
  · have he : Tile.tile (board i).tape x y ∉ Set.range key := by
      rintro ⟨⟨j, t⟩, hq⟩
      have hq' : (board j).live (childAt t) = (board i).live x := congrArg Prod.fst hq
      exact hl (hq' ▸ (live j _).mpr ⟨(t.1.1, t.2), rfl⟩)
    have hv : (U i).records M (room i) cap (g i) x y = Post.vacant :=
      (g i).record_vacant _ _ (x, y, 0) (mt ht.mpr hl)
    exact (Function.extend_apply' _ _ _ he).trans
      ((congrArg _ hv).trans (vacant i x y (Bool.eq_false_iff.mpr hl))).symm

end OAI.LinearAlgebra.MatrixExponent.Assembly.State.Board
end

/-! # Cost of producing every child record with one additional table label -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.State.Board
open Coloring Packing History Window
open scoped Classical

variable {F : Type} [Field F] {S : Scheme F} {P : Gadget F} {a h z Δ D k b : ℕ} {B' : ℝ}
  {u : State S P a h z Δ D k B'} {d : ℕ} {A : Format}
  {read : A.obj → (Source S (h - a) b).obj}

def raw (p : u.Board d A read) : (Tile.raw S.m S.d a (h - a) d A).obj :=
  (p.live, u.col, p.child, p.parent)

variable {hz : 0 < z} {e : ℕ} (M : Book S P z hz) (cap : ℕ) (le : Δ ≤ D)
    {I : Type*} (U : I → State S P a h z Δ D k B')
    (board : ∀ i, (U i).Board d A read) (room : ∀ i, (U i).Room e)
    (Y : Format) (blank : Y.obj)
    (post : I → B (S.m + ((h - a) + 1)) → B a → (Post.record d e M.d (.addr cap)).obj → Y.obj)

/-- The table is fixed for the entire family, before choosing the
routing bound or admissible dictionary. -/
theorem print_net (live : ∀ i, (board i).Live)
    (agree : ∀ i j t u, ((board i).recenter t).look = ((board j).recenter u).look →
      ∀ v, post i (childAt t) (cellIndex a t.1.2) v = post j (childAt u) (cellIndex a u.1.2) v)
    (vacant : ∀ i x y, (board i).live x = false → post i x y Post.vacant = blank)
    (recip : ∀ i, Fmt.Reciprocal (.vec a A) (board i).parent) :
    ∃ table : Table F, wd table.1 + wd table.2.1 = (Tile.word S.d a (h - a) d A).width + Y.width ∧
      ∀ {u v N t : ℕ} {L : Set (Table F)},
      3 ≤ u → table ∈ L → (Tile.word S.d a (h - a) d A).width + Y.width ≤ u →
      Access F u L (S.m + S.d) v N → 2 ^ a * (Walks 8 S.d A).width ≤ v →
      S.m + ((h - a) + 1) ≤ t → 2 ^ (Tile.radius S.d + ((h - a) + 1)) ≤ t → 2 ^ d ≤ t →
      Computes F u L (Tile.raw S.m S.d a (h - a) d A) (Tile.output S.m a (h - a) Y)
        (fun i => (board i).raw)
        (fun i x y => post i x y ((U i).records M (room i) cap ((board i).assign M (room i) cap le) x y))
        (fun _ => 1) (Tile.bankCost S.m S.d a (h - a) d A v N t + Tile.cost S.m S.d a (h - a) d A Y) := by
  obtain ⟨f, hf⟩ := print_table M cap le U board room blank post live agree vacant
  refine ⟨Tile.gate F (H := Y) f, by simp only [Tile.gate, lookup, wd_word], ?_⟩
  intro u v N t L hu allowed fit access send hm hq hd
  have H := Tile.print_net hu access send hm hq hd (fun i => (board i).raw) recip f fit allowed
  have eqn : (fun i x y => f (Tile.tile (Tile.fill (board i).raw) x y)) =
      fun i x y => post i x y ((U i).records M (room i) cap ((board i).assign M (room i) cap le) x y) :=
    funext fun i => funext fun x => funext fun y => hf i x y
  rwa [eqn] at H

end OAI.LinearAlgebra.MatrixExponent.Assembly.State.Board
end
