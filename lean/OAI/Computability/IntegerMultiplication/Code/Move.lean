import OAI.Computability.IntegerMultiplication.Code.Tree

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Code

def scatter (l : List ℕ) (x : Tree) (r : Deck) : Deck :=
  l.foldr (fun i => pile i x) r

theorem scatter_nil (x : Tree) (r : Deck) : scatter [] x r = r := rfl
theorem scatter_cons (i l x r) : scatter (i::l) x r = pile i x (scatter l x r) := rfl

theorem pile_scatter (l : List ℕ) (x : Tree) (r : Deck) (i) (y : Tree) (h : i ∉ l) :
    pile i y (scatter l x r) = scatter l x (pile i y r) := by
  induction l with
  | nil => rfl
  | cons j l ih =>
    simp only [List.mem_cons, not_or] at h
    simp only [scatter_cons, pile_comm i y _ j x h.1, ih h.2]

/-- Macros with a fixed list of stack parameters in the program. -/
def flood (l : List ℕ) (c : ℕ → Cmd) : Cmd :=
  match l with
  | [] => .pass
  | i::l => (c i).join (flood l c)

theorem fits_flood_atom (b : Bool) (d : List ℕ) (env : Env) (r : Deck) (hd : d.Nodup) :
    Fits env (flood d (fun i => give i b)) r (scatter d (.atom b) r) (3*d.length+1) := by
  induction d generalizing r with
  | nil => exact Fits.pass _
  | cons i l ih =>
    simp only [List.nodup_cons] at hd
    rw [flood, scatter_cons, pile_scatter l _ r i _ hd.1]
    -- simp didn't know order? x=y
    simp only [List.length_cons]
    exact ((fits_give b r i env).join (ih _ hd.2)).mono (by omega)

theorem fits_flood_pack (x y : Tree) (d : List ℕ) (env : Env) (r : Deck) (hd : d.Nodup) :
    Fits env (flood d pack) (scatter d x (scatter d y r)) (scatter d (.fork x y) r) (3*d.length+1) := by
  induction d generalizing r with
  | nil => simpa [scatter_nil, flood] using Fits.pass (env := env) r
  | cons i l ih =>
    simp only [List.nodup_cons] at hd
    have hw := ih (pile i (.fork x y) r) hd.2
    simp only [scatter_cons, flood]
    have hm := fits_pack x y (scatter l x (scatter l y r)) i env
    -- input pile i x (scatter l x (pile i y ...))
    rw [← pile_scatter l x (scatter l y r) i y hd.1]
    -- ih with packed parked on i
    rw [← pile_scatter l y r i (.fork x y) hd.1,
        ← pile_scatter l x (scatter l y r) i (.fork x y) hd.1,
        ← pile_scatter l (.fork x y) r i (.fork x y) hd.1] at hw
    simp only [List.length_cons]
    exact (hm.join hw).mono (by omega)

/-- Consume the value on i, sending a reflected copy to each of d. -/
def forwardBody (i : ℕ) (d : List ℕ) :=
  splitRoot i (fun b => flood d (fun j => give j b)) <|
    (.join (.again 0) (.join (.again 0) (flood d pack)))

def forward (i : ℕ) (d : List ℕ) : Cmd :=
  Prog.tie (forwardBody i d)

theorem fits_forward_body (i : ℕ) (d : List ℕ) (hd : d.Nodup) (hi : i ∉ d)
    (env : Env) (x : Tree) (r : Deck) :
    Fits (forwardBody i d::env) (forwardBody i d)
      (pile i x r) (scatter d x.flip r) ((16+3*d.length)*x.count) := by
  let g := forwardBody i d :: env
  change Fits g _ _ _ _
  induction x generalizing r with
  | atom b =>
    exact (fits_bit (fits_flood_atom b d _ r hd)).mono (by
      dsimp [Tree.count]; omega)
  | fork x y hx hy =>
    have ha := Fits.again0 (hx (pile i y r))
    rw [← pile_scatter d x.flip r i y hi] at ha
    have hb := Fits.again0 (hy (scatter d x.flip r))
    have hc := fits_flood_pack y.flip x.flip d g r hd
    exact (fits_pair (ha.join (hb.join hc))).mono (by
      simp only [Tree.count, Nat.mul_add, Nat.mul_one]
      omega)

theorem fits_forward (i : ℕ) (d : List ℕ) (hd : d.Nodup) (hi : i ∉ d)
    (env : Env) (x : Tree) (r : Deck) :
    Fits env (forward i d)
      (pile i x r) (scatter d x.flip r) ((17+3*d.length)*x.count) :=
  (Fits.tie (fits_forward_body i d hd hi _ _ _)).mono (by
    let a := d.length
    have h : 17+3*d.length = (16+3*d.length)+1 := by omega
    rw [h]; simp only [Nat.add_mul, Nat.one_mul]
    have := x.count_pos
    omega)

/-- The empty list of destinations discards the value. -/
def discard (i : ℕ) := forward i []

/-- Move using an intermediate stack, restoring it. Make this a third, fresh register,
charged and accessed only for this value. -/
def move (i j u : ℕ) : Cmd :=
  (forward i [u]).join (forward u [j])

/-- Copy using an intermediate stack (j=i also possible? destinations must be distinct,
no use). -/
def clone (i j u : ℕ) : Cmd :=
  (forward i [u]).join (forward u [i,j])

theorem fits_discard (i : ℕ) (x : Tree) (env r) :
    Fits env (discard i) (pile i x r) r (17*x.count) :=
  fits_forward i [] (by simp) (by simp) env x r

theorem fits_move {i j u : ℕ} (h : i≠u) (e : u≠j) (x : Tree) (env r) :
    Fits env (move i j u) (pile i x r) (pile j x r) (42*x.count) := by
  have ha := fits_forward i [u] (by simp) (by simpa using h) env x r
  have hb := fits_forward u [j] (by simp) (by simpa using e) env x.flip r
  change Fits env _ _ (pile u x.flip r) _ at ha
  change Fits env _ _ (pile j _ r) _ at hb
  simp only [Tree.flip_flip,Tree.count_flip,List.length_cons,List.length_nil] at hb
  exact (ha.join hb).mono (by
    simp only [List.length_cons,List.length_nil]
    have := x.count_pos
    omega)

theorem fits_clone {i j u : ℕ} (h : i≠u) (e : u≠j) (f : i≠j) (x : Tree) (env r) :
    Fits env (clone i j u) (pile i x r) (pile i x (pile j x r)) (45*x.count) := by
  have ha := fits_forward i [u] (by simp) (by simpa using h) env x r
  have hb := fits_forward u [i,j] (by simpa using f) (by simp [e,Ne.symm h]) env x.flip r
  change Fits env _ _ (pile u x.flip r) _ at ha
  change Fits env _ _ (pile i _ (pile j _ r)) _ at hb
  simp only [Tree.flip_flip,Tree.count_flip,List.length_cons,List.length_nil] at hb
  exact (ha.join hb).mono (by
    simp only [List.length_cons,List.length_nil]
    have := x.count_pos
    omega)

end Code

end IntegerMultiplication
end Computability
end OAI
