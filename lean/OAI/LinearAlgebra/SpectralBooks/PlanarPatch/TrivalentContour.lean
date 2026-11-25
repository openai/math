import OAI.LinearAlgebra.SpectralBooks.PlanarPatch.TrivalentOpenShape
import OAI.Geometry.HyperbolicGroups.BoundaryList

/-! # The oriented disk boundary of a trivalent tensor tree

A turn visits output, left input, and right input in that order. Crossing an
internal edge before turning visits the left subtree before the right one.
The root output and the leaf inputs are the unpaired darts of this walk.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section
namespace PlanarPatch.TrivalentTree

open Equiv HyperbolicObstruction.PictureSwitch
open scoped Classical

variable {F V D : Type*} {d : V → ℕ} {q : ℕ}

/-- Progress to the next slot in the positive rotation. -/
def positivePosition : Perm (Option Bool) where
  toFun | none => some false | some false => some true | some true => none
  invFun | none => some true | some false => none | some true => some false
  left_inv := by rintro (_ | (_ | _)) <;> rfl
  right_inv := by rintro (_ | (_ | _)) <;> rfl

/-- Vertex rotation on the actual internal ports and stubs. -/
def positiveTurn (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) : Perm t.TreeEnd :=
  (t.treeEndEquiv h).trans (((Equiv.refl t.Role).prodCongr positivePosition).trans (t.treeEndEquiv h).symm)

/-- Crossing a retained wire interchanges its two darts and fixes the stubs. -/
def internalPairing (t : TrivalentTree F d q) : Perm t.TreeEnd where
  toFun | .inl (w,b) => .inl (w,!b) | .inr s => .inr s
  invFun | .inl (w,b) => .inl (w,!b) | .inr s => .inr s
  left_inv := by rintro (⟨w, _ | _⟩ | s) <;> rfl
  right_inv := by rintro (⟨w, _ | _⟩ | s) <;> rfl

/-- At a stub the walk turns, while at an internal port it first crosses the wire. -/
def diskTurn (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) : Perm t.TreeEnd :=
  t.positiveTurn h * t.internalPairing

private abbrev Slots (D : Type*) := List Bool → Option Bool → D

private def descend (f : Slots D) (b : Bool) : Slots D := fun p => f (b :: p)

/-- Visit both input slots, traversing each child before returning through the output. -/
private def body : {q : ℕ} → TrivalentTree F d q → Slots D → List D
  | _, .port _, _ => []
  | _, .branch _ l r, f =>
    f [] (some false) :: (body l (descend f false) ++
      f [] (some true) :: (body r (descend f true) ++ [f [] none]))

private def atEnd (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) : Slots t.TreeEnd :=
  fun p pos => if hp : p ∈ t.branchAddresses then (t.treeEndEquiv h).symm (⟨p,hp⟩,pos) else .inr none

private theorem atEnd_valid (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses)
    (p : t.Role) (a : Option Bool) :
    t.atEnd h p.val a = (t.treeEndEquiv h).symm (p,a) := by simp [atEnd,p.property]

private theorem pair_pos (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses)
    (p : t.Role) (b : Bool) (hc : p.val ++ [b] ∈ t.branchAddresses) :
    t.internalPairing (t.atEnd h p.val (some b)) = t.atEnd h (p.val ++ [b]) none := by
  simp only [atEnd, p.property, hc, ↓reduceDIte, treeEndEquiv]
  simp [openOutputEnd,openChildEnd,hc,internalPairing]

private theorem pair_leaf (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses)
    (p : t.Role) (b : Bool) (hc : p.val ++ [b] ∉ t.branchAddresses) :
    t.internalPairing (t.atEnd h p.val (some b)) = t.atEnd h p.val (some b) := by
  simp only [atEnd, p.property, ↓reduceDIte, treeEndEquiv]
  simp [openChildEnd,hc,internalPairing]

private theorem turn_pos (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses)
    (p : List Bool) (hp : p ∈ t.branchAddresses) (a : Option Bool) :
    t.positiveTurn h (t.atEnd h p a) = t.atEnd h p (positivePosition a) := by
  simp [atEnd,hp,positiveTurn]

private theorem pair_root (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) :
    t.internalPairing (t.atEnd h [] none) = t.atEnd h [] none := by
  simp [atEnd,h,treeEndEquiv,openOutputEnd,internalPairing]

private theorem body_length (t : TrivalentTree F d q) (f : Slots D) :
    (body t f).length = 3*t.vertices := by
  induction t generalizing f with
  | port => rfl
  | branch B l r il ir =>
    simp only [body, List.length_cons, List.length_append,List.length_nil,il,ir,vertices]
    omega

private theorem mem_body (t : TrivalentTree F d q) (f : Slots D)
    (p : List Bool) (hp : p ∈ t.branchAddresses) (a : Option Bool) : f p a ∈ body t f := by
  induction t generalizing f p with
  | port => simp [branchAddresses] at hp
  | branch B l r il ir =>
    cases p with
    | nil => rcases a with _ | (_ | _) <;> simp [body]
    | cons b p =>
      cases b
      · have h := il (descend f false) p ((left_mem_branchAddresses ..).mp hp)
        simp only [descend] at h
        simp [body,h]
      · have h := ir (descend f true) p ((right_mem_branchAddresses ..).mp hp)
        simp only [descend] at h
        simp [body,h]

/-- The port list begins at the distinguished output. -/
def diskWalk : {q : ℕ} → (t : TrivalentTree F d q) → [] ∈ t.branchAddresses → List t.TreeEnd
  | _, .port _, h => False.elim (by simp [branchAddresses] at h)
  | _, .branch B l r, h =>
    let f := (branch B l r).atEnd h
    f [] none :: f [] (some false) :: (body l (descend f false) ++
      f [] (some true) :: body r (descend f true))

private theorem body_perm_walk (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) :
    (body t (t.atEnd h)).Perm (diskWalk t h) := by
  cases t with
  | port => simp [branchAddresses] at h
  | branch B l r =>
    unfold body diskWalk
    simp only [← List.cons_append,← List.append_assoc]
    exact List.perm_append_singleton ..

theorem diskWalk_all (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) (e : t.TreeEnd) :
    e ∈ diskWalk t h := by
  let p := t.treeEndEquiv h e
  have he := mem_body t (t.atEnd h) p.1.val p.1.property p.2
  rw [atEnd_valid] at he
  exact (body_perm_walk t h).mem_iff.mp (by simpa [p] using he)

theorem diskWalk_nodup (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) :
    (diskWalk t h).Nodup := by
  have hl := (body_perm_walk t h).length_eq
  rw [body_length] at hl
  have hc := Fintype.card_congr (t.treeEndEquiv h)
  rw [Fintype.card_prod,card_role,Fintype.card_option,Fintype.card_bool] at hc
  classical
  refine Multiset.coe_nodup.mp ((Multiset.toFinset_card_eq_card_iff_nodup
    (m := ((diskWalk t h : List t.TreeEnd) : Multiset t.TreeEnd))).mp ?_)
  change (diskWalk t h).toFinset.card = (diskWalk t h).length
  have he : (diskWalk t h).toFinset = Finset.univ := by ext; simp [diskWalk_all]
  rw [he,Finset.card_univ,hc,← hl]; omega

/-- `Run f a xs b` visits the entries of `xs` in order, starting at `a`, and ends
one step beyond the final entry at `b`. -/
private inductive Run (f : D → D) : D → List D → D → Prop
  | nil (a : D) : Run f a [] a
  | cons {a b : D} {xs : List D} : Run f (f a) xs b → Run f a (a :: xs) b

private theorem Run.append {f : D → D} {a b c : D} {xs ys : List D}
    (hx : Run f a xs b) (hy : Run f b ys c) : Run f a (xs ++ ys) c := by
  induction hx with
  | nil => exact hy
  | cons _ ih => exact .cons (ih hy)

private theorem Run.one {f : D → D} {a b : D} (h : f a = b) : Run f a [a] b :=
  h ▸ Run.cons (Run.nil _)

private theorem Run.get_next {f : D → D} {a b : D} {xs : List D} (r : Run f a xs b) :
    ∀ i (hi : i < xs.length), f xs[i] = (xs ++ [b])[i+1]'(by simp; omega) := by
  induction r with
  | nil => simp
  | @cons a b xs h ih =>
    intro i hi
    cases i with
    | zero =>
      cases h <;> rfl
    | succ i =>
      exact ih i (by simpa using hi)

private theorem Run.boundary [DecidableEq D] {f : Perm D} {a : D} {xs : List D}
    (r : Run f a xs a) (hn : xs.Nodup) : IsBoundary f xs := by
  refine ⟨hn, ?_⟩
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hx
  rw [List.formPerm_apply_getElem xs hn i hi]
  have h := r.get_next i hi
  by_cases hlt : i+1 < xs.length
  · simpa only [Nat.mod_eq_of_lt hlt,List.getElem_append_left hlt] using h
  · have he : i+1 = xs.length := by omega
    rw [List.getElem_concat_length he] at h
    have hhead : xs[0]'(by omega) = a := by
      cases r with
      | nil => simp at hi
      | cons => rfl
    simpa only [he,Nat.mod_self,hhead] using h

private theorem pair_return (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses)
    (p : t.Role) (b : Bool) (hc : p.val ++ [b] ∈ t.branchAddresses) :
    t.internalPairing (t.atEnd h (p.val ++ [b]) none) = t.atEnd h p.val (some b) := by
  rw [← t.pair_pos h p b hc]
  generalize t.atEnd h p.val (some b) = e
  rcases e with ⟨w, _ | _⟩ | s <;> rfl

private def subslots (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) (p : List Bool) :
    Slots t.TreeEnd := fun a => t.atEnd h (p ++ a)

private theorem descend_subslots (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) (p) (b) :
    descend (t.subslots h p) b = t.subslots h (p ++ [b]) := by
  funext a
  simp [descend,subslots]

private theorem child_run (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) {i : ℕ}
    (u : TrivalentTree F d i) (p : t.Role) (b : Bool)
    (hs : ∀ a, (p.val ++ [b]) ++ a ∈ t.branchAddresses ↔ a ∈ u.branchAddresses) :
    Run (t.diskTurn h) (t.atEnd h p.val (some b))
      (t.atEnd h p.val (some b) :: body u (t.subslots h (p.val ++ [b])))
      (t.atEnd h p.val (positivePosition (some b))) := by
  induction u generalizing p b with
  | port v =>
    apply Run.one
    have hn : p.val ++ [b] ∉ t.branchAddresses := by simpa [branchAddresses] using hs []
    exact (congrArg (t.positiveTurn h) (t.pair_leaf h p b hn)).trans
      (t.turn_pos h p.val p.property (some b))
  | branch B l r il ir =>
    have hn : p.val ++ [b] ∈ t.branchAddresses := by simpa using (hs []).mpr (nil_mem_branchAddresses ..)
    let child : t.Role := ⟨p.val ++ [b],hn⟩
    have descend_left := il child false (fun a => by
      change ((p.val ++ [b]) ++ [false]) ++ a ∈ t.branchAddresses ↔ _
      rw [List.append_assoc]; exact (hs (false :: a)).trans (left_mem_branchAddresses ..))
    have descend_right := ir child true (fun a => by
      change ((p.val ++ [b]) ++ [true]) ++ a ∈ t.branchAddresses ↔ _
      rw [List.append_assoc]; exact (hs (true :: a)).trans (right_mem_branchAddresses ..))
    have enter : t.diskTurn h (t.atEnd h p.val (some b)) = t.atEnd h child.val (some false) :=
      (congrArg (t.positiveTurn h) (t.pair_pos h p b hn)).trans (t.turn_pos h _ hn none)
    have leave : t.diskTurn h (t.atEnd h child.val none) =
        t.atEnd h p.val (positivePosition (some b)) :=
      (congrArg (t.positiveTurn h) (t.pair_return h p b hn)).trans (t.turn_pos h _ p.property _)
    apply Run.cons
    rw [enter]
    simp only [body, descend_subslots]
    simpa [positivePosition,subslots, child, List.append_assoc] using
      (descend_left.append (descend_right.append (Run.one leave)))

private theorem diskWalk_run (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) :
    Run (t.diskTurn h) (t.atEnd h [] none) (diskWalk t h) (t.atEnd h [] none) := by
  cases t with
  | port => simp [branchAddresses] at h
  | branch B l r =>
    let t := branch B l r
    let root : t.Role := ⟨[],h⟩
    have left := t.child_run h l root false (fun a => left_mem_branchAddresses ..)
    have right := t.child_run h r root true (fun a => right_mem_branchAddresses ..)
    apply Run.cons
    have he : t.diskTurn h (t.atEnd h [] none) = t.atEnd h [] (some false) :=
      (congrArg (t.positiveTurn h) (t.pair_root h)).trans (t.turn_pos h [] h none)
    rw [he]
    change Run (t.diskTurn h) (t.atEnd h [] (some false))
      (t.atEnd h [] (some false) :: (body l (t.subslots h [false]) ++
        t.atEnd h [] (some true) :: body r (t.subslots h [true]))) (t.atEnd h [] none)
    simpa [positivePosition,root] using left.append right

/-- The literal port walk is the positive boundary of the vertex disks and all
internal tree bands. Every port occurs exactly once, including external stubs. -/
theorem diskWalk_isBoundary (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) :
    IsBoundary (t.diskTurn h) (diskWalk t h) :=
  (t.diskWalk_run h).boundary (t.diskWalk_nodup h)

/-- Read only the unpaired darts of the disk, retaining each named stub. -/
def readStub (t : TrivalentTree F d q) : t.TreeEnd → Option t.Stub
  | .inl _ => none
  | .inr s => some s

private def stubPath (t : TrivalentTree F d q) (e : t.TreeEnd) : Option (Option (List Bool)) :=
  (t.readStub e).map (Option.map Subtype.val)

private theorem read_child_leaf (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses)
    (p : t.Role) (b : Bool) (hc : p.val ++ [b] ∉ t.branchAddresses) :
    t.stubPath (t.atEnd h p.val (some b)) = some (some (p.val ++ [b])) := by
  simp [stubPath,atEnd,p.property,treeEndEquiv,openChildEnd,hc,readStub]

private theorem skip_child (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses)
    (p : t.Role) (b : Bool) (hc : p.val ++ [b] ∈ t.branchAddresses) :
    t.stubPath (t.atEnd h p.val (some b)) = none ∧
    t.stubPath (t.atEnd h (p.val ++ [b]) none) = none := by
  simp [stubPath,atEnd,p.property,treeEndEquiv,openChildEnd,openOutputEnd,hc,readStub]

private theorem child_stubs (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) {i : ℕ}
    (u : TrivalentTree F d i) (p : t.Role) (b : Bool)
    (hs : ∀ a, (p.val ++ [b]) ++ a ∈ t.branchAddresses ↔ a ∈ u.branchAddresses) :
    (t.atEnd h p.val (some b) :: body u (t.subslots h (p.val ++ [b]))).filterMap t.stubPath =
      u.leafPaths.map (fun a => some ((p.val ++ [b]) ++ a)) := by
  induction u generalizing p b with
  | port v =>
    have hn : p.val ++ [b] ∉ t.branchAddresses := by simpa [branchAddresses] using hs []
    simp [body,leafPaths,t.read_child_leaf h p b hn]
  | branch B l r il ir =>
    have hn : p.val ++ [b] ∈ t.branchAddresses := by simpa using (hs []).mpr (nil_mem_branchAddresses ..)
    let child : t.Role := ⟨p.val ++ [b],hn⟩
    have left := il child false (fun a => by
      change ((p.val ++ [b]) ++ [false]) ++ a ∈ t.branchAddresses ↔ _
      rw [List.append_assoc]; exact (hs (false :: a)).trans (left_mem_branchAddresses ..))
    have right := ir child true (fun a => by
      change ((p.val ++ [b]) ++ [true]) ++ a ∈ t.branchAddresses ↔ _
      rw [List.append_assoc]; exact (hs (true :: a)).trans (right_mem_branchAddresses ..))
    have he := t.skip_child h p b hn
    rw [List.filterMap_cons, he.1]
    simp only [body,descend_subslots]
    have join (a z o : t.TreeEnd) (ls rs : List t.TreeEnd) :
        a :: (ls ++ z :: (rs ++ [o])) = ((a :: ls) ++ (z :: rs)) ++ [o] := by simp
    rw [join,List.filterMap_append,List.filterMap_append]
    have sub_empty (pos : Option Bool) : t.subslots h (p.val ++ [b]) [] pos = t.atEnd h child.val pos := by simp [subslots,child]
    simp only [sub_empty]
    change (t.atEnd h child.val (some false) :: body l (t.subslots h (child.val ++ [false]))).filterMap t.stubPath ++
      (t.atEnd h child.val (some true) :: body r (t.subslots h (child.val ++ [true]))).filterMap t.stubPath ++
      [t.atEnd h (p.val ++ [b]) none].filterMap t.stubPath = _
    rw [left,right]
    simp [he.2,leafPaths,Function.comp_def,child]

/-- The stubs as encountered on the positive boundary, based at the output. -/
theorem diskWalk_stubs (t : TrivalentTree F d q) (h : [] ∈ t.branchAddresses) :
    (t.diskWalk h).filterMap t.readStub = none :: t.leafPaths.attach.map some := by
  apply List.map_injective_iff.mpr (Option.map_injective Subtype.val_injective)
  rw [List.map_filterMap]
  change (t.diskWalk h).filterMap t.stubPath = _
  cases t with
  | port => simp [branchAddresses] at h
  | branch B l r =>
    let t := branch B l r
    let root : t.Role := ⟨[],h⟩
    have left := t.child_stubs h l root false (fun a => left_mem_branchAddresses ..)
    have right := t.child_stubs h r root true (fun a => right_mem_branchAddresses ..)
    have he : t.stubPath (t.atEnd h [] none) = some none := by
      simp [stubPath,atEnd,treeEndEquiv,openOutputEnd,readStub]
    change (t.atEnd h [] none :: ((t.atEnd h root.val (some false) ::
      body l (t.subslots h (root.val ++ [false]))) ++ (t.atEnd h root.val (some true) ::
      body r (t.subslots h (root.val ++ [true]))))).filterMap t.stubPath = _
    rw [List.filterMap_cons,he,List.filterMap_append,left,right]
    simp [root,leafPaths,Function.comp_def]

end PlanarPatch.TrivalentTree

end

end SpectralBooks
end LinearAlgebra
end OAI
