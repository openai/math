import OAI.Hierarchy.DescentBundleHistory
import OAI.Hierarchy.DescentBundleScalar
import OAI.Hierarchy.DescentBitDescription
import OAI.Hierarchy.DescentCableUnbundling

namespace OAI
/-! # Terminal local contractions with one named field per true aligned payload -/

namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {U A F : Type} [CommSemiring F] {w : A→ℕ} {p : ℕ} (hp : 0<p) {r : BitRecipe U A w}

def Slice.code {α : Type} (s : Slice p α) : SliceCode := ⟨s.start,s.stride,s.count⟩
def Slice.names {α : Type} (s : Slice p α) : List α := List.ofFn s.get

theorem Slice.eval_code {α : Type} (s : Slice p α) (x : α→Word p) :
    s.code.eval p (s.names.map (wordList ∘ x)) =
      wordList (fun d=>x (s.get (s.index d)) (s.offset d)) := by
  apply congrArg List.ofFn
  funext d
  have pos : 0<p:=Nat.lt_of_le_of_lt (Nat.zero_le d.val) d.isLt
  simp [code,names,wordList,Function.comp_def,s.fits d,
    Slice.index,Slice.offset,Nat.mod_lt _ pos]

abbrev Private (r : BitRecipe U A w) (p : ℕ) := Σh : r.Hidden,Fin (r.hiddenWidth h/p)

def privateIndex (b : BlockRef p r.hiddenWidth) : Private r p :=
  ⟨b.port,⟨b.block,(Nat.le_div_iff_mul_le hp).2 b.fits⟩⟩

def Shape.hiddenWords (s : Shape p r) :
    ((h : r.Hidden)→Word (r.hiddenWidth h))≃(Private r p→Word p) :=
  (Equiv.piCongrRight (fun h=>DescentCableUnbundling.splitWord (Nat.div_mul_cancel (s.hiddenMultiple h)).symm)).trans
    (Equiv.piCurry (fun (_ : r.Hidden) (_ : Fin (_/p))=>Word p)).symm

theorem Shape.hiddenWords_read (s : Shape p r) (z : (h:r.Hidden)→Word (r.hiddenWidth h))
    (b : BlockRef p r.hiddenWidth) (d : Fin p) :
    s.hiddenWords z (privateIndex hp b) d=z b.port (b.atBit d).2 := by
  apply congrArg (z b.port)
  apply Fin.ext
  change d.val+p*b.block=b.block*p+d.val
  ring

def Shape.rows (s : Shape p r) (u : r.Node) :=
  List.ofFn (fun j=>List.ofFn (fun g=>s.chunk u j g))

def Shape.keys (s : Shape p r) (u : r.Node) := (s.rows u).flatMap (List.flatMap Slice.names)

def Shape.recipe (s : Shape p r) : Recipe (U×List (List SliceCode)) (BlockRef p w) where
  Hidden := Private r p
  width _ := p
  Node := r.Node
  tag u := (r.tag u,(s.rows u).map (List.map Slice.code))
  arity u := (s.keys u).length
  operand u j := (s.keys u)[j.val].map id (privateIndex hp)

theorem Shape.recipe_refs (s : Shape p r) (u : r.Node) :
    (s.recipe hp).arity u=∑j,∑g,(s.chunk u j g).count := by
  simp [recipe,keys,rows,Slice.names,List.length_flatMap,List.sum_ofFn]

private theorem word_chunks {t a : ℕ} (eqn : t=a*p) (x : Word t) :
    (List.ofFn (fun g : Fin a=>wordList (fun d : Fin p=>x (Fin.cast eqn.symm (finProdFinEquiv (g,d)))))).flatten=
      wordList x := by
  subst t
  rw [wordList,List.ofFn_mul]
  apply congrArg List.flatten
  apply congrArg List.ofFn
  funext g
  apply congrArg List.ofFn
  funext d
  apply congrArg x
  apply Fin.ext
  change d.val+p*g.val=g.val*p+d.val
  ring

theorem Shape.recipe_value (s : Shape p r) (scalar : U→List (List Bool)→F) (x : BitRef w→Bool) :
    (s.recipe hp).value (bundleScalar p scalar) (fun b=>wordList (fun d=>x (b.atBit d)))=r.value scalar x := by
  let fetch (z : (h:r.Hidden)→Word (r.hiddenWidth h)) (b : BlockRef p w⊕BlockRef p r.hiddenWidth) : Word p :=
    b.elim (fun a d=>x (a.atBit d)) (fun a d=>z a.port (a.atBit d).2)
  unfold Recipe.value BitRecipe.value
  refine Finset.sum_bij' (fun z _=>s.hiddenWords.symm z) (fun h _=>s.hiddenWords h)
    (fun _ _=>Finset.mem_univ _) (fun _ _=>Finset.mem_univ _) (fun z _=>s.hiddenWords.apply_symm_apply z) (fun h _=>s.hiddenWords.symm_apply_apply h) ?_
  intro z _
  change Private r p→Word p at z
  let h := s.hiddenWords.symm z
  have saved (a : BlockRef p r.hiddenWidth) (d : Fin p) : z (privateIndex hp a) d=h a.port (a.atBit d).2 := by
    have same : s.hiddenWords h=z:=s.hiddenWords.apply_symm_apply z
    exact (congrArg (fun words : Private r p→Word p=>words (privateIndex hp a) d) same.symm).trans
      (s.hiddenWords_read hp h a d)
  apply Finset.prod_congr (congrArg (@Finset.univ _) (Subsingleton.elim _ _))
  intro u _
  change r.Node at u
  let publicRead (b : BlockRef p w) := wordList (fun d=>x (b.atBit d))
  let privateRead (b : Private r p) := wordList (z b)
  have ordered : List.ofFn (fun j : Fin ((s.recipe hp).arity u)=>
      ((s.recipe hp).operand u j).elim publicRead privateRead)=(s.keys u).map (wordList ∘ fetch h) := by
    apply List.ext_getElem
    · simp [recipe]
    · intro i hi hj
      have bound : i<(s.keys u).length := by simpa using hj
      simp only [List.getElem_ofFn,List.getElem_map,recipe]
      cases loc : (s.keys u)[i] with
      | inl a=>rfl
      | inr a=>exact congrArg wordList (funext (saved a))
  change bundleScalar p scalar _ (List.ofFn (fun j=>((s.recipe hp).operand u j).elim publicRead privateRead))=_
  rw [ordered]
  unfold bundleScalar
  apply congrArg (scalar (r.tag u))
  rw [show (s.keys u)=(s.rows u).flatMap (List.flatMap Slice.names) from rfl]
  rw [show ((s.recipe hp).tag u).2=(s.rows u).map (List.map Slice.code) from rfl]
  rw [evalRows_true (wordList ∘ fetch h) Slice.code Slice.names (by intro sl;simp [Slice.names,Slice.code])]
  simp only [rows,List.map_ofFn]
  apply congrArg List.ofFn
  funext j
  simp only [Function.comp_apply]
  rw [List.flatMap_def,List.map_ofFn]
  let f (t : Fin (r.size u j)) := (r.arg u j t).elim x (fun b=>h b.1 b.2)
  trans (List.ofFn (fun g : Fin (s.groups u j)=>wordList (fun d : Fin p=>f (Fin.cast (s.size_eq u j).symm
    (finProdFinEquiv (g,d)))))).flatten
  · apply congrArg List.flatten
    apply congrArg List.ofFn
    funext g
    simp only [Function.comp_apply]
    rw [Slice.eval_code]
    apply congrArg wordList
    funext d
    unfold f
    rw [←s.read]
    unfold decode
    cases eqn : (s.chunk u j g).get ((s.chunk u j g).index d) <;> rfl
  · exact word_chunks (s.size_eq u j) f

theorem site_read {K : Type} [Field K] {D : ℕ} {P : Type} {pins : P→ℕ} (N : Network D P pins)
    (scalar : U→List (List Bool)→K) (r : SiteBits (U:=U) N) (t : N.Tables K)
    (valid : ReadsBits N scalar r t) (s : ∀v,Shape p (r v)) (v : N.Site)
    (a : N.Assignment) (x : Ports pins) :
    ((s v).recipe hp).value (bundleScalar p scalar)
      (fun b=>wordList (fun d=>bitInput N a x v (b.atBit d)))=N.read t a x v :=
  ((s v).recipe_value hp scalar (bitInput N a x v)).trans (valid a x v)

end
end Hierarchy.DescentBundleHistory

end OAI
