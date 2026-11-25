import OAI.Hierarchy.TaggedPruning
import OAI.ThreeFlat.Routing.TypedWiring

namespace OAI
/-! # Contracting a pruned network with its binary selector hidden

The permutation is read from the exposed pins. A private fixed-length word
chooses an accepted selector for that permutation. Every retained selector
has exactly one word, including in fields of positive characteristic.
-/

noncomputable section
namespace Hierarchy.TaggedPrune

open ThreeFlat Routing
open Tagged Catalyst
open scoped Classical BigOperators

variable {F : Type*} [Field F] {h w k B : ℕ} {b : Fin k → ℕ}
variable {count : Equiv.Perm (Row h) → ℕ}

def selectorWord (enc : Encoding count B) (a : Index count) : Fin B → Bool := enc a.1 a.2

theorem encoded_count (enc : Encoding count B) (perm : Equiv.Perm (Row h)) :
    count perm ≤ 2^B := by
  simpa [Bits,Fintype.card_fun] using Fintype.card_le_of_embedding (enc perm)

def reads (enc : Encoding count B) (x : OpenPins h w b → Bool)
    (s : Fin B → Bool) (a : Index count) : Prop :=
  (a.1 : Row h → Row h) = tag (fun i => x (.inl i)) ∧ s = selectorWord enc a

theorem reads_unique (enc : Encoding count B) {x : OpenPins h w b → Bool} {s : Fin B → Bool}
    {a a' : Index count} (ha : reads enc x s a) (ha' : reads enc x s a') : a=a' := by
  obtain ⟨perm,i⟩ := a
  obtain ⟨perm',i'⟩ := a'
  have same : perm = perm' := Equiv.ext (congrFun (ha.1.trans ha'.1.symm))
  subst perm'
  have hi : i=i' := (enc perm).injective (ha.2.symm.trans ha'.2)
  cases hi
  rfl

def selected (keep : Index count → Prop) (enc : Encoding count B)
    (route : Index count → Table F h w b) (x : OpenPins h w b → Bool) (s : Fin B → Bool) : F :=
  if found : ∃ a : {a // keep a}, reads enc x s a.val then route found.choose.val x else 0

theorem selected_of_reads (keep : Index count → Prop) (enc : Encoding count B)
    (route : Index count → Table F h w b) (x : OpenPins h w b → Bool) (s : Fin B → Bool)
    (a : Index count) (retained : keep a) (ha : reads enc x s a) :
    selected keep enc route x s = route a x := by
  have hit : ∃ u : {u // keep u}, reads enc x s u.val := ⟨⟨a,retained⟩,ha⟩
  rw [selected,dite_eq_left hit,reads_unique enc hit.choose_spec ha]

theorem selected_of_no_read (keep : Index count → Prop) (enc : Encoding count B)
    (route : Index count → Table F h w b) (x : OpenPins h w b → Bool) (s : Fin B → Bool)
    (reject : ∀ a, keep a → ¬reads enc x s a) : selected keep enc route x s = 0 := by
  apply dite_eq_right
  rintro ⟨a,ha⟩
  exact reject a a.property ha

theorem selected_value (keep : Index count → Prop) (enc : Encoding count B)
    (route : Index count → Table F h w b) (x : OpenPins h w b → Bool) (s : Fin B → Bool) :
    selected keep enc route x s =
      ∑ a : {a // keep a}, if s=selectorWord enc a.val then exposed a.val.1 (route a.val) x else 0 := by
  by_cases hit : ∃ a : {a // keep a}, reads enc x s a.val
  · rw [selected,dite_eq_left hit,Finset.sum_eq_single hit.choose]
    · rw [ite_eq_left hit.choose_spec.2,exposed,ite_eq_left hit.choose_spec.1]
    · intro a _ ne
      by_cases hword : s=selectorWord enc a.val
      · rw [ite_eq_left hword,exposed,ite_eq_right]
        intro hp
        exact ne (Subtype.ext (reads_unique enc ⟨hp,hword⟩ hit.choose_spec))
      · rw [ite_eq_right hword]
    · simp
  · rw [selected,dite_eq_right hit]
    symm
    apply Finset.sum_eq_zero
    intro a _
    by_cases hword : s=selectorWord enc a.val
    · rw [ite_eq_left hword,exposed,ite_eq_right]
      intro hp
      exact hit ⟨a,hp,hword⟩
    · rw [ite_eq_right hword]

theorem contract_selectors (keep : Index count → Prop) (enc : Encoding count B)
    (route : Index count → Table F h w b) (x : OpenPins h w b → Bool) :
    (∑ s, selected keep enc route x s) = (∑ a : {a // keep a}, exposed a.val.1 (route a.val)) x := by
  simp_rw [selected_value keep enc route x]
  rw [Finset.sum_comm,Finset.sum_apply]
  simp

/-- Only the selector bits are shared and contracted. All physical data and
through-wire bits stay exposed at their original ports. -/
def hideSelector (b : Fin k → ℕ)
    (configured : BitNetwork F (Fintype.card (OpenPins h w b ⊕ Fin B))) :
    Approximation F k (pins h w) where
  width := b
  network := TypedWiring.glue (fun _ : Unit => configured)
    (fun _ (i : OpenPins h w b ⊕ Fin B) => i)

private theorem same_univ {I : Type*} (a b : Fintype I) : @Finset.univ I a=@Finset.univ I b :=
  congrArg (fun t=>@Finset.univ I t) (Subsingleton.elim a b)

theorem hideSelector_coeff (keep : Index count → Prop) (enc : Encoding count B)
    (route : Index count → Table F h w b)
    (configured : BitNetwork F (Fintype.card (OpenPins h w b ⊕ Fin B)))
    (value : ∀ x s, TypedWiring.value configured (Sum.elim x s) = selected keep enc route x s) :
    (hideSelector b configured).coeff =
      ∑ a : {a // keep a}, exposed a.val.1 (route a.val) := by
  change (fun x : OpenPins h w b→Bool=>TypedWiring.value (TypedWiring.glue
    (fun _ : Unit => configured) (fun _ (i : OpenPins h w b ⊕ Fin B) => i)) x)=_
  funext x
  calc
    _ = ∑s : Fin B→Bool,TypedWiring.value configured (Sum.elim x s) := by
      refine (TypedWiring.glue_value (P:=OpenPins h w b) (H:=Fin B)
        (port:=fun _ : Unit=>OpenPins h w b ⊕ Fin B) (fun _=>configured) (fun _ i=>i) x).trans ?_
      simp only [Fintype.prod_unique]
      apply Finset.sum_congr (same_univ _ _)
      intro word _
      rfl
    _ = _ := by simpa only [value] using contract_selectors keep enc route x

omit [Field F] in
@[simp] theorem hideSelector_size (b : Fin k → ℕ)
    (configured : BitNetwork F (Fintype.card (OpenPins h w b ⊕ Fin B))) :
    (hideSelector b configured).size =
      configured.cells + (B + configured.internal) + Fintype.card (OpenPins h w b) := by
  change (TypedWiring.glue (fun _ : Unit=>configured) (fun _ (i : OpenPins h w b ⊕ Fin B)=>i)).cells+
    (TypedWiring.glue (fun _ : Unit=>configured) (fun _ (i : OpenPins h w b ⊕ Fin B)=>i)).internal+
      Fintype.card (OpenPins h w b)=_
  simp only [TypedWiring.glue_cells,TypedWiring.glue_internal,Fintype.sum_unique,Fintype.card_fin]

/-- The selector input of a relative implementation can be contracted without
replicating the implementation across words or permutation tags. -/
theorem hideSelector_gap {M : ℕ} (hM : 0<M) (hw : 0<w) (hk : 0<k)
    (D : Layout h w b) (enc : Encoding count B)
    (route : Index count → Table F h w b) (links : Index count → Links D M)
    (routing : ∀ perm, (∑ i : Fin (count perm), route ⟨perm,i⟩) = perTag perm)
    (tables : ∀ a, ((CorrectionProducts.raw (route a)).group D.port).Restricts
      (LinearAlgebra.SpectralBooks.ChordGraph.raw F
        (AdaptiveProbe.installedWidths (links a).ends (links a).bits)))
    (configured : BitNetwork F (Fintype.card (OpenPins h w b ⊕ Fin B)))
    (value : ∀ x s, TypedWiring.value configured (Sum.elim x s) =
      selected (fun a => (links a).Keep (2^h)) enc route x s) :
    (hideSelector b configured).Gap (coeff F h w)
      ((2:ℝ)^h*w/M - 2*(k:ℝ)*((h:ℝ)*2^h+B)) :=
  pruning_gap hM hw hk _ D (encoded_count enc) route links routing tables
    (hideSelector_coeff _ enc route configured value)

/-- A finite table realizes the selector semantics on every format. The
efficient physical shorter-call construction can supply its own implementation
to `hideSelector_gap` and use `hideSelector_size` for the cost. -/
def selectorTable (keep : Index count → Prop) (enc : Encoding count B)
    (route : Index count → Table F h w b) :
    BitNetwork F (Fintype.card (OpenPins h w b ⊕ Fin B)) :=
  TypedWiring.localTable (fun z => selected keep enc route (z ∘ Sum.inl) (z ∘ Sum.inr))

theorem selectorTable_value (keep : Index count → Prop) (enc : Encoding count B)
    (route : Index count → Table F h w b) (x : OpenPins h w b → Bool) (s : Fin B → Bool) :
    TypedWiring.value (selectorTable keep enc route) (Sum.elim x s) =
      selected keep enc route x s := by
  exact TypedWiring.localTable_value _ _

/-- Original local restrictions and matching identities already give an
actual finite approximation on the original physical catalyst. Efficient
implementations of the configured table inherit the stronger size identity. -/
theorem exists_pruned {M : ℕ} (hM : 0<M) (hw : 0<w) (hk : 0<k)
    (D : Layout h w b) (enc : Encoding count B)
    (route : Index count → (RoutingPin h w b → Bool) → F) (links : Index count → Links D M)
    (routing : ∀ perm, (∑ i : Fin (count perm), route ⟨perm,i⟩) = routingMatch perm)
    (tables : ∀ a, ((CorrectionProducts.raw (route a)).group (D.port ∘ routingPort)).Restricts
      (LinearAlgebra.SpectralBooks.ChordGraph.raw F
        (AdaptiveProbe.installedWidths (links a).ends (links a).bits))) :
    ∃ X : Approximation F k (pins h w), X.width = b ∧
      X.Gap (coeff F h w) ((2:ℝ)^h*w/M - 2*(k:ℝ)*((h:ℝ)*2^h+B)) := by
  let f (a : Index count) := addTagPorts (route a)
  let keep (a : Index count) := (links a).Keep (2^h)
  let net := selectorTable keep enc f
  exact ⟨hideSelector b net,rfl,hideSelector_gap hM hw hk D enc f links
    (addTagPorts_sum route routing) (fun a => addTagPorts_restricts D.port _ (tables a))
    net (selectorTable_value keep enc f)⟩


end Hierarchy.TaggedPrune

end
end OAI
