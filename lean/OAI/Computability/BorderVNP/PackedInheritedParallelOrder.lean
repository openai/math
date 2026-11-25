import OAI.Computability.BorderVNP.PackedBankInheritedValue
import OAI.Computability.BorderVNP.ShortenPublicParallelNames

/-! # Site-local incidence order in a parallel pack

A copy receives one rectangular block of public cable rows and one block of
external port rows. Its site's internal cables, source ends, destination ends
and exterior ports retain their individual order within each of the four
blocks. Thus the original compressed input addresses can be reused.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Parallel

open Crossing Shortening PublicParallel CellAddresses
open private endRow from OAI.Computability.BorderVNP.PackedCellAddresses
open scoped Classical

variable {copies D M np : ℕ} {P : Type} {bits : P → ℕ} (N : Fin copies → Network D P bits)
    (rows : ∀ i, (N i).Edge ↪ Fin M) (portID : P ↪ Fin np) (i : Fin copies) (v : (N i).Site)

/-- Row-major public port slots in a disjoint union, in child then port order. -/
def portRows (copies : ℕ) (p : P ↪ Fin np) : Fin copies × P ↪ Fin (copies*np) :=
  ((Function.Embedding.refl (Fin copies)).prodMap p).trans finProdFinEquiv.toEmbedding

private abbrev union := Network.parallel N

private noncomputable def fiber {I : Type} {X : I → Type*} (i : I)
    (localPred : X i → Prop) (globalPred : (Σ j,X j) → Prop)
    (iff' : ∀ x, localPred x ↔ globalPred ⟨i,x⟩)
    (tag : ∀ z, globalPred z → z.1 = i) :
    {x // localPred x} ≃ {z // globalPred z} :=
  Equiv.ofBijective (fun x => ⟨⟨i,x.val⟩,(iff' x.val).1 x.property⟩) ⟨by
    intro x y eq
    exact Subtype.ext (Sigma.mk.inj_iff.mp (congrArg Subtype.val eq) |>.2 |> eq_of_heq), by
    rintro ⟨⟨j,x⟩,hx⟩
    obtain rfl := tag ⟨j,x⟩ hx
    exact ⟨⟨x,(iff' x).2 hx⟩,rfl⟩⟩

/-- Each incident cable at the global copy-site is a cable of that copy. -/
noncomputable def incident : Incident (N i) v ≃ Incident (union N) ⟨i,v⟩ :=
  fiber (X := fun j => (N j).Edge) i (fun e => (N i).src e = v ∨ (N i).dst e = v)
    (fun z => (union N).src z = ⟨i,v⟩ ∨ (union N).dst z = ⟨i,v⟩)
    (fun e => by simp only [union,Network.parallel,Sigma.mk.inj_iff,heq_eq_eq,true_and])
    (fun _ h => h.elim (congrArg Sigma.fst) (congrArg Sigma.fst))

private noncomputable def loops : (N i).InsideEdge id v ≃ (union N).InsideEdge id ⟨i,v⟩ :=
  fiber (X := fun j => (N j).Edge) i (fun e => (N i).src e = v ∧ (N i).dst e = v)
    (fun z => (union N).src z = ⟨i,v⟩ ∧ (union N).dst z = ⟨i,v⟩)
    (fun e => by simp only [union,Network.parallel,Sigma.mk.inj_iff,heq_eq_eq,true_and])
    (fun _ h => congrArg Sigma.fst h.1)

private def boundaryIncident {Q : Type} {widths : Q → ℕ} (L : Network D Q widths) (u : L.Site) :
    Boundary L id u ≃ {z : Incident L u // L.src z.val ≠ L.dst z.val} where
  toFun e := ⟨⟨e.val.val,e.property⟩,e.val.property⟩
  invFun z := ⟨⟨z.val.val,z.property⟩,z.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

private noncomputable def boundary : Boundary (N i) id v ≃ Boundary (union N) id ⟨i,v⟩ :=
  (boundaryIncident (N i) v).trans (((incident N i v).subtypeEquiv (fun z => by
    change ((N i).src z.val ≠ (N i).dst z.val) ↔ (Sigma.mk i ((N i).src z.val) : Σ j,(N j).Site) ≠ ⟨i,(N i).dst z.val⟩
    exact ⟨fun h he => h (eq_of_heq (Sigma.mk.inj_iff.mp he).2), fun h he => h (congrArg (Sigma.mk i) he)⟩)).trans (boundaryIncident (union N) ⟨i,v⟩).symm)

/-- Every global exterior port at the copy-site is one of its original exterior ports. -/
noncomputable def attached : Attached (N i) v ≃ Attached (union N) ⟨i,v⟩ :=
  Equiv.ofBijective (fun u => ⟨(i,u.val),congrArg (Sigma.mk i) u.property⟩) ⟨by
    intro x y h
    exact Subtype.ext (congrArg Prod.snd (congrArg Subtype.val h)), by
    rintro ⟨⟨j,p⟩,hp⟩
    obtain rfl : j=i := congrArg Sigma.fst hp
    exact ⟨⟨p,by simpa [union,Network.parallel] using hp⟩,rfl⟩⟩

private noncomputable def supplied : Supplied (N i) id v ≃ Supplied (union N) id ⟨i,v⟩ :=
  Equiv.sumCongr (boundary N i v) (attached N i v)

private theorem supplyWidth (u : Supplied (N i) id v) :
    suppliedWidth (union N) id ⟨i,v⟩ (supplied N i v u) = suppliedWidth (N i) id v u := by cases u <;> rfl

private theorem guessed : guessedSize (union N) id ⟨i,v⟩ = guessedSize (N i) id v := by
  unfold guessedSize
  rw [← (loops N i v).sum_comp]
  rfl

variable [Fintype P]

/-- Parallel composition retains the child's full virtual-site bit capacity. -/
theorem incoming_eq : incoming (Network.parallel N) ⟨i,v⟩ = incoming (N i) v := by
  unfold incoming
  rw [guessed N i v]
  congr 1
  unfold suppliedSize
  rw [← (supplied N i v).sum_comp]
  exact Finset.sum_congr rfl (fun z _ => supplyWidth N i v z)

private theorem flat_lt {m : ℕ} (a b : Fin m) : flat i a < flat i b ↔ a < b := by
  simp only [Fin.lt_def,flat_val,Nat.add_lt_add_iff_right]

private theorem sum_lt {a b c d : ℕ} (f : Fin a → Fin c) (g : Fin b → Fin d)
    (hf : ∀ x y, f x < f y ↔ x < y) (hg : ∀ x y, g x < g y ↔ x < y)
    (x y : Fin a ⊕ Fin b) :
    finSumFinEquiv (Sum.map f g x) < finSumFinEquiv (Sum.map f g y) ↔ finSumFinEquiv x < finSumFinEquiv y := by
  rcases x with x|x <;> rcases y with y|y
  · exact hf x y
  · change (f x).val < c+(g y).val ↔ x.val < a+y.val
    exact iff_of_true ((f x).isLt.trans_le (Nat.le_add_right _ _)) (x.isLt.trans_le (Nat.le_add_right _ _))
  · change c+(g x).val < (f y).val ↔ a+x.val < y.val
    exact iff_of_false (not_lt_of_ge ((f y).isLt.le.trans (Nat.le_add_right _ _))) (not_lt_of_ge (y.isLt.le.trans (Nat.le_add_right _ _)))
  · change c+(g x).val < c+(g y).val ↔ a+x.val < a+y.val
    rw [Nat.add_lt_add_iff_left,Nat.add_lt_add_iff_left]
    exact hg x y

private def endpointLift (i : Fin copies) : Fin (M+M) → Fin (copies*M+copies*M) :=
  fun r => finSumFinEquiv (Sum.map (flat i) (flat i) (finSumFinEquiv.symm r))

private theorem endpoint_lt (x y : Fin (M+M)) :
    endpointLift i x < endpointLift i y ↔ x < y := by
  obtain ⟨x,rfl⟩ := finSumFinEquiv.surjective x
  obtain ⟨y,rfl⟩ := finSumFinEquiv.surjective y
  simp only [endpointLift,Equiv.symm_apply_apply]
  exact sum_lt _ _ (flat_lt i) (flat_lt i) x y

private noncomputable def key {Q : Type} {widths : Q → ℕ} (L : Network D Q widths)
    (c : L.Site) (edge : L.Edge ↪ Fin M) (port : Q ↪ Fin np) : Supplied L id c → Fin (M+M) ⊕ Fin np :=
  Sum.elim (fun e => .inl (finSumFinEquiv (endRow L id c edge e))) (fun p => .inr (port p.val))

omit [Fintype P] in
private theorem key_eq (u : Supplied (N i) id v) :
    key (union N) ⟨i,v⟩ (parallelName rows) (portRows copies portID) (supplied N i v u) =
      Sum.map (endpointLift i) (flat i) (key (N i) v (rows i) portID u) := by
  rcases u with e|p
  · have hrow : endRow (union N) id ⟨i,v⟩ (parallelName rows) (boundary N i v e) =
        Sum.map (flat i) (flat i) (endRow (N i) id v (rows i) e) := by
      by_cases hs : (N i).src e.val.val = v
      · have hg : (union N).src (boundary N i v e).val.val = ⟨i,v⟩ := congrArg (Sigma.mk i) hs
        change (if (union N).src (boundary N i v e).val.val = ⟨i,v⟩ then Sum.inl _ else Sum.inr _) =
          Sum.map _ _ (if (N i).src e.val.val = v then Sum.inl _ else Sum.inr _)
        rw [ite_eq_left hg,ite_eq_left hs]
        rfl
      · have hg : (union N).src (boundary N i v e).val.val ≠ ⟨i,v⟩ :=
          fun h => hs (Sigma.mk.inj_iff.mp h |>.2 |> eq_of_heq)
        simp only [endRow,Function.Embedding.coeFn_mk,id_eq,hg,hs,ite_false,Sum.map_inr]
        rfl
    change Sum.inl (finSumFinEquiv (endRow _ _ _ _ _)) = Sum.inl (endpointLift i (finSumFinEquiv _))
    rw [hrow]
    simp only [endpointLift,Equiv.symm_apply_apply]
  · rfl

omit [Fintype P] in
private theorem supply_lt (x y : Supplied (N i) id v) :
    suppliedRow (union N) id ⟨i,v⟩ (parallelName rows) (portRows copies portID) (supplied N i v x) <
      suppliedRow (union N) id ⟨i,v⟩ (parallelName rows) (portRows copies portID) (supplied N i v y) ↔
    suppliedRow (N i) id v (rows i) portID x < suppliedRow (N i) id v (rows i) portID y := by
  have keyVal {Q : Type} {widths : Q → ℕ} {M' n' : ℕ} (L : Network D Q widths) (c : L.Site)
      (r : L.Edge ↪ Fin M') (p : Q ↪ Fin n') (z : Supplied L id c) :
      suppliedRow L id c r p z = (finSumFinEquiv (key L c r p z)).val := by cases z <;> rfl
  let l := key (N i) v (rows i) portID
  have hg (t : Supplied (N i) id v) :
      suppliedRow (union N) id ⟨i,v⟩ (parallelName rows) (portRows copies portID) (supplied N i v t) =
      (finSumFinEquiv (Sum.map (endpointLift i) (flat i) (l t))).val :=
    (keyVal (union N) _ _ _ (supplied N i v t)).trans (congrArg (fun r => (finSumFinEquiv r).val) (key_eq N rows portID i v t))
  exact Iff.trans (Iff.of_eq (congrArg₂ (fun a b : ℕ => a < b) (hg x) (hg y))) ((sum_lt _ _ (endpoint_lt i) (flat_lt i) (l x) (l y)).trans
    (Iff.of_eq (congrArg₂ (fun a b : ℕ => a < b) (keyVal (N i) v (rows i) portID x).symm (keyVal (N i) v (rows i) portID y).symm)))

private theorem start_eq {A B : Type*} [Fintype A] [Fintype B] (e : A ≃ B) (a : A ↪ ℕ) (b : B ↪ ℕ)
    (wa : A → ℕ) (wb : B → ℕ) (lt : ∀ x y, b (e x) < b (e y) ↔ a x < a y)
    (width : ∀ x, wb (e x) = wa x) (x : A) :
    CellSlabs.start b wb (e x) = CellSlabs.start a wa x := by
  unfold CellSlabs.start
  rw [←e.sum_comp]
  exact Finset.sum_congr rfl (fun y _ => by simp only [lt,width])

private theorem supply_start (u : Supplied (N i) id v) :
    CellSlabs.start (suppliedRow (union N) id ⟨i,v⟩ (parallelName rows) (portRows copies portID))
      (suppliedWidth (union N) id ⟨i,v⟩) (supplied N i v u) =
    CellSlabs.start (suppliedRow (N i) id v (rows i) portID) (suppliedWidth (N i) id v) u :=
  start_eq (supplied N i v) _ _ _ _ (supply_lt N rows portID i v) (supplyWidth N i v) u

omit [Fintype P] in
private theorem ext_base :
    externalBase (union N) id ⟨i,v⟩ (fun _ => 0) = externalBase (N i) id v (fun _ => 0) := by
  simp only [externalBase,siteSize,Finset.sum_const_zero,Nat.add_zero,guessed N i v]

/-- The full local address of a shared loop or supplied endpoint in the parallel pack. -/
theorem wireStart_eq (z : Incident (N i) v) :
    wireStart (Network.parallel N) (parallelName rows) (portRows copies portID) ⟨i,v⟩ (incident N i v z) =
    wireStart (N i) (rows i) portID v z := by
  unfold wireStart wireBase
  by_cases h : (N i).src z.val = (N i).dst z.val
  · have h' : id ((union N).src (incident N i v z).val) = id ((union N).dst (incident N i v z).val) :=
      congrArg (Sigma.mk i) h
    rw [dite_eq_left h',dite_eq_left (show id ((N i).src z.val) = id ((N i).dst z.val) from h)]
    have both : (N i).src z.val = v ∧ (N i).dst z.val = v := by rcases z.property with hv|hv <;> simp_all
    exact start_eq (loops N i v) _ _ _ _ (fun x y => flat_lt i (rows i x.val) (rows i y.val))
      (fun _ => rfl) ⟨z.val,both⟩
  · have h' : id ((union N).src (incident N i v z).val) ≠ id ((union N).dst (incident N i v z).val) :=
      fun eqn => h (Sigma.mk.inj_iff.mp eqn |>.2 |> eq_of_heq)
    rw [dite_eq_right h',dite_eq_right (show id ((N i).src z.val) ≠ id ((N i).dst z.val) from h),ext_base N i v]
    exact congrArg (_ + ·) (supply_start N rows portID i v (.inl ⟨⟨z.val,h⟩,z.property⟩))

/-- The full local address of a supplied argument port in the parallel pack. -/
theorem portStart_eq (u : Attached (N i) v) :
    portStart (Network.parallel N) (parallelName rows) (portRows copies portID) ⟨i,v⟩ (attached N i v u) =
    portStart (N i) (rows i) portID v u := by
  unfold portStart portBase
  rw [ext_base N i v]
  exact congrArg (_ + ·) (supply_start N rows portID i v (.inr u))

end Packing.Inherited.Parallel

end BorderVNP
end Computability
end OAI
