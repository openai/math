import OAI.LinearAlgebra.SpectralBooks.PortGraph.PlanarPatchRecordChecks
import OAI.LinearAlgebra.SpectralBooks.UniformDecorations.UniformDecorations

/-! # Equality of canonically sorted patch records -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

noncomputable section
open scoped Classical

namespace PortGraph.PatchRecord

variable {A : Type*} {K : ℕ}

/-- Sorted slots remove the freedom to rename vertices. The recorded type,
label and actual mate at each numbered port therefore determine the entire
record. The argument also applies when a compared pair of records has
a priori different dependent dart types. -/
theorem eq_of_congr (R S : PatchRecord K A) (v : R.shape.Vertex ≃ S.shape.Vertex)
    (hv : StrictMono v) (t : ∀ i, R.shape.typeAt i = S.shape.typeAt (v i))
    (l : ∀ i, R.label i = S.label (v i)) (d : R.shape.Dart → S.shape.Dart)
    (owner : ∀ p, (d p).1 = v p.1) (number : ∀ p, (d p).2.val = p.2.val)
    (opposite : ∀ p, d (R.shape.opposite p) = S.shape.opposite (d p)) : R = S := by
  rcases R with ⟨⟨n,hn,θ,o,_,_⟩,z⟩
  rcases S with ⟨⟨m,hm,θ',o',_,_⟩,z'⟩
  have hnm : n = m := Fin.ext (by simpa only [PatchShape.Vertex, Fintype.card_fin] using Fintype.card_congr v)
  subst m
  have hi : ∀ i, v i = i := congrFun hv.eq_id
  have ht : θ = θ' := funext fun i => (t i).trans (congrArg θ' (hi i))
  subst θ'
  have hd (p : PatchDart θ) : d p = p := by
    obtain ⟨i,j⟩ := p
    have h₁ := (owner ⟨i,j⟩).trans (hi i)
    have h₂ := number ⟨i,j⟩
    generalize hh : d ⟨i,j⟩ = q at h₁ h₂ ⊢
    obtain ⟨i',j'⟩ := q
    change i' = i at h₁
    subst i'
    exact congrArg (Sigma.mk i) (Fin.ext h₂)
  have hO : o = o' := Equiv.ext fun p => (hd (o p)).symm.trans ((opposite p).trans (congrArg o' (hd p)))
  have hZ : z = z' := funext fun i => (l i).trans (congrArg z' (hi i))
  subst o'
  subst z'
  rfl

variable {V E W D : Type*} [Fintype V] [Fintype E] [DecidableEq V]
  [Fintype W] [Fintype D] [DecidableEq W]
  {M : RootedMap V E} {H : RootedMap W D}

/-- The incident vertex and its local number determine an oriented dart,
including in the presence of loops. -/
theorem dart_ext (M : RootedMap V E) (p q : E × Bool)
    (hv : M.graph.vertex p.1 p.2 = M.graph.vertex q.1 q.2)
    (hs : M.portNumber p.1 p.2 = M.portNumber q.1 q.2) : p = q :=
  port_ext ⟨p,rfl⟩ ⟨q,rfl⟩ hv hs
where
  port_ext {v w : V} (p : M.graph.Port v) (q : M.graph.Port w) (hv : v = w)
      (hs : (M.num _ p).val = (M.num _ q).val) : p.val = q.val := by
    subst w
    exact congrArg Subtype.val ((M.num _).injective (Fin.ext hs))

/-- Transport a record to another named presentation of the same labelled
patch. The two canonically sorted records agree literally. -/
theorem extract_iso (f : M.Iso H) {P : Finset V} {Q : Finset W}
    (hPQ : ∀ x, x ∈ P ↔ f.vertex x ∈ Q) (name : V ↪ ℕ) (name' : W ↪ ℕ)
    (hnm : ∀ x, name x = name' (f.vertex x)) (z : V → A) (z' : W → A)
    (hl : ∀ x, z x = z' (f.vertex x))
    (hp : P.Nonempty) (hpK : P.card ≤ K) (hq : Q.Nonempty) (hqK : Q.card ≤ K) :
    extract M z P name hp hpK = extract H z' Q name' hq hqK := by
  let s := slots P name
  let t := slots Q name'
  let v := (slotOrder P name).trans ((f.vertex.subtypeEquiv hPQ).trans (slotOrder Q name').symm)
  have ho (i) : t (v i) = f.vertex (s i) :=
    congrArg Subtype.val ((slotOrder Q name').apply_symm_apply _)
  have hm : StrictMono v := by
    intro i j hij
    apply (slotOrder_strict Q name').lt_iff_lt.mp
    change name' (t (v i)) < name' (t (v j))
    rw [ho,ho,← hnm,← hnm]
    exact slotOrder_strict P name hij
  have ht (i) : M.typeAt (s i) = H.typeAt (t (v i)) := (UniformDecorations.typeAt_iso f _).trans (congrArg H.typeAt (ho i).symm)
  let d : PatchDart (fun i => M.typeAt (s i)) ≃ PatchDart (fun i => H.typeAt (t i)) :=
    Equiv.sigmaCongr v (fun i => finCongr (congrArg (fun a : MapType => a.degree.val) (ht i)))
  let a := f.edge.prodCongr (Equiv.refl Bool)
  have ha (p) : actual H t (d p) = a (actual M s p) := by
    apply dart_ext H
    · exact (actual_owner H t (d p)).trans ((ho p.1).trans
        ((congrArg f.vertex (actual_owner M s p).symm).trans (f.incidence _ _)))
    · have h₁ := actual_slot H t (d p)
      have h₂ := actual_slot M s p
      exact h₁.trans (h₂.symm.trans (f.number _ _))
  have hcross (p) : a (cross p) = cross (a p) := rfl
  apply eq_of_congr _ _ v hm ht (fun i => (hl _).trans (congrArg z' (ho i).symm)) d (fun _ => rfl) (fun _ => rfl)
  intro p
  change PatchDart (fun i => M.typeAt (s i)) at p
  change d (partner M s p) = partner H t (d p)
  by_cases hp : partner M s p = p
  · rw [hp]
    apply Eq.symm
    apply (partner_fixed_iff H t _).mpr
    rintro ⟨q,hq⟩
    apply (partner_fixed_iff M s _).mp hp
    refine ⟨d.symm q, a.injective ?_⟩
    rw [← ha, d.apply_symm_apply, hcross, ← ha, hq]
  · apply Eq.symm
    apply partner_of_internal
    rw [ha, actual_partner M s hp, hcross, ← ha]

/-- Reading a labelled presentation of the internal pairs and stubs gives
the original record. The hypotheses refer to actual darts in the ambient map.
-/
theorem extract_presented (M : RootedMap V E) (z : V → A) (R : PatchRecord K A)
    (P : Finset V) (name : V ↪ ℕ) (hn : P.Nonempty) (hk : P.card ≤ K)
    (x : R.shape.Vertex ≃ ↥P) (sorted : StrictMono (fun i => name (x i).val))
    (types : ∀ i, M.typeAt (x i).val = R.shape.typeAt i)
    (labels : ∀ i, z (x i).val = R.label i) (port : R.shape.Dart → E × Bool)
    (owner : ∀ p, M.graph.vertex (port p).1 (port p).2 = (x p.1).val)
    (number : ∀ p, M.portNumber (port p).1 (port p).2 = p.2.val)
    (stub : ∀ p, R.shape.opposite p = p →
      M.graph.vertex (cross (port p)).1 (cross (port p)).2 ∉ P)
    (inside : ∀ p, R.shape.opposite p ≠ p → port (R.shape.opposite p) = cross (port p)) :
    extract M z P name hn hk = R := by
  let s := slots P name
  let v := x.trans (slotOrder P name).symm
  have ho (i) : s (v i) = (x i).val := congrArg Subtype.val ((slotOrder P name).apply_symm_apply _)
  have hm : StrictMono v := by
    intro i j hij
    apply (slotOrder_strict P name).lt_iff_lt.mp
    change name (s (v i)) < name (s (v j))
    rw [ho,ho]
    exact sorted hij
  have ht (i) : R.shape.typeAt i = M.typeAt (s (v i)) := (types i).symm.trans (congrArg M.typeAt (ho i).symm)
  let d : R.shape.Dart ≃ PatchDart (fun i => M.typeAt (s i)) :=
    Equiv.sigmaCongr v (fun i => finCongr (congrArg (fun a : MapType => a.degree.val) (ht i)))
  have ha (p) : actual M s (d p) = port p := dart_ext M _ _
    ((actual_owner M s (d p)).trans ((ho p.1).trans (owner p).symm))
    ((actual_slot M s (d p)).trans (number p).symm)
  symm
  apply eq_of_congr _ _ v hm ht (fun i => (labels i).symm.trans (congrArg z (ho i).symm))
    d (fun _ => rfl) (fun _ => rfl)
  intro p
  change d (R.shape.opposite p) = partner M s (d p)
  by_cases hp : R.shape.opposite p = p
  · rw [hp]
    apply Eq.symm
    apply (partner_fixed_iff M s _).mpr
    intro h
    apply stub p hp
    rw [← ha p]
    exact (mem_slots_iff P name _).mp ((actual_range M s _).mp h)
  · apply Eq.symm
    exact partner_of_internal M s ((ha _).trans ((inside _ hp).trans (congrArg cross (ha p).symm)))

end PortGraph.PatchRecord

end

end SpectralBooks
end LinearAlgebra
end OAI
