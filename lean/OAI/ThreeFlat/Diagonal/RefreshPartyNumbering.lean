import OAI.ThreeFlat.Diagonal.RefreshPartyMeaning
import OAI.ThreeFlat.Diagonal.CompressorHalfPorts

namespace OAI
/-! # The refresh lookup uses exactly the half ordinals in retained node records -/

namespace ThreeFlat.Diagonal.RefreshParty

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks RefreshTies Expander CompressorRefresh
open CompressorPacking.Native.ShrinkStage.Halves
open scoped Classical BigOperators
noncomputable section

variable {V C L : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] {m h : ℕ}
    (G : LiftedSlots V m (C×L)) (c : Fin m → Fin m → ℕ) (sym : ∀ i j,c i j=c j i)
    (rows : ∀ i,∑ j,c i j=h) (zero : ∀ i,c i i=0) (hm : 2 ≤ m) (pad : ℕ)

/-- Numerical half ordinal on any directed regular graph. -/
def physicalHalf {B L : Type} [AddCommGroup L] {d : ℕ} (H : LiftedSlots B d L)
    (e : (B × Fin d) × L) (side : Bool) : ℕ :=
  if side then d+(H.actualTarget e).1.2.val else e.1.2.val

omit [Fintype V] [AddCommGroup C] [Fintype L] in
/-- The raw kernel's external and internal edges have the same order
as the graph matrix published by the compressor. -/
theorem freshHalf_physical (u : V×L) (p : Fin m)
    (q : (rawGraph (externalSite G) (fun _=>ports c)).Port (u,p)) :
    freshHalf (pad:=pad) (externalSite G) c sym rows u p q=
      physicalHalf (outputGraph G c sym rows zero hm pad) (actualHalf G c sym rows zero hm pad q).1.1 q.1.2 := by
  obtain ⟨⟨e,side⟩,endpoint⟩ := q
  rcases e with (⟨⟨v,l⟩,j⟩ | ⟨⟨v,l⟩,e⟩) <;> cases side
  · rfl
  · simp only [freshHalf,physicalHalf,actualHalf,ite_true,refreshSlots,Equiv.trans_apply,
      Equiv.sumCongr_apply,Sum.map_inl,outputGraph,graph,union_actual_left,extSlots]
    rfl
  · change 1+0+(numbering c rows e).2.val=_
    rfl
  · simp only [freshHalf,physicalHalf,actualHalf,ite_true,refreshSlots,Equiv.trans_apply,
      Equiv.sumCongr_apply,Sum.map_inl,Sum.map_inr,outputGraph,graph,union_actual_left,
      RefreshTies.union_actual_right,sparseSlots,numbering]
    change 1+(1+h+pad)+(DoublePorts.arcNumber (Equiv.refl _) c rows (DoublePorts.reverseArc c sym e)).2.val =
      (1+h+pad)+(1+((DoublePorts.ofMatrix (Equiv.refl _) c sym rows zero).target
        (DoublePorts.arcNumber (Equiv.refl _) c rows e)).2.val)
    rw [DoublePorts.ofMatrix_target]
    omega

theorem portOrder_physical {B S : Type} {t d : ℕ} (G : LiftedSlots B d (BitWord t))
    (chart : B × BitWord t ≃ S) (site : B × BitWord t) (q : (chartGraph G chart).Port (chart site)) :
    ((portOrder G chart site).symm q).val=physicalHalf G q.1.1 q.1.2 := by
  obtain ⟨⟨e,b⟩,hp⟩ := q
  cases b <;> rfl

end
end ThreeFlat.Diagonal.RefreshParty

namespace ThreeFlat.Diagonal.RefreshTies

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks Expander RefreshParty
open CompressorPacking.Native.ShrinkStage.Halves
open scoped BigOperators

/-- The numerical sparse half exposed to the selected party has exactly its
histogram payload width, also when the party reads the head of a directed arc. -/
theorem sparse_half_width {V C : Type} [Fintype V] [AddCommGroup C] {l m h : ℕ}
    (G : LiftedSlots V m (C × BitWord l)) (c : Fin m → Fin m → ℕ)
    (sym : ∀ a b,c a b=c b a) (rows : ∀ a,∑ b,c a b=h) (zero : ∀ a,c a a=0)
    (hm : 2 ≤ m) (pad : ℕ) (w : Address (V × BitWord l) m → ℕ)
    (sw : V × BitWord l → Arc c → ℕ) (z : V × BitWord l) (p : Fin m)
    (edge : (ports c).Port p) (j : Fin (2*(1+h+pad)))
    (idx : j.val=1+(if edge.1.2 then 1+h+pad else 0)+
      (numbering c rows (if edge.1.2 then DoublePorts.reverseArc c sym edge.1.1 else edge.1.1)).2.val) :
    freshWidth c rows (termWidth c w sw) pad
      (sourceHalf (outputGraph G c sym rows zero hm pad) ((z.1,p),z.2) j)=sw z edge.1.1 := by
  let H:=outputGraph G c sym rows zero hm pad
  let chart : (V × Fin m) × BitWord l ≃ (V × BitWord l) × Fin m :=
    ⟨fun x=>((x.1.1,x.2),x.1.2),fun x=>((x.1.1,x.2),x.1.2),fun _=>rfl,fun _=>rfl⟩
  let site:=((z.1,p),z.2)
  let raw : (rawGraph (externalSite G) (fun _=>ports c)).Port (z,p) :=
    ⟨(.inr ⟨z,edge.1.1⟩,edge.1.2),by
      rcases edge with ⟨⟨a,b⟩,hb⟩
      cases b <;> exact congrArg (Prod.mk z) hb⟩
  let actual : (chartGraph H chart).Port (chart site):=actualHalf G c sym rows zero hm pad raw
  have which : (portOrder H chart site).symm actual=j := by
    apply Fin.ext
    exact (portOrder_physical H chart site actual).trans
      ((freshHalf_physical G c sym rows zero hm pad z p raw).symm.trans idx.symm)
  have edgeEq := congrArg Prod.fst (portOrder_value H chart site j)
  rw [←which,Equiv.apply_symm_apply] at edgeEq
  change freshWidth c rows (termWidth c w sw) pad (sourceHalf H site j)=_
  rw [which] at edgeEq
  change actual.1.1 = sourceHalf H site j at edgeEq
  rw [←edgeEq]
  change Sum.elim (termWidth c w sw) (fun _=>0)
    ((refreshSlots (numbering c rows) pad).symm (refreshSlots (numbering c rows) pad
      (.inl (.inr ⟨z,edge.1.1⟩))))=_
  rw [Equiv.symm_apply_apply]
  rfl

end ThreeFlat.Diagonal.RefreshTies

end OAI
