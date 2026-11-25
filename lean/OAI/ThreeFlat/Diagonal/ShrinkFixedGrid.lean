import OAI.ThreeFlat.Diagonal.ShrinkPortKernel
import OAI.ThreeFlat.Diagonal.FixedMotifTile

namespace OAI
/-! # The fixed finite selection table for the six-party shrinking step -/

namespace ThreeFlat.Diagonal.ShrinkMotif

open LinearAlgebra.SpectralBooks Computability.VPVNP.MotifGrid Computability.VPVNP.MotifWidths Computability.VPVNP.MotifBase
open scoped Classical BigOperators

/-- Numerical tile maps and their binary selector codes, ready for the
histogram-indexed kernel. All constants precede the incoming demand. -/
theorem exists_shrink_tiles (F : Type) [Field F] {R δ : ℝ} (hR : √(31/16 : ℝ)<R) (hδ : 0<δ) :
    ∃ (G : StrictGrids demandMass supplyMass (31/16) R) (t h : ℕ), 0<t ∧ 0<h ∧
      ∀ z : G.demands, ∃ T : FixedMotifTile ⟨demandSrc,demandDst⟩ ⟨supply.src,supply.dst⟩
        (fun e => h*G.demandWidths t z e) F,
        (T.bits : ℝ)/(h*(t*G.denominator):ℕ) < δ ∧
        ∀ s, widthNorm supplyMass (fun e => (T.output s e : ℝ)) ≤ (h*(t*G.denominator):ℕ)*R := by
  obtain ⟨G,t,h,K,ht,hh,hK,frac,base,rad⟩ := exists_maps F hR hδ
  refine ⟨G,t,h,ht,hh,?_⟩
  intro z
  let D : PortGraph (Fin 6) (Fin 2) := ⟨demandSrc,demandDst⟩
  let P : PortGraph (Fin 6) (Fin 8) := ⟨supply.src,supply.dst⟩
  let Q := Fin K × (Fin h → G.supplies)
  let s := selectorBits K G.supplies.card h
  have fit : Fintype.card Q ≤ 2^s := by
    simpa only [Q,s,Fintype.card_prod,Fintype.card_fun,Fintype.card_fin,Fintype.card_coe] using
      selector_capacity K G.supplies.card h
  obtain ⟨M,id⟩ := base_to_port D P (G.demandWidths t z) (G.supplyWidths t) (base z)
  let T : FixedMotifTile D P (fun e => h*G.demandWidths t z e) F :=
    { Alphabet := Q, bits := s, encode := (Fintype.equivFin Q).toEmbedding.trans (Fin.castLEEmb fit),
      output := fun a e => payload (G.supplyWidths t) a.2 e, entry := M, identity := id }
  exact ⟨T,by simpa only [T,s,Nat.cast_mul] using frac,fun a => rad a.2⟩

end ThreeFlat.Diagonal.ShrinkMotif

end OAI
