import OAI.Computability.NearSquareRoot.InterchangeROMBankCompose

/-! # Banking the raw center stream in physical register order -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip Space
  GeneratorSyntax CommonRegisters LoomRegisters InterchangeROMBankCarve

noncomputable def bank (b W : ℕ) : Cmd :=
  (carveCommand.join (pad b W)).join (mapCommand flattenCommand)

theorem effective_bank : Effective ltr (fun x : ℕ × ℕ => bank x.1 x.2) :=
  ((effective_const ltr carveCommand).join effective_pad).join (effective_const ltr _)

theorem bank_within : ∃ R, 4 ≤ R ∧ ∀ b W, Within R (bank b W) := by
  obtain ⟨R,hR,hc,hf⟩ := ((Filter.eventually_ge_atTop 4).and
    ((RegisterSelect.within_eventually carveCommand).and
     (RegisterSelect.within_eventually flattenCommand))).exists
  exact ⟨R,hR,fun b W => ⟨⟨hc, RegisterSelect.within_mono (by omega : 3 ≤ R) _ (pad_within b W)⟩,
    map_within (by omega) hf⟩⟩

noncomputable def bankTime (b W : ℕ) : ℕ :=
  chainCoeff (chainCoeff carveCoeff ((W+1)*((BatchRows.groups b W+1)*190+210)) 5)
    (flattenCoeff+110) 5

noncomputable def bankSpace : ℕ :=
  chainCoeff (chainCoeff carveCoeff 281 5) (flattenCoeff+50) 5

theorem groups_pos {b W : ℕ} (hb : 0 < b) (hW : 0 < W) : 0 < BatchRows.groups b W := by
  have h := BatchRows.le_groups_volume (b := b) hW
  by_contra! hn
  rw [Nat.le_zero.mp hn,Nat.mul_zero] at h
  omega

theorem bankRaw_run {P T : Type} (p : Series P) (t : Series T) {b W : ℕ}
    (hp : 0 < p.count) (ht : 0 < t.count) (hb : 0 < b) (hW : 0 < W)
    (v : (P × Fin b) × T → Tree) :
    Run (bank b W) (bankTime b W) bankSpace
      ((ruler p (Series.natural b) t).fork (flat p (Series.natural b) t v))
      (stripe (Series.natural W) (fun u => flat p (Series.natural (BatchRows.groups b W)) t
        (fun z => v ((z.1.1,BatchRows.select hb u z.1.2),z.2)))) := by
  let d := Series.natural b
  let g := Series.natural (BatchRows.groups b W)
  let w := Series.natural W
  let y (u : Fin W) (z : (P × Fin (BatchRows.groups b W)) × T) := v ((z.1.1,BatchRows.select hb u z.1.2),z.2)
  let src := (ruler p d t).fork (flat p d t v)
  let dst := stripe w (fun u => flat p g t (y u))
  let pending := stripe w (fun u => nested p g t (y u))
  have hd : 0 < d.count := by simpa [d] using hb
  have hg : 0 < g.count := by simpa [g] using groups_pos hb hW
  have first := carve_run p d t hp hd ht v
  have second := pad_run (W := W) p hb (fun x j => stripe t (fun z => v ((x,j),z)))
  have m₁ : (nested p d t v).count ≤ 5*amount src pending := by
    have h := nested_le_flat p d t hd ht v
    change (nested p d t v).count ≤ 5*(flat p d t v).count at h
    dsimp only [src,amount,Tree.count]
    omega
  have left := first.join second m₁
  have right := map_run w (fun u => nested p g t (y u)) (fun u => flat p g t (y u))
    (fun u => flatten_run p g t hp hg ht (y u))
  have m₂ : pending.count ≤ 5*amount src dst := by
    have h := stripe_counts_le w (fun u => nested p g t (y u)) (fun u => flat p g t (y u))
      (by decide : 0 < 5) (fun u => nested_le_flat p g t hg ht (y u))
    change pending.count ≤ 5*dst.count at h
    dsimp only [amount]
    omega
  exact left.join right m₂

end InterchangeROMBank

end NearSquareRoot
end Computability
end OAI
