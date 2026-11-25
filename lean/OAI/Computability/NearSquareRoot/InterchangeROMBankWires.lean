import OAI.Computability.NearSquareRoot.InterchangeROMBankPack
import OAI.Computability.NearSquareRoot.InterchangeROMBankUnpad
import OAI.Computability.NearSquareRoot.InterchangeROMBankOpen

/-! # The inverse bank and the effective time coefficients for both adapters -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBank

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip Space
  GeneratorSyntax CommonRegisters LoomRegisters InterchangeROMBankCarve

noncomputable def unbank (b W : ℕ) : Cmd :=
  ((openBank W).join (unpad b W)).join flattenCommand

theorem effective_unbank : Effective ltr (fun x : ℕ × ℕ => unbank x.1 x.2) := by
  have opened : Effective ltr (fun x : ℕ × ℕ => openBank x.2) := effective_openBank.comp Computable.snd
  exact (opened.join effective_unpad).join (effective_const ltr _)

theorem unbank_within : ∃ R, 4 ≤ R ∧ ∀ b W, Within R (unbank b W) := by
  obtain ⟨D,hD,hopen⟩ := openBank_within
  obtain ⟨R,hR,hf⟩ := ((Filter.eventually_ge_atTop D).and
    (RegisterSelect.within_eventually flattenCommand)).exists
  exact ⟨R,hD.trans hR,fun b W => ⟨⟨RegisterSelect.within_mono hR _ (hopen W),
    RegisterSelect.within_mono (hD.trans hR) _ (unpad_within b W)⟩,hf⟩⟩

noncomputable def unbankTime (b W : ℕ) : ℕ :=
  chainCoeff (chainCoeff (openTime W) (2*(401*(W+1))+((b+1)*372+110)+2) 11) flattenCoeff 5

noncomputable def unbankSpace : ℕ :=
  chainCoeff (chainCoeff openSpace 995 11) flattenCoeff 5

theorem unbankRaw_run {P T : Type} (p : Series P) (t : Series T) {b W : ℕ}
    (hp : 0 < p.count) (ht : 0 < t.count) (hb : 0 < b) (hW : 0 < W)
    (v : Fin W → (P × Fin (BatchRows.groups b W)) × T → Tree) :
    Run (unbank b W) (unbankTime b W) unbankSpace
      ((ruler p (Series.natural (BatchRows.groups b W)) t).fork
        (stripe (Series.natural W) (fun u => flat p (Series.natural (BatchRows.groups b W)) t (v u))))
      (flat p (Series.natural b) t
        (fun z => v (BatchRows.row hW z.1.2) ((z.1.1,BatchRows.group hW z.1.2),z.2))) := by
  let d := Series.natural b
  let g := Series.natural (BatchRows.groups b W)
  let w := Series.natural W
  let z : (P × Fin b) × T → Tree := fun a => v (BatchRows.row hW a.1.2) ((a.1.1,BatchRows.group hW a.1.2),a.2)
  let raw := stripe w (fun u => flat p g t (v u))
  let src := (ruler p g t).fork raw
  let las := nested p d t z
  let opened := stripe w (fun u => nested p g t (v u))
  let blank := stripe p (fun _ => Tree.atom false)
  have hd : 0 < d.count := by simpa [d] using hb
  have hg : 0 < g.count := by simpa [g] using groups_pos hb hW
  have first := open_run hW p g t hp hg ht v
  have second := unpad_run p hW (fun u x j => stripe t (fun k => v u ((x,j),k)))
  have m₁ : (opened.fork blank).count ≤ 11*amount src las := by
    have h := stripe_counts_le w (fun u => nested p g t (v u)) (fun u => flat p g t (v u))
      (by decide : 0 < 5) (fun u => nested_le_flat p g t hg ht (v u))
    change opened.count ≤ 5*raw.count at h
    let u : Fin W := ⟨0,hW⟩
    have blank_le : blank.count ≤ (nested p g t (v u)).count := by
      apply (show blank.count ≤ 1*(nested p g t (v u)).count from ?_).trans_eq (Nat.one_mul _)
      apply stripe_counts_le p _ _ (by decide)
      intro x
      simp only [Tree.count,Nat.one_mul]
      have hpos := (stripe g (fun j => stripe t (fun k => v u ((x,j),k)))).count_pos
      omega
    have one := stripe_entry_le w (fun j => nested p g t (v j)) u
    change _ ≤ opened.count at one
    dsimp only [amount,src,Tree.count]
    omega
  have left := first.join second m₁
  have right := flatten_run p d t hp hd ht z
  have m₂ : las.count ≤ 5*amount src (flat p d t z) := by
    have h := nested_le_flat p d t hd ht z
    change las.count ≤ 5*(flat p d t z).count at h
    dsimp only [amount]; omega
  exact left.join right m₂

private theorem prChain {X : Type} [Primcodable X] {a b k : X → ℕ}
    (ha : Primrec a) (hb : Primrec b) (hk : Primrec k) :
    Primrec (fun x => chainCoeff (a x) (b x) (k x)) :=
  Primrec.nat_mul.comp (Primrec.nat_add.comp (Primrec.nat_add.comp ha hb) (.const 2))
    (Primrec.nat_add.comp hk (.const 1))

theorem primrec_bankTime : Primrec₂ bankTime := by
  have g : Primrec (fun x : ℕ × ℕ => BatchRows.groups x.1 x.2) := by
    simpa only [BatchRows.groups,Nat.ceilDiv_eq_add_pred_div] using
      Primrec.nat_div.comp (Primrec.nat_sub.comp (Primrec.nat_add.comp Primrec.fst Primrec.snd)
        (.const 1)) Primrec.snd
  exact (prChain (prChain (.const carveCoeff) (Primrec.nat_mul.comp (Primrec.nat_add.comp .snd (.const 1))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_add.comp g (.const 1)) (.const 190)) (.const 210)))
    (.const 5)) (.const _) (.const 5)).to₂

theorem primrec_unbankTime : Primrec₂ unbankTime := by
  have tr : Primrec (fun x : ℕ × ℕ => openTime x.2) := prChain
    (Primrec.nat_mul.comp (Primrec.nat_add.comp .snd (.const 1)) (.const _)) (.const 441) (.const 1)
  have time := Primrec.nat_add.comp (Primrec.nat_add.comp
    (Primrec.nat_mul.comp (.const 2) (Primrec.nat_mul.comp (.const 401) (Primrec.nat_add.comp
      (Primrec.snd (α := ℕ) (β := ℕ)) (.const 1))))
    (Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.nat_add.comp .fst (.const 1)) (.const 372)) (.const 110)))
    (.const 2)
  exact (prChain (prChain tr time (.const 11)) (.const _) (.const 5)).to₂

end InterchangeROMBank

end NearSquareRoot
end Computability
end OAI
