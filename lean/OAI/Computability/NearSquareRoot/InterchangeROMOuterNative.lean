import OAI.Computability.NearSquareRoot.InterchangeROMOuterGeometry
import OAI.Computability.NearSquareRoot.InterchangeROMOuterSequence
import OAI.Computability.NearSquareRoot.InterchangeROMStarsStage

/-!
# Native command for banking, the cubic main swap, and the outer reserve swaps
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMOuter

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Port IntegerMultiplication.Loom
  NearSquareRoot.InterchangeROMRecursion NearSquareRoot.InterchangeAddress NearSquareRoot.InterchangeAddress.Request
  NearSquareRoot.InterchangeROMExpose NearSquareRoot.InterchangeROMRepair NearSquareRoot.InterchangeROMRepair.Physical
  NearSquareRoot.InterchangeROMTable NearSquareRoot.InterchangeSpectralFibre

abbrev value {p : ℕ} (x : ZMod p) := numeral x.val

abbrev key (i : Input) (W : ℕ) :=
  Keys (i.req.before ++ [BatchRows.groups i.b W]) (axisG i ()) (axisB i ()) (Fin i.n) (Block i.b (f i))

abbrev tensor (i : Input) (p l n : ℕ) :=
  Bank (ZMod (p+1)) (Fin l) (key i (l*n) × Fin i.req.recordWidth) (Fin n)

abbrev groupedHeader (i : Input) (W : ℕ) :=
  InterchangeROMAddress.header (f i) (i.req.before ++ [BatchRows.groups i.b W]) (axisG i ()) (axisB i ())

noncomputable abbrev stream (i : Input) (W : ℕ) (σ : key i W → key i W) :=
  stripe (Series.natural W) (fun u => stripe (groupedRows i W) (paddedRow i u ∘ σ))

noncomputable abbrev cubic (i : Input) {p l n : ℕ} (x : tensor i p l n) :=
  InterchangeROM.packet (send (groupedHeader i (l*n))) (LocalTable.Lift.bank (groupedRows i (l*n))
    (fun _ => Series.natural i.req.recordWidth) (fun k j => (k,j)) x)

abbrev permute {i : Input} {p l n : ℕ} (x : tensor i p l n) (σ : key i (l*n) → key i (l*n)) :
    tensor i p l n := fun u z k => x u (σ z.1,z.2) k

/-- For an actual parent, decode all its padded native row records at once.
Applying a key permutation to the field tensor recovers the same physical
rows with that permutation inside each label and lane. -/
theorem tensor_input (i : Input) (p l n : ℕ) (ok : Packed (@value (p+1)) i.req) :
    ∃ x : tensor i p l n, ∀ σ, cubic i (permute x σ) =
      .fork (send (groupedHeader i (l*n))) (stream i (l*n) σ) := by
  obtain ⟨x,hx⟩ := bank_wires (p:=p) (l:=l) (n:=n) (groupedRows i (l*n))
    (Series.natural i.req.recordWidth) (paddedRow i) (fun _ _ => ok.2.2 _)
  exact ⟨x,fun σ => congrArg (Tree.fork (send (groupedHeader i (l*n)))) (hx σ)⟩

/-- The banked cubic runs underneath the original native header. The inverse
unbanking pass restores the initial row layout before any full-volume call. -/
noncomputable def stage (b a m : ℕ) (enter main leave : Cmd) :=
  ((enter.join (InterchangeROM.underHeader main)).join leave).join (InterchangeROMStars.command b a m)

theorem effective_stage {T : Type} [Primcodable T] {b a m : T → ℕ} {enter main leave : T → Cmd}
    (hb : Computable b) (ha : Computable a) (hm : Computable m)
    (he : GeneratorSyntax.Effective GeneratorSyntax.ltr enter)
    (hc : GeneratorSyntax.Effective GeneratorSyntax.ltr main)
    (hl : GeneratorSyntax.Effective GeneratorSyntax.ltr leave) :
    GeneratorSyntax.Effective GeneratorSyntax.ltr (fun t => stage (b t) (a t) (m t) (enter t) (main t) (leave t)) :=
  ((he.join (KernelEffectiveFamily.effective_right hc)).join hl).join (InterchangeROMStars.effective hb ha hm)

theorem within_stage {b a m R : ℕ} {enter main leave : Cmd} (hR : 3≤R) (he : CommonRegisters.Within R enter)
    (hc : CommonRegisters.Within R main) (hl : CommonRegisters.Within R leave)
    (hs : CommonRegisters.Within R (InterchangeROMStars.command b a m)) :
    CommonRegisters.Within R (stage b a m enter main leave) :=
  ⟨⟨⟨he,InterchangeROM.underHeader_within hR hc⟩,hl⟩,hs⟩

theorem record_size {p : ℕ} [NeZero p] {t : Tree} {w : ℕ} (h : record (@value p) w t) :
    t.count ≤ (2*p+3)*(w+1) := by
  obtain ⟨v,rfl⟩ := h
  have sz : ∀ j, ((@value p ∘ v) j).count ≤ 2*p+1 := by
    intro j
    change size (tally (v j).val) ≤ _
    rw [size_tally,tally_length]
    have := (v j).val_lt
    omega
  have bound := stripe_size (Series.natural w) _ _ sz
  rw [Series.count_natural] at bound
  exact bound.trans ((Nat.add_le_add (Nat.mul_le_mul_left w (show 2*p+1+1≤2*p+3 by omega))
    (show 1≤2*p+3 by omega)).trans_eq (by ring))

end InterchangeROMOuter

end NearSquareRoot
end Computability
end OAI
