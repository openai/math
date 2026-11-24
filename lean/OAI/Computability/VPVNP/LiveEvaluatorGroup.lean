import OAI.Computability.VPVNP.LiveEvaluatorCells
import OAI.Computability.VPVNP.LiveEvaluatorRAMPrepareImage

/-!
# Exact choice multiplicity of one native live evaluator group

The preparing call is the only call that can consume a choice bit. It
publishes one instruction in scratch and all later calls check its tape
cells without altering memory. The successful preparation bit streams are
in bijection with exactly the nonrejecting choices of the evaluator.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveEvaluatorGroup

open BurstRAM (Word Memory)
open UniversalMachine (Program)
open LiveEvaluatorEncoding (Code)
open LiveEvaluatorRAM (PrepLayout ConfigAt Prepared prepared_iff preparedMemory preparedMemory_images)
open LiveEvaluatorRAM.Schedule (Pub calls)
open LiveEvaluatorAction (pick_checks_iff checks pick_bit_unique branchBits)
open LiveEvaluatorStep (nextCode)

variable {M w : ℕ} {p : Program} {pub : Pub → Word w} {m : Memory w} {old out : Code p.extra M}

theorem calls_fit (hl : PrepLayout p pub M) : calls M < 2 ^ w := by
  have h := hl.oldFit
  obtain ha | ha := hl.oldDisjoint
  · exact (Nat.le_add_left ..).trans_lt (ha.trans_lt (pub 3).isLt)
  · omega

/-- Accepting native streams after the entire cell scan. -/
def SuccessfulStream (M : ℕ) (p : Program) (pub : Pub → Word w) (m : Memory w) (bs : List Bool) : Prop :=
  ∃ mem, Prepared p pub m mem bs ∧ AllCells M p pub mem

/-- No assumptions about which evaluator row or native slot was selected
are needed. The memory contents and choice string determine that selection. -/
theorem successfulStream_iff (hl : PrepLayout p pub M)
    (ho : ConfigAt m (pub 1) old) (hz : ConfigAt m (pub 2) out) (bs : List Bool) :
    SuccessfulStream M p pub m bs ↔
      ∃ bit, bs = branchBits p old bit ∧ nextCode p old bit = some out ∧ out ≠ .rejected := by
  constructor
  · rintro ⟨mem, hp, hc⟩
    obtain ⟨bit, a, ha, hpos, he, hb, rfl⟩ := (prepared_iff hl ho hz).mp hp
    obtain ⟨ho', hz', himg⟩ := preparedMemory_images hl ho hz ha
    have hchecks := (allCells_iff p pub _ old out a bit hl.width hl.radius (calls_fit hl)
      ho' hz' himg ha hpos he).mp hc
    exact ⟨bit, hb, (pick_checks_iff p old out bit).mp ⟨a, ha, hchecks⟩⟩
  · rintro ⟨bit, hb, hstep⟩
    obtain ⟨a, ha, hchecks⟩ := (pick_checks_iff p old out bit).mpr hstep
    obtain ⟨ho', hz', himg⟩ := preparedMemory_images hl ho hz ha
    have hpos := hchecks.1
    have he := hchecks.2.1.symm
    exact ⟨preparedMemory p pub m old a, (prepared_iff hl ho hz).mpr ⟨bit, a, ha, hpos, he, hb, rfl⟩,
      (allCells_iff p pub _ old out a bit hl.width hl.radius (calls_fit hl) ho' hz' himg ha hpos he).mpr hchecks⟩

/-- The group preserves path counts, including two slots with the same
successor, without introducing a choice in a deterministic row or carry. -/
noncomputable def streamEquiv (hl : PrepLayout p pub M)
    (ho : ConfigAt m (pub 1) old) (hz : ConfigAt m (pub 2) out) :
    {bit : Bool // nextCode p old bit = some out ∧ out ≠ .rejected} ≃
      {bs : List Bool // SuccessfulStream M p pub m bs} := by
  refine Equiv.ofBijective
    (fun bit => ⟨branchBits p old bit.val, (successfulStream_iff hl ho hz _).mpr ⟨bit.val, rfl, bit.property⟩⟩)
    ⟨?_, ?_⟩
  · intro b d h
    obtain ⟨a, ha, _⟩ := (pick_checks_iff ..).mpr b.property
    obtain ⟨a', ha', _⟩ := (pick_checks_iff ..).mpr d.property
    exact Subtype.ext (pick_bit_unique p old ha ha' (congrArg Subtype.val h))
  · rintro ⟨bs, hbs⟩
    obtain ⟨bit, hb, hs⟩ := (successfulStream_iff hl ho hz bs).mp hbs
    exact ⟨⟨bit, hs⟩, Subtype.ext hb.symm⟩

theorem card_streams (hl : PrepLayout p pub M)
    (ho : ConfigAt m (pub 1) old) (hz : ConfigAt m (pub 2) out) :
    Nat.card {bs : List Bool // SuccessfulStream M p pub m bs} =
      Nat.card {bit : Bool // nextCode p old bit = some out ∧ out ≠ .rejected} :=
  Nat.card_congr (streamEquiv hl ho hz).symm

end LiveEvaluatorGroup

end VPVNP
end Computability
end OAI
