import OAI.Hierarchy.DiscrepancyPaddedCap
import OAI.Hierarchy.ProtocolRAMMenuAlphabetWords
import OAI.Hierarchy.ProbeHistogramNative

namespace OAI
/-! # Finite recommended packet codes and positivity of the alphabet word at their native addresses -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical Fin.CommRing

theorem DiscrepancyROM.Table.Capped.read {p D w q : ℕ} {t : DiscrepancyROM.Table p D}
    {m : Memory w} (bounded : t.Capped q m) (phase : Fin p) (key : Word w) :
    ((t.bank phase).read m key).val≤q := by
  change (m (t.base+phase.val*t.size+key.val%t.size)).val≤q
  have span : 0<t.size := Nat.zero_lt_of_lt (ProtocolRAMPurchaseSampler.lt_span t.entries)
  apply bounded
  · omega
  · have inside := Nat.mod_lt key.val span
    have next : (phase.val+1)*t.size≤p*t.size := Nat.mul_le_mul_right _ phase.isLt
    rw [Nat.succ_mul] at next
    change _<t.base+p*t.size
    omega

namespace MenuROM
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
    {sites : ℕ} [Nonempty (Fin sites)] {edge : E→Chord sites} {req : A→E}
    {box : Set (E→ℝ)} {ε tree : ℝ} {N W : ℕ} (menu : Probe.FixedMenu F edge req box ε tree N)

theorem recommendations_bounded {phases digits : ℕ} (base radix : ℕ)
    (price : Fin phases→(Fin digits→Fin radix)→E→ℝ) :
    ∀ u key, (menus menu base radix price).word u key≤Fintype.card menu.index := by
  intro u key
  change recommendation menu (price u key)≤_
  unfold recommendation
  split
  · exact (Fintype.equivFin _ _).isLt
  · exact Nat.zero_le _

/-- A nonzero code within the finite native menu denotes a genuine packet.
Its term count is positive, and fits the chosen alphabet width. -/
theorem positive_alphabet (base cap : ℕ) (m : Memory W) (key : Word W)
    (resident : (alphabets menu base).Resident m)
    (word : cap<2^W) (terms : ∀j,(menu.packet j).terms≤ cap)
    (bounded : key.val≤Fintype.card menu.index) (active : key≠0) :
    ∃j:menu.index, key.val=(Fintype.equivFin menu.index j).val+1 ∧
      ((alphabets menu base).bank 0).read m key=((menu.packet j).terms:Word W) ∧
      0< min (((alphabets menu base).bank 0).read m key).val cap := by
  have nz : 0<key.val := Nat.pos_of_ne_zero (fun h=>active (Fin.ext h))
  let j := (Fintype.equivFin menu.index).symm ⟨key.val-1,by omega⟩
  have code : key.val=(Fintype.equivFin menu.index j).val+1 := by
    change _=((Fintype.equivFin menu.index) ((Fintype.equivFin _).symm _) ).val+1
    rw [Equiv.apply_symm_apply]
    change key.val=(key.val-1)+1
    omega
  have fits : (Fintype.equivFin menu.index j).val+1<2^W := by rw [←code];exact key.isLt
  have keyEq : key=(((Fintype.equivFin menu.index j).val+1:ℕ):Word W) :=
    Fin.ext (code.trans (Fin.val_cast_of_lt fits).symm)
  have read := (congrArg (fun a : Word W => ((alphabets menu base).bank 0).read m a) keyEq).trans
    (alphabet_lookup menu base m resident j)
  refine ⟨j,code,read,?_⟩
  rw [read,Fin.val_cast_of_lt ((terms j).trans_lt word),Nat.min_eq_left (terms j)]
  exact Probe.NativeHistogram.alphabet_pos (menu.packet j)

end MenuROM
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
