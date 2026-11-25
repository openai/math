import OAI.Hierarchy.DescentResetStencilAddressBook
import OAI.Hierarchy.DescentResetPortReaders

namespace OAI
/-! # Reading each paid and original-coordinate field from the same smaller physical bank -/
namespace Hierarchy.DescentSixParty.PackedFlow.Channels
open DescentGLPacked DescentGLPacked.BankImage DescentPlainTerminal DescentPlainTerminal.Suffix DescentGL DescentColonies
open DescentSIMDLookup DescentPackedZip DescentIssuedFallbackPanel DescentPackedColony.Phase
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {D H h l b w c M floor : ℕ}

def shortBank (out H G M : ℕ) (i : Fin D) : Bank :=
  ⟨slice out H (chunks G M) i,Nat.clog 2 (H*chunks G M)⟩

theorem short_fits (out : ℕ) (i : Fin D) (upper : out+D*H*chunks (2^c) M+2^(Nat.clog 2 (H*chunks (2^c) M))≤floor)
    (word : floor<2^w) : (shortBank out H (2^c) M i).Fits w floor := by
  have size:=Nat.two_pow_pos (Nat.clog 2 (H*chunks (2^c) M))
  have begin: i.val*H*chunks (2^c) M≤D*H*chunks (2^c) M:=Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ i.isLt.le)
  let span := 2^(Nat.clog 2 (H*chunks (2^c) M))
  change 0<span ∧ span<2^w ∧ (out+i.val*H*chunks (2^c) M)+span≤floor
  dsimp [span]
  exact ⟨size,by omega,by omega⟩

def narrowImage (base b r M : ℕ) : Arena.Image w := ⟨base,base+2^(b*2^r*M),fun z=>
    let a:=b*2^r*M
    let key:Cell a:=(z-base:ℕ)
    (DescentSIMDLookup.table (M:=M) (Original.narrow b r) key).val⟩

theorem narrow_words (base b r M : ℕ) (mem : Memory w) (issued : (narrowImage base b r M).Resident mem)
    (x : Cell ((b*2^r)*M)) :
    mem (base+x.val)=((DescentSIMDLookup.table (M:=M) (Original.narrow b r) x).val:Word w) := by
  have get:=issued (base+x.val) (Nat.le_add_right ..) (Nat.add_lt_add_left x.isLt base)
  simpa [narrowImage,Nat.add_sub_cancel_left,Fin.cast_val_eq_self] using get

local notation "m" => h+l
local notation "r" => m-c

theorem operands_short (small : c≤ m) (loads : Fin H→Block m→Cell b) (paid : Fin D→Fin H→Block m→Cell b)
    (positive : 0<b) (L : DescentGL.Layout m) (out floor base : ℕ) (mem : Memory w)
    (upper : out+((1+D)+m)*H*chunks (2^c) M+2^(Nat.clog 2 (H*chunks (2^c) M))≤floor)
    (fit : floor<2^w) (literal : base+2^((b*2^r)*M)≤floor) (pub : (narrowImage base b r M).Resident mem)
    (read : ∀(i : Index D m) (p : Row H (2^c) M),mem (slice out H (chunks (2^c) M) i+(row _ _ _ p).val)=
      ((data (blockValues small (values loads paid positive i) L) p).val:Word w)) :
    let bank:=shortBank out H (2^c) M (D:=(1+D)+m)
    Source (.lookup (bank (loadIndex D m)) .row) (blockValues small loads L) M mem ∧
    (∀j,Source (.lookup (bank (flowIndex m j)) .row) (blockValues small (paid j) L) M mem) ∧
    ∀d,Source (PackedOrder.projected ⟨base,(b*2^r)*M⟩ (.lookup (bank (planeIndex D d)) .row))
      (fun (_:Fin H) hi=>PackedOrder.panel small L hi d) M mem := by
  intro bank
  have direct (i : Index D m) : Source (.lookup (bank i) .row) (blockValues small (values loads paid positive i) L) M mem :=
    source_column (bank i) floor (short_fits _ i upper fit) mem _ (Nat.le_pow_clog (by decide) _) (read i)
  refine ⟨?_,?_,?_⟩
  · have load : values loads paid positive (loadIndex D m) = loads := by
      funext v x
      simp [values,loadIndex]
    simpa only [load] using direct (loadIndex D m)
  · intro j
    have flow : values loads paid positive (flowIndex m j) = paid j := by
      funext v x
      simp [values,flowIndex]
    simpa only [flow] using direct (flowIndex m j)
  · intro d
    have room : (⟨base,(b*2^r)*M⟩:Bank).Fits w floor:=⟨Nat.two_pow_pos _,by change 2^((b*2^r)*M)<2^w;omega,literal⟩
    apply Original.panel_source small positive L d _ _ floor mem room rfl (narrow_words base b r M mem pub)
    have plane : values loads paid positive (planeIndex D d) = fun _ x=>Original.bit positive d x := by
      funext v x
      simp [values,planeIndex]
    have readPlane := direct (planeIndex D d)
    rw [plane] at readPlane
    unfold blockValues at readPlane
    exact readPlane

end
end Hierarchy.DescentSixParty.PackedFlow.Channels

end OAI
