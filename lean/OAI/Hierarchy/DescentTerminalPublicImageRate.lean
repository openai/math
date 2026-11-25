import OAI.Hierarchy.DescentTerminalPublicIdentity
import OAI.Hierarchy.DescentTerminalChipBootExtent
import OAI.Hierarchy.DescentDatedAddressRate

namespace OAI
/-! # The original physical size of the immutable terminal input image -/
namespace Hierarchy.DescentTerminalPublicIdentity
open DescentTerminalDenseWindow DescentTerminalBinReaddress DescentDatedAddressBook Filter
noncomputable section

/-- All ten original chip columns, four width dictionaries, and two dyadic input pages. -/
theorem total_envelope (K W q piece codes rows publicRows a : ℕ)
    (bought : K*W≤2^a) (raw : rows≤2^a) (outer : publicRows≤2^a)
    (dense : formatBits q (W*piece)+2*(q*(W*piece))≤a)
    (route : DescentTerminalBinFormat.controlBits W q+sliceWidth W q piece≤a)
    (alphabet : codes≤2^a) :
    total K W q piece codes rows publicRows≤2^(a+7) := by
  have powPos : 0<2^a:=Nat.two_pow_pos _
  have half : 2*(a+1)/2=a+1:=by omega
  have denseRoom : formatBits q (W*piece)+2*(q*(W*piece))≤2*(a+1)/2:=by omega
  have routeRoom : DescentTerminalBinFormat.controlBits W q+sliceWidth W q piece≤2*(a+1)/2:=by omega
  have codesRoom : codes+1≤2^(2*(a+1)/2):=by rw [half,pow_succ]; omega
  have chip:=DescentTerminalChipBootWords.room K W q piece codes (2*(a+1)) denseRoom routeRoom codesRoom
  have header:=DescentTerminalDenseHeaderBoot.extent_le denseRoom
  have paid:=DescentTerminalPaidBoot.total_le K W q piece codes rows
  have «public»:=total_le K W q piece codes rows publicRows
  rw [half,pow_succ] at chip header
  unfold DescentTerminalBoot.total at paid
  rw [pow_add]
  norm_num
  omega

/-- A shared payload cutoff for the three lookup alphabets and the actual purchased
linear pages gives one address exponent for every original input record. -/
theorem extra_rate {ι : ℕ→Type*} (K W q piece codes rows publicRows : ∀h,ι h→ℕ)
    (linear : Bounded fun h i => K h i*W h i+rows h i+publicRows h i)
    (alphabet : Bounded codes)
    (lookups : ∃B:ℕ,∀ᶠ h:ℕ in atTop,∀i:ι h,
      formatBits (q h i) (W h i*piece h i)+2*(q h i*(W h i*piece h i))≤B*h ∧
      DescentTerminalBinFormat.controlBits (W h i) (q h i)+sliceWidth (W h i) (q h i) (piece h i)≤B*h) :
    Bounded fun h i => total (K h i) (W h i) (q h i) (piece h i) (codes h i) (rows h i) (publicRows h i) := by
  obtain ⟨A,hA⟩:=linear
  obtain ⟨B,hB⟩:=alphabet
  obtain ⟨C,hC⟩:=lookups
  let L:=max (max A B) C
  refine ⟨L+7,?_⟩
  filter_upwards [hA,hB,hC,eventually_ge_atTop 1] with h a b c hh
  intro i
  have wa : A*h≤L*h:=Nat.mul_le_mul_right _ ((Nat.le_max_left ..).trans (Nat.le_max_left ..))
  have wb : B*h≤L*h:=Nat.mul_le_mul_right _ ((Nat.le_max_right ..).trans (Nat.le_max_left ..))
  have wc : C*h≤L*h:=Nat.mul_le_mul_right _ (Nat.le_max_right ..)
  have numbers:K h i*W h i+rows h i+publicRows h i≤2^(L*h):=(a i).trans (Nat.pow_le_pow_right (by decide) wa)
  have result:=total_envelope (K h i) (W h i) (q h i) (piece h i) (codes h i) (rows h i) (publicRows h i) (L*h)
    (by omega) (by omega) (by omega) ((c i).1.trans wc) ((c i).2.trans wc)
    ((b i).trans (Nat.pow_le_pow_right (by decide) wb))
  apply result.trans (Nat.pow_le_pow_right (by decide) _)
  rw [Nat.add_mul]
  omega

end
end Hierarchy.DescentTerminalPublicIdentity

end OAI
