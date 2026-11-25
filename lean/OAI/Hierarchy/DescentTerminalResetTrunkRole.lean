import OAI.Hierarchy.DescentTerminalResetRoleWords
import OAI.Hierarchy.DescentResetTerminalNodeFields

namespace OAI
/-! # The three genuine reset sources of all immutable scalar fields -/
namespace Hierarchy.DescentTerminalCombinedRole
open DescentBundleHistory DescentKernelHistory DescentNamedContact DescentRouterBank DescentResetTrunks Computability.BorderVNP.Crossing
open DescentEpochTagKeys
open scoped Classical
noncomputable section
variable {n d L p : ℕ} {P H Q X Y U : Type} [Fintype H] [Fintype Q] {bits:P→ℕ}
    (N:Network n P bits) (home:N.Site→H) (group:Bool→N.Edge→Q)
    (R:Network d (Bool×Q) (publicWidth group N.width)) (key:N.Edge↪Fin L)
    (whole:∀e,p∣N.width e) (hp:0<p)
    (old:SiteBits (U:=X) N) (bank:SiteBits (U:=Y) R)
    (src:∀v,Shape p (old v)) (dev:∀v,Shape p (bank v))
local notation "sh" => trunkShape N home group R key whole hp old bank src dev
local notation "tr" => trunkBits N home group R key old bank

omit [Fintype Q] in
theorem retained_fields (v:N.Site) (u:(old v).Node) :
    (sh (.inl (false,home v))).sliceFields ⟨⟨v,rfl⟩,u⟩=(src v).sliceFields u := by
  have eq:=congrArg Prod.snd (retained_terminal_tag N home group R key whole hp old bank src dev v u)
  rw [(sh (.inl (false,home v))).tag_fields hp ⟨⟨v,rfl⟩,u⟩, (src v).tag_fields hp u] at eq
  exact eq

omit [Fintype Q] in
theorem device_fields (v:R.Site) (u:(bank v).Node) :
    (sh (.inr v)).sliceFields u=(dev v).sliceFields u := by
  have eq:=congrArg Prod.snd (bank_terminal_tag N home group R key whole hp old bank src dev v u)
  rw [(sh (.inr v)).tag_fields hp u, (dev v).tag_fields hp u] at eq
  exact eq

/-- A relay consumes precisely two original cable words of equal true width. -/
def relayFields (p w:ℕ) : List (List SliceCode) :=
  List.replicate 2 (List.replicate (w/p) ⟨0,1,1⟩)

omit [Fintype Q] in
theorem relay_fields (h:H) (e:Fibre (moved N home) h) :
    (sh (.inl (true,h))).sliceFields e=relayFields p (N.width e.val) := by
  change (List.ofFn fun _ : Fin 2 => List.ofFn fun _ : Fin (N.width e.val / p) =>
    (⟨0,1,1⟩ : SliceCode)) = _
  simp [List.ofFn_const,relayFields]

variable {initial A gr stride : ℕ} (dict:Codec U initial) (relayTag:U)
local notation "raw" => fun t xs=>rawWords (n:=initial) (p:=p) (R:=stride) (birth (A:=A) (G:=gr) dict t xs)

omit [Fintype Q] in
theorem relay_printed (h:H) (e:Fibre (moved N home) h)
    (valid:DescentBundleTagKeys.Fits dict A gr p stride (relayTag,(sh (.inl (true,h))).sliceFields e)) :
    Printed dict («fields» (raw relayTag (relayFields p (N.width e.val)))) relayTag ((sh (.inl (true,h))).sliceFields e) := by
  rw [←relay_fields N home group R key whole hp old bank src dev h e]
  exact birth_printed dict _ _ valid

end
end Hierarchy.DescentTerminalCombinedRole

end OAI
