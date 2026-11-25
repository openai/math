import OAI.Hierarchy.DescentPrivateIssued
import OAI.Hierarchy.DescentVenueCodes

namespace OAI
/-! # Recovering the measured short cable venues from every actual issued history -/

namespace Hierarchy.DescentHostDirectory
open DescentColonies
open scoped Classical
variable {V : Type} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem merged_mem_keys (hub : V→Bool) (k g slots : ℕ) {q : Key V} (valid : q∈keys k slots) :
    mergeHub hub k g q∈keys k slots := by
  cases flag : hub q.1
  · simpa [mergeHub,flag] using valid
  · obtain ⟨tree,slot⟩:=Finset.mem_product.mp (Finset.mem_product.mp valid).2
    obtain ⟨_,hi⟩:=codes_valid tree
    have hs:=Finset.mem_range.mp slot
    have id_lt : q.2.1.2/2^(q.2.1.1-(k-g))<2^(k-g) := by
      apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).2
      rw [←pow_add]
      have exponents : q.2.1.1 ≤ (k-g) + (q.2.1.1-(k-g)) := by omega
      exact hi.trans_le (Nat.pow_le_pow_right (by decide) exponents)
    simp only [mergeHub,flag,ite_true]
    exact Finset.mem_product.mpr ⟨Finset.mem_univ _,Finset.mem_product.mpr
      ⟨mem_codes (Nat.sub_le k g) id_lt,Finset.mem_range.mpr (by change 0<slots; exact (Nat.zero_le _).trans_lt hs)⟩⟩

end Hierarchy.DescentHostDirectory

namespace Hierarchy.DescentStageEdgeReceipt
open Computability.BorderVNP.Crossing DescentSixParty DescentKernelHistory DescentHostDirectory DescentNetworkPartition
open DescentHistoryOrder GadgetNetwork DescentPacking DescentHostDegree DescentSixParty.StarKeys
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P H : Type} [Field F] [Fintype H] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {u ε : ℝ}
variable (he : 0≤ε) (T : StageInput W G u ε) (c : (T.result he).Choice)
local notation "r" => BitDescription.scannedRows he T
local notation "layout" => bestLayout (branchWidth G (fun _ : (r).pairs=>T.z) ((r).profile c))
local notation "venue" => newSite W.graph (r).pick layout (r).pack
local notation "slots" => 2^(packExponent 20 T.Δ)+2
variable {old : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)} {root : H↪ℕ}
variable {U : MarkedWorld F d P bits} {n : Normalize U} {t : Tape n.result.graph.Edge} {pair : ScanNumbers he T}

theorem IssuedRows.measured_chart (issued : IssuedRows he T c old root U n t pair) (input : U=scanWorld he T c) :
    ∃b : IssuedDonorChart he T H,
      (∀v,b.key he T c v∈keys T.k slots) ∧
      ∀x y : (rawGraph he T c).Site,n.destination (rawInput he T c input x)=n.destination (rawInput he T c input y) ↔
        mergeHub b.hub T.k (gainExponent 20 T.Δ) (b.key he T c (venue x))=
          mergeHub b.hub T.k (gainExponent 20 T.Δ) (b.key he T c (venue y)) := by
  induction issued with
  | stage col same hub k g q legal source oldCut used cut=>
    obtain ⟨_,size,gain,valid,coord,code,oldRow⟩:=source
    subst k
    subst g
    let b : IssuedDonorChart he T H:=⟨col,same,hub,coord,code,oldRow⟩
    exact ⟨b,valid,fun x y=>Subtype.ext_iff⟩
  | named n t keep site ih=>
    obtain ⟨b,valid,read⟩:=ih input
    exact ⟨b,valid,fun x y=>(Normalize.destination_appendNames n _ _ _ _).trans (read x y)⟩

theorem IssuedRows.donor_chart (issued : IssuedRows he T c old root U n t pair) (input : U=scanWorld he T c) :
    ∃(key : (scanWorld he T c).graph.Site↪Key H) (hub : H→Bool),
      (∀v,key v∈keys T.k slots) ∧
      ∀x y : (rawGraph he T c).Site,n.destination (rawInput he T c input x)=n.destination (rawInput he T c input y) ↔
        mergeHub hub T.k (gainExponent 20 T.Δ) (key (venue x))=
          mergeHub hub T.k (gainExponent 20 T.Δ) (key (venue y)) := by
  obtain ⟨b,read⟩:=IssuedRows.measured_chart he T c issued input
  exact ⟨b.key he T c,b.hub,read⟩

theorem rawInput_eq_iff (input : U=scanWorld he T c) (x y : (rawGraph he T c).Site) :
    rawInput he T c input x=rawInput he T c input y ↔ venue x=venue y := by
  subst U
  rfl

end
end Hierarchy.DescentStageEdgeReceipt

end OAI
