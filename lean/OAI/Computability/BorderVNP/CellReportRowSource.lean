import OAI.Computability.BorderVNP.CellGadgetRowCost
import OAI.Computability.BorderVNP.CellSubtotalInputs
import OAI.Computability.BorderVNP.CellLocalSweepFields

/-! # Physical fields for one original indexed gadget subtotal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

/-- The stored bit vector of an actual subtotal and its ordinal already fit in
the complete typed directory. -/
theorem report_argument_length (D : Directory) (i : Fin D.reportedCounts.length) :
    (prodCode Typed.directory (prodCode Nat.bits Typed.naturals) (D,i.val,D.reportedCounts[i])).length+1 ≤
      6*((Typed.directory D).length+1) := by
  let reports := listCode Typed.naturals D.reportedCounts
  have hi : i.val.bits.length ≤ i.val := by rw [Nat.size_eq_bits_len,Nat.size_le]; exact Nat.lt_two_pow_self
  have hn := list_length_le_code Typed.naturals D.reportedCounts
  have hb := code_le_of_mem Typed.naturals (List.getElem_mem (l := D.reportedCounts) i.isLt)
  have hh : reports.length ≤ (Typed.directory D).length := by
    simp only [reports,Typed.directory,prodCode,pairBits_length]
    omega
  change (Typed.naturals D.reportedCounts[i]).length ≤ reports.length at hb
  change _ ≤ reports.length at hn
  have ht := i.isLt
  simp only [prodCode,pairBits_length]
  omega

/-- Specialize the complete row printer to the directory, binary index, and
named wire list supplied by the native indexed report traversal. -/
theorem reportRow_meter_components (D : Directory) (i : Fin D.reportedCounts.length) :
    reportRow.meter (D,i.val,D.reportedCounts[i]) ≤ 10^149*((Typed.directory D).length+
      scopedGlue+rowCharge D i D.reportedCounts[i]+1) := by
  let enc := prodCode Nat.bits Typed.naturals
  let x := (D,i.val,D.reportedCounts[i])
  let env := first Typed.directory enc
  let rest := second Typed.directory enc
  let hd := (identity Typed.directory).comp env
  let hi := (first Nat.bits Typed.naturals).comp rest
  let hs := (second Nat.bits Typed.naturals).comp rest
  have hx := report_argument_length D i
  have he := meter_first Typed.directory enc x
  have hr := meter_second Typed.directory enc x
  have hdir := meter_comp (identity Typed.directory) env x
  have hid := meter_identity Typed.directory D
  have hidx := meter_comp (first Nat.bits Typed.naturals) rest x
  have hlist := meter_comp (second Nat.bits Typed.naturals) rest x
  have hf := meter_first Nat.bits Typed.naturals x.2
  have hsnd := meter_second Nat.bits Typed.naturals x.2
  have hpair : (enc x.2).length ≤ (prodCode Typed.directory enc x).length := by
    rw [prodCode,pairBits_length]; omega
  change env.meter x ≤ _ at he
  change rest.meter x ≤ _ at hr
  change hd.meter x ≤ 6*(env.meter x+(identity Typed.directory).meter D) at hdir
  change hi.meter x ≤ 6*(rest.meter x+(first Nat.bits Typed.naturals).meter x.2) at hidx
  change hs.meter x ≤ 6*(rest.meter x+(second Nat.bits Typed.naturals).meter x.2) at hlist
  change (prodCode Typed.directory enc x).length+1 ≤ _ at hx
  change (first Nat.bits Typed.naturals).meter x.2 ≤ 10*((enc x.2).length+1) at hf
  change (second Nat.bits Typed.naturals).meter x.2 ≤ 300*((enc x.2).length+1) at hsnd
  apply (gadgetRow_meter_le hd hi hs x).trans
  change 10^140*(hd.meter x+hi.meter x+hs.meter x+(prodCode Typed.directory enc x).length+scopedGlue+
    rowCharge D i D.reportedCounts[i]+1) ≤ _
  omega

/-- A bound on raw fields gives a polynomial bound on every scalar entering
the local report printer and its factor sweep. -/
theorem report_params_bound (D : Directory) (i : Fin D.reportedCounts.length) {p U B j n : ℕ}
    (hraw : RawFields D p U) (hU : U ≤ B*(n+2)^j) :
    Local.ParamsBound (D.visitCount,(D.visitCount+1)*(D.visitCount+1),i.val)
      ((B+2)^6*(n+2)^(6*j)) ∧ U ≤ (B+2)^6*(n+2)^(6*j) := by
  let Z := (n+2)^j
  have hZ : 1 ≤ Z := Nat.one_le_pow _ _ (by omega)
  have hbase : U+2 ≤ (B+2)*Z := by rw [Nat.add_mul]; change U ≤ B*Z at hU; omega
  have htop : (U+2)^6 ≤ (B+2)^6*(n+2)^(6*j) := by
    simpa only [Nat.mul_pow,Z,← Nat.pow_mul,Nat.mul_comm j 6] using Nat.pow_le_pow_left hbase 6
  have hvc := resolved_prefix_le D hraw D.blocks.length
  simp only [List.take_length] at hvc
  change D.visitCount ≤ U^3 at hvc
  have hplus : D.visitCount+1 ≤ (U+2)^3 := by
    apply (Nat.add_le_add_right hvc 1).trans
    nlinarith only [Nat.zero_le (U^2),Nat.zero_le U]
  have haux := Nat.pow_le_pow_left hplus 2
  rw [← pow_mul] at haux
  have hval : U ≤ (U+2)^6 := (show U ≤ U+2 by omega).trans (Nat.le_self_pow (by decide) _)
  have hv : D.visitCount ≤ (U+2)^6 := (Nat.le_succ _).trans (hplus.trans
    (Nat.pow_le_pow_right (by omega) (by decide)))
  have hi : i.val ≤ U := i.isLt.le.trans hraw.lengths.2.2
  exact ⟨⟨hv.trans htop,(by simpa only [pow_two] using haux.trans htop),hi.trans (hval.trans htop)⟩,
    hval.trans htop⟩

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
