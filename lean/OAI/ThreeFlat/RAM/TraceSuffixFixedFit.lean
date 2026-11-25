import OAI.ThreeFlat.RAM.TraceSuffixFixed

namespace OAI
/-! # Word correctness of the single-read uniform scalar kernel -/

namespace ThreeFlat.RAM.TraceSuffixOracle
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing
variable {W K : ℕ}

theorem address_lt (s : Layout) (t : ℕ) (h : Bounds W s t) : address s t<2^W := by
  obtain ⟨small,index,width,paired,params,table,count,code,desc,ps,tab⟩ := h
  unfold address rawAddress tailBit
  split_ifs <;> omega

private theorem fits_branches {test left right : Prop} [Decidable test]
    (yes : left) (no : right) : (if test then left else right) := by
  by_cases h : test
  · simpa only [ite_eq_left h] using yes
  · simpa only [ite_eq_right h] using no

theorem rawAddress_fits (s : Layout) (m : ℕ → ℕ) (t : ℕ) (h : Bounds W s t) :
    rawAddressForm.Fits W s.params m (fun _ => t) := by
  obtain ⟨small,index,width,paired,params,table,count,code,desc,ps,tab⟩ := h
  have bit : t-s.rawTable<2^W := (Nat.sub_le ..).trans_lt index
  have word := (Nat.div_le_self (t-s.rawTable) s.hWidth).trans_lt bit
  have pos := (Nat.mod_le (t-s.rawTable) s.hWidth).trans_lt bit
  have field := (Nat.mod_lt ((t-s.rawTable)/s.hWidth) (show 0<11 by decide)).trans small
  have last := (Nat.sub_le s.hWidth 1).trans_lt width
  have ones : 1<2^W := by omega
  have three : 3<2^W := by omega
  simp only [rawAddressForm,Formula.Fits,Formula.natural,Layout.params,natOp,opFits,
    index,width,paired,params,table,count,bit,word,pos,field,last,small,ones,three,
    true_and,and_true]
  repeat' first | exact True.intro | apply fits_branches

theorem fixed_fits (s : Layout) (m : ℕ → ℕ) (t : ℕ) (h : Bounds W s t) :
    (Formula.load addressForm).Fits W s.params m (fun _ => t) := by
  constructor
  · have low := rawAddress_fits s m t h
    have ht := h.index
    have code := h.code
    have base : s.codeBase<2^W := by omega
    simp only [addressForm,Formula.Fits,Formula.natural,Layout.params,natOp,opFits,
      low,ht,base,code,and_true,ite_self]
  · rw [address_nat]
    exact address_lt s t h

theorem fixedOracle_eval (s : Layout) (slots : Fin 11 → Fin K) (data : Fin K → Word W) (m : Memory W)
    (t : ℕ) (h : Bounds W s t) (params : ∀ i, data (slots i)=(s.fields i : Word W))
    (zero : (m 0).val=0) (one : (m 1).val=1) :
    (fixedOracle W K slots).eval data m (fun _ => (t : Word W))=(read s (fun j => (m j).val) t : Word W) := by
  have pub : data ∘ (slots ∘ Param.index) = fun p => (s.params p : Word W) := by
    funext p
    simpa only [Function.comp_apply,Layout.fields_at] using params p.index
  rw [fixedOracle,Formula.eval_compile,pub]
  have e := Formula.value_eq_natural (.load addressForm) s.params (fun j => (m j).val) (fun _ => t)
    (fixed_fits s _ t h)
  have rd := address_reads s (fun j => (m j).val) t zero one
  rw [← rd]
  simpa only [Formula.natural,address_nat,Fin.cast_val_eq_self] using e

end ThreeFlat.RAM.TraceSuffixOracle

end OAI
