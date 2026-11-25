import OAI.Computability.BorderVNP.CellBoxSpanStatic
import OAI.Computability.BorderVNP.CellLocalVisitMeter

/-! # Scalar fields on the actual resolved box visits

Resolution chooses an original stored factor list or the empty default.
Its prefix ordinal is bounded by the number of records times the largest
copy count times the largest stored factor count. The three independently
computed sweep parameters may be larger than any raw directory field.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

/-- A resolved box contains an original stored factor list, or the default empty list. -/
theorem resolved_factors_source (D : Directory) (b : BoxBlock) (hb : b ∈ D.blocks) :
    b.factors = [] ∨ b.factors ∈ D.boxes := by
  obtain ⟨r,_,he⟩ := List.mem_filterMap.mp hb
  cases r with
  | zero | equal | profile => contradiction
  | box id base c stride =>
    change some (⟨base,c,stride,D.boxes.getD id []⟩ : BoxBlock) = some b at he
    obtain rfl := Option.some.inj he
    by_cases hi : id < D.boxes.length
    · right
      simpa only [List.getD,List.getElem?_eq_getElem hi,Option.getD_some] using List.getElem_mem hi
    · left
      simp only [List.getD,List.getElem?_eq_none (Nat.le_of_not_gt hi),Option.getD_none]

/-- Fixed dimensions of all stored factor tables transfer to every actual private visit. -/
theorem resolved_tableBound (D : Directory) {T : ℕ}
    (ht : ∀ fs ∈ D.boxes, ∀ f ∈ fs, f.TableBound T) (b : BoxBlock) (hb : b ∈ D.blocks)
    (f : Factor) (hf : f ∈ b.factors) : f.TableBound T := by
  rcases resolved_factors_source D b hb with he|hs
  · simp [he] at hf
  · exact ht _ hs _ hf

/-- Every resolved one-copy list retains its bounded original count. -/
theorem resolved_factor_count (D : Directory) {p U : ℕ} (h : RawFields D p U) (b : BoxBlock)
    (hb : b ∈ D.blocks) : b.factors.length ≤ U := by
  rcases resolved_factors_source D b hb with he|hs
  · simp [he]
  · exact (h.boxes _ hs).1

/-- The cumulative start of any prefix uses at most the cube of the raw scalar bound. -/
theorem resolved_prefix_le (D : Directory) {p U : ℕ} (h : RawFields D p U) (i : ℕ) :
    ((D.blocks.take i).map fun b => b.copies*b.factors.length).sum ≤ U^3 := by
  have len : (D.blocks.take i).length ≤ U := calc
    _ ≤ D.blocks.length := by simp only [List.length_take]; exact min_le_right ..
    _ ≤ D.records.length := List.length_filterMap_le ..
    _ ≤ U := h.lengths.2.1
  have hsum := List.sum_le_sum (l := D.blocks.take i) (g := Function.const _ (U*U)) (fun b hb =>
    Nat.mul_le_mul (resolved_fields D h b (List.mem_of_mem_take hb)).2.1
      (resolved_factor_count D h b (List.mem_of_mem_take hb)))
  simp only [List.map_const,List.sum_replicate,nsmul_eq_mul] at hsum
  exact hsum.trans ((Nat.mul_le_mul_right (U*U) len).trans_eq (by ring))

private theorem factorFields_mono {f : Factor} {U V : ℕ} (h : FactorFields f U) (hu : U ≤ V) : FactorFields f V := by
  cases f with
  | truth ws rs | sign ws rs =>
    obtain ⟨⟨⟨hw,hr⟩,ha⟩,_⟩ := h
    exact ⟨⟨⟨hw.trans hu,hr.trans hu⟩,fun w hm => (ha w hm).trans hu⟩,trivial⟩
  | gadget ws rs =>
    obtain ⟨⟨⟨hw,hr⟩,ha⟩,hi⟩ := h
    exact ⟨⟨⟨hw.trans hu,hr.trans hu⟩,fun w hm => (ha w hm).trans hu⟩,fun r hm => (hi r hm).trans hu⟩
  | unary w q =>
    obtain ⟨⟨_,hw,hb,hc,hl⟩,_⟩ := h
    exact ⟨⟨trivial,hw.trans hu,hb.trans hu,hc.trans hu,hl.trans hu⟩,trivial⟩

namespace Local

/-- Numeric bounds for the three precomputed arguments of a sweep. -/
def ParamsBound (x : Params) (V : ℕ) : Prop := x.1 ≤ V ∧ x.2.1 ≤ V ∧ x.2.2 ≤ V

/-- Scalar and table fields of each actual local row. The raw fields and computed
sweep parameters share a polynomial upper bound `V`, but can have different maxima. -/
theorem visit_fields (D : Directory) (params : Params) {p U V : ℕ} (h : RawFields D p U)
    (hu : U ≤ V) (hp : ParamsBound params V) (i : Fin D.blocks.length)
    (k : Fin D.blocks[i].factors.length) :
    let b := visit (params,D) i D.blocks[i]
    let x : Input := ((prepare b).1,k.val,D.blocks[i].factors[k])
    ScalarFields x ((V+1)^3) ∧ FactorFields x.2.2 ((V+1)^3) := by
  have hb : D.blocks[i] ∈ D.blocks := List.getElem_mem ..
  have hw := resolved_fields D h D.blocks[i] hb
  have hn := resolved_factor_count D h D.blocks[i] hb
  have hstart := (resolved_prefix_le D h i).trans (Nat.pow_le_pow_left (hu.trans (Nat.le_succ _)) 3)
  have hV : V ≤ (V+1)^3 := (Nat.le_succ V).trans (Nat.le_self_pow (by decide) _)
  have hU := hu.trans hV
  obtain ⟨h₁,h₂,h₃⟩ := hp
  exact ⟨⟨h₁.trans hV,h₂.trans hV,h₃.trans hV,hstart,hw.1.trans hU,hw.2.2.1.trans hU,
      hn.trans hU,k.isLt.le.trans (hn.trans hU)⟩,
    factorFields_mono (hw.2.2.2 _ (List.getElem_mem ..)) hU⟩

/-- Three scalar parameters add one binary-width term to the combined box span. -/
theorem sweepSpan_static_le (D : Directory) (p : ℕ) (params : Params) {A M U B j n : ℕ}
    (hs : D.StaticBounds A M) (hstore : storedMass D ≤ A*(M+1)^2) (h : RawFields D p U)
    (hu : U ≤ B*(n+2)^j) (hp : ParamsBound params (B*(n+2)^j)) :
    sweepSpan (params,D)+1 ≤ (300*(8*A+4)+8*A+8)*(B.size+j+1)*(M+1)^2*(n.size+1) := by
  obtain ⟨h₁,h₂,h₃⟩ := hp
  let V := (B.size+j+1)*(n.size+1)
  have bound (x : ℕ) (hx : x ≤ B*(n+2)^j) : x.size+1 ≤ V := by
    have hb := CellMacro.Generator.size_of_polynomial_field hx
    dsimp [V]
    rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
    have := Nat.le_mul_of_pos_right B.size (by omega : 0 < n.size+1)
    omega
  have hP : (paramsCode params).length+1 ≤ 8*V := by
    have ha := bound _ h₁
    have hb := bound _ h₂
    have hc := bound _ h₃
    simp only [paramsCode,ExactQuantumFactoring.BitStackProgram.prodCode,
      ExactQuantumFactoring.BitStackProgram.pairBits_length,Nat.size_eq_bits_len]
    omega
  have hspan := blockSpan_static_le D p hs hstore h hu
  have hv : V ≤ V*(M+1)^2 := Nat.le_mul_of_pos_right _ (by positivity)
  change (paramsCode params).length+blockSpan D+1 ≤ _
  calc _ ≤ 8*V+(300*(8*A+4)+8*A)*(B.size+j+1)*(M+1)^2*(n.size+1) := by omega
       _ ≤ 8*(V*(M+1)^2)+(300*(8*A+4)+8*A)*(B.size+j+1)*(M+1)^2*(n.size+1) := by gcongr
       _ = _ := by dsimp [V]; ring

end Local
end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
