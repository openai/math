import OAI.Computability.BorderVNP.PackedDirectoryBits

/-! # Row-major candidate indices in the populated delivery table -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

/-- Arithmetic index of one private bundle/site and one of its two tail pieces. -/
def privateIndex (j k : ℕ) := 2*j+k

/-- Arithmetic index of a live delivery piece in team, processor, field and site order. -/
def Layout.liveIndex (d : Layout) (t p f k : ℕ) :=
  2*d.entries + (d.literal/d.block+2)*(d.fields*(d.processors*t+p)+f)+k

private theorem pair_index_lt {n m i j : ℕ} (hi : i < n) (hj : j < m) : m*i+j < n*m := by
  have h := Nat.mul_le_mul_left m (show i+1 ≤ n from hi)
  rw [Nat.mul_succ] at h
  rw [Nat.mul_comm n m]
  omega

/-- Every private pair of indices decodes to its actual candidate, in its prefix of
the table. -/
theorem Layout.row_privateIndex (d : Layout) (pp lp : ℕ → ℕ × ℕ) (j : Fin d.entries) (k : Fin 2) :
    privateIndex j k < d.candidates ∧ d.row pp lp (privateIndex j k) = d.privateRow pp j k := by
  have h := pair_index_lt j.isLt k.isLt
  rw [Nat.mul_comm d.entries 2] at h
  refine ⟨h.trans_le (Nat.le_add_right ..),?_⟩
  simp only [Layout.row,privateIndex,h,ite_true,Nat.mul_add_div (by decide : 0 < 2),
    Nat.div_eq_of_lt k.isLt,Nat.add_zero,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt k.isLt]

/-- Every legal team, processor, field and intersected-site step decodes to that same
live-field candidate in the public directory. -/
theorem Layout.row_liveIndex (d : Layout) (pp lp : ℕ → ℕ × ℕ) (t : Fin d.teams) (p : Fin d.processors)
    (f : Fin d.fields) (k : Fin (d.literal/d.block+2)) :
    d.liveIndex t p f k < d.candidates ∧ d.row pp lp (d.liveIndex t p f k) = d.liveRow lp t p f k := by
  have h₁ := pair_index_lt t.isLt p.isLt
  have h₂ := pair_index_lt h₁ f.isLt
  have h₃ := pair_index_lt h₂ k.isLt
  refine ⟨?_,?_⟩
  · unfold liveIndex candidates
    omega
  · have hn : ¬ d.liveIndex t p f k < 2*d.entries := by unfold liveIndex; omega
    rw [Layout.row,ite_eq_right hn]
    simp only [liveIndex,Nat.add_assoc,Nat.add_sub_cancel_left,
      Nat.mul_add_div (Nat.zero_lt_of_lt k.isLt),Nat.mul_add_div (Nat.zero_lt_of_lt f.isLt),
      Nat.mul_add_div (Nat.zero_lt_of_lt p.isLt),Nat.div_eq_of_lt k.isLt,Nat.div_eq_of_lt f.isLt,
      Nat.div_eq_of_lt p.isLt,Nat.add_zero,Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt k.isLt,
      Nat.mod_eq_of_lt f.isLt,Nat.mod_eq_of_lt p.isLt]

/-- The compact table contains precisely the nonempty rows at publicly enumerated
candidate positions. -/
theorem Layout.mem_directory_iff (d : Layout) (pp lp : ℕ → ℕ × ℕ) (r : Row) :
    r ∈ d.directory pp lp ↔ ∃ i < d.candidates, d.row pp lp i = r ∧ 0 < r.width := by
  simp only [directory,List.mem_filter,List.mem_map,List.mem_range,decide_eq_true_eq]
  aesop

/-- Every private bit in the concatenation has a populated record carrying it from its
actual reserved processor tail to its receiving slot. -/
theorem Layout.private_delivered (d : Layout) (pp lp : ℕ → ℕ × ℕ) (j : Fin d.entries)
    (ht : 0 < d.literal/2) (hs : d.description ≤ d.literal/2) (bit : Fin d.description) :
    ∃ r ∈ d.directory pp lp, ∃ e < r.width,
      r.cell = (pp j).1 ∧ r.slot+e = (pp j).2+bit ∧
      (r.team*d.processors+r.processor)*(d.literal/2)+(r.offset+e-(d.literal-d.literal/2)) =
        j.val*d.description+bit := by
  obtain ⟨k,⟨e,he,hc,hd,hsrc⟩,_⟩ := d.private_bit pp j ht hs bit
  obtain ⟨hindex,hrow⟩ := d.row_privateIndex pp lp j k
  exact ⟨_,(d.mem_directory_iff ..).mpr ⟨_,hindex,hrow,Nat.zero_lt_of_lt he⟩,e,he,hc,hd,hsrc⟩

/-- Every processor pin, including the extra substituted pin field, reaches its original
site-block slot through an actually populated interval. -/
theorem Layout.live_delivered (d : Layout) (pp lp : ℕ → ℕ × ℕ) (t : Fin d.teams) (p : Fin d.processors)
    (f : Fin d.fields) (hb : 0 < d.block) (bit : Fin d.literal) :
    let pos := p.val*d.stride+f.val*(d.literal+(d.teams-1)*d.link)+bit
    let dest := lp (t.val*d.sites+pos/d.block)
    ∃ r ∈ d.directory pp lp, ∃ e < r.width, r.team = t.val ∧ r.processor = p.val ∧
      r.field = f.val ∧ r.offset+e = bit.val ∧ r.cell = dest.1 ∧ r.slot+e = dest.2+pos%d.block := by
  obtain ⟨k,⟨e,he,ho,hc,hd⟩,_⟩ := d.live_bit lp t p f hb bit
  obtain ⟨hindex,hrow⟩ := d.row_liveIndex pp lp t p f k
  exact ⟨_,(d.mem_directory_iff ..).mpr ⟨_,hindex,hrow,Nat.zero_lt_of_lt he⟩,e,he,rfl,rfl,rfl,ho,hc,hd⟩

end Packing.Directory

end BorderVNP
end Computability
end OAI
