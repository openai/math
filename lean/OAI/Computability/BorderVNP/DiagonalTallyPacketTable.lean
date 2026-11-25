import OAI.Computability.BorderVNP.DiagonalTallyPacketDigits

/-! # The fixed directory of all cube table positions

The input to the lookup has a fixed-width selector, a fixed-width vertex and the
padded digits of the selected local row. Padding uses literal zero. Consequently
one finite integer table suffices for all packets and every input length.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Tally

open DiagonalTallyGather VPVNP.BurstRAM VPVNP.TapeWord

variable {n b h K s : ℕ}

private theorem exists_width_bound {α : Type*} [Fintype α] (f : α → ℕ) : ∃ M, ∀ x, f x ≤ M :=
  ⟨Finset.univ.sup f,fun x => Finset.le_sup (f := f) (Finset.mem_univ x)⟩

private noncomputable def rowBound (n b h K s : ℕ) :
    {M : ℕ // ∀ (u : Selector n K h) (v : Vertex (n+1)), rowWidth u v b s ≤ M} :=
  let ex := exists_width_bound (fun z : Selector n K h × Vertex (n+1) => rowWidth z.1 z.2 b s)
  ⟨ex.choose,fun u v => ex.choose_spec (u,v)⟩

/-- Fixed width for any selected local row in this cube identity. -/
noncomputable def maximumWidth (n b h K s : ℕ) : ℕ := (rowBound n b h K s).val

theorem rowWidth_le (u : Selector n K h) (v : Vertex (n+1)) (b s : ℕ) :
    rowWidth u v b s ≤ maximumWidth n b h K s := (rowBound n b h K s).property u v

/-- Literal code bits in decreasing significance order, for a fixed finite set. -/
noncomputable def prefixDigits {α : Type*} [Fintype α] (order : α ≃ Fin (Fintype.card α))
    (a : α) : List Bool :=
  (wordBits (⟨(order a).val,(order a).isLt.trans_le (Nat.le_pow_clog (by decide) _)⟩ :
    Word (Nat.clog 2 (Fintype.card α)))).reverse

/-- The bit count of every selector prefix is exactly the manuscript's §8 selector cost. -/
theorem selector_prefix_width (n K h : ℕ) :
    Nat.clog 2 (Fintype.card (Selector n K h)) =
      VPVNP.MotifWidths.selectorBits K (Fintype.card (Edge (n+1))) h := by
  simp [Selector,VPVNP.MotifWidths.selectorBits]

/-- All raw bits named by the native selected-ID lookup at this vertex. -/
noncomputable def lookupDigits
    (sel : Selector n K h ≃ Fin (Fintype.card (Selector n K h)))
    (vertex : Vertex (n+1) ≃ Fin (Fintype.card (Vertex (n+1)))) (e : TableEntry n b h K s) : List Bool :=
  prefixDigits sel e.1 ++ prefixDigits vertex e.2.1 ++
    List.replicate (maximumWidth n b h K s - rowWidth e.1 e.2.1 b s) false ++
      physicalDigits e.1 e.2.1 e.2.2

private theorem readDigits_shift (a : ℕ) (bs : List Bool) :
    readDigits a bs = a*2^bs.length+readDigits 0 bs := by
  induction bs generalizing a with
  | nil => simp [readDigits]
  | cons b bs ih =>
    change readDigits (a+a+b.toNat) bs = a*2^(bs.length+1)+readDigits (0+0+b.toNat) bs
    rw [ih,ih (0+0+b.toNat),pow_succ]; ring

private theorem readDigits_append (a : ℕ) (xs ys : List Bool) :
    readDigits a (xs++ys) = readDigits a xs*2^ys.length+readDigits 0 ys := by
  rw [readDigits,List.foldl_append]
  exact readDigits_shift _ _

private theorem readDigits_zeros (len : ℕ) : readDigits 0 (List.replicate len false) = 0 := by
  induction len with
  | zero => rfl
  | succ n ih => simpa [List.replicate_succ,readDigits] using ih

private theorem readDigits_prefix {α : Type*} [Fintype α] (order : α ≃ Fin (Fintype.card α)) (a : α) :
    readDigits 0 (prefixDigits order a) = (order a).val := by
  rw [prefixDigits,readDigits_reverse,value_wordBits]

/-- Position in the finite directory indexed by selector, vertex and local row. -/
noncomputable def lookupIndex
    (sel : Selector n K h ≃ Fin (Fintype.card (Selector n K h)))
    (vertex : Vertex (n+1) ≃ Fin (Fintype.card (Vertex (n+1)))) (e : TableEntry n b h K s) : ℕ :=
  ((sel e.1).val*2^Nat.clog 2 (Fintype.card (Vertex (n+1))) + (vertex e.2.1).val) *
    2^maximumWidth n b h K s + (rowIndex e.1 e.2.1 b s e.2.2).val

/-- Native high-to-low accumulation of the actual argument bits gives the precise table address. -/
theorem lookupDigits_index
    (sel : Selector n K h ≃ Fin (Fintype.card (Selector n K h)))
    (vertex : Vertex (n+1) ≃ Fin (Fintype.card (Vertex (n+1)))) (e : TableEntry n b h K s) :
    readDigits 0 (lookupDigits sel vertex e) = lookupIndex sel vertex e := by
  have h := rowWidth_le e.1 e.2.1 b s
  have hl : (physicalDigits e.1 e.2.1 e.2.2).length = rowWidth e.1 e.2.1 b s := by
    simp [physicalDigits]
  rw [lookupDigits,readDigits_append,readDigits_append,readDigits_append,
    readDigits_prefix,readDigits_prefix,readDigits_zeros,physicalDigits_index,
    Nat.add_zero,List.length_replicate,hl,lookupIndex]
  rw [Nat.mul_assoc,← pow_add,Nat.sub_add_cancel h]
  simp [prefixDigits]

private theorem split_digits {x y i j cap : ℕ} (hi : i < cap) (hj : j < cap)
    (he : x*cap+i = y*cap+j) : x = y ∧ i = j := by
  have hc : 0 < cap := Nat.zero_lt_of_lt hi
  have rem := congrArg (· % cap) he
  simp [Nat.add_mod,Nat.mod_eq_of_lt hi,Nat.mod_eq_of_lt hj] at rem
  exact ⟨Nat.eq_of_mul_eq_mul_right hc (Nat.add_right_cancel (rem ▸ he)),rem⟩

/-- Two distinct table positions never alias, even if the table assigns them equal
scalars or the supplied edge has width zero. -/
theorem lookupIndex_injective
    (sel : Selector n K h ≃ Fin (Fintype.card (Selector n K h)))
    (vertex : Vertex (n+1) ≃ Fin (Fintype.card (Vertex (n+1)))) :
    Function.Injective (lookupIndex (b := b) (s := s) sel vertex) := by
  rintro ⟨u,v,x⟩ ⟨t,z,y⟩ he
  have width (u : Selector n K h) (v : Vertex (n+1)) (x : Row (b := b) (s := s) u v) :
      (rowIndex u v b s x).val < 2^maximumWidth n b h K s :=
    (rowIndex u v b s x).isLt.trans_le (Nat.pow_le_pow_right (by decide) (rowWidth_le u v b s))
  obtain ⟨hp,hr⟩ := split_digits (width u v x) (width t z y) he
  have vertexBound (v : Vertex (n+1)) :=
    (vertex v).isLt.trans_le (Nat.le_pow_clog (by decide : 1 < 2) _)
  obtain ⟨hu,hv⟩ := split_digits (vertexBound v) (vertexBound z) hp
  have eu : u = t := sel.injective (Fin.ext hu)
  have ev : v = z := vertex.injective (Fin.ext hv)
  subst t; subst z
  have er := (rowIndex u v b s).injective (Fin.ext hr)
  subst y; rfl

/-- A fixed table of small natural IDs for the physical cube identity. It depends on the
identity and the two finite orders, and can be shared by all dynamic packet instances. -/
noncomputable def idTable
    (sel : Selector n K h ≃ Fin (Fintype.card (Selector n K h)))
    (vertex : Vertex (n+1) ≃ Fin (Fintype.card (Vertex (n+1))))
    (id : TableEntry n b h K s → ℕ) (k : ℕ) : ℕ := by
  classical
  exact if he : ∃ e, lookupIndex sel vertex e = k then id he.choose else 0

/-- Reading that table with the exact incident arguments retrieves their designated ID. -/
theorem idTable_lookup
    (sel : Selector n K h ≃ Fin (Fintype.card (Selector n K h)))
    (vertex : Vertex (n+1) ≃ Fin (Fintype.card (Vertex (n+1))))
    (id : TableEntry n b h K s → ℕ) (e : TableEntry n b h K s) :
    idTable sel vertex id (readDigits 0 (lookupDigits sel vertex e)) = id e := by
  classical
  let ex : ∃ q : TableEntry n b h K s, lookupIndex sel vertex q = lookupIndex sel vertex e := ⟨e,rfl⟩
  rw [lookupDigits_index,idTable,dite_eq_left ex]
  exact congrArg id (lookupIndex_injective sel vertex ex.choose_spec)

end Cube.Tally

end BorderVNP
end Computability
end OAI
