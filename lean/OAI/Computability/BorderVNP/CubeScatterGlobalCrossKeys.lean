import OAI.Computability.BorderVNP.CubeScatterRowCrossKeys
import OAI.Computability.BorderVNP.CubeScatterAssignment

/-! # Reassembling every strict row into one global shared-cut assignment -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Physical Physical.Owned VPVNP.MotifBase

variable {n d blocks h K : ℕ}

/-- The active bits crossing one grouping cut: selected-axis supply lanes
and singleton slots with different endpoint symbols on this axis. -/
abbrev GlobalCrossBit (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) :=
  (Σ p : Packet n d blocks, CrossLane (select p) i s) ⊕
    {z : SingleSlot n d blocks (h*b) // z.1.val.1 i ≠ z.1.val.2 i}

private def sortedSymbols (a b : Fin d) (ne : a ≠ b) : Symbols d :=
  if lt : a < b then ⟨(a,b),lt⟩ else ⟨(b,a),lt_of_le_of_ne (le_of_not_gt lt) ne.symm⟩

private theorem sortedSymbols_row (a b : Fin d) (ne : a ≠ b) :
    Sym2.mk a b = Sym2.mk (sortedSymbols a b ne).val.1 (sortedSymbols a b ne).val.2 := by
  unfold sortedSymbols
  split <;> first | rfl | exact Sym2.eq_swap

private theorem symbols_inj {x y : Symbols d} (h : Sym2.mk x.val.1 x.val.2 = Sym2.mk y.val.1 y.val.2) : x = y := by
  rcases Sym2.eq_iff.mp h with h | ⟨h₁,h₂⟩
  · exact Subtype.ext (Prod.ext h.1 h.2)
  · have lt := x.property
    rw [h₁,h₂] at lt
    exact (y.property.not_gt lt).elim

private theorem singleton_ne {b : ℕ} {i : Fin (n+1)} {sym : Symbols d} {z : SingleSlot n d blocks (h*b)}
    (row : itemRow i (.inr z : Item n d blocks (h*b)) = Sym2.mk sym.val.1 sym.val.2) : z.1.val.1 i ≠ z.1.val.2 i := by
  intro eq
  have hr : (itemRow i (.inr z : Item n d blocks (h*b))).IsDiag := Sym2.mk_isDiag_iff.mpr eq
  exact sym.property.ne (Sym2.mk_isDiag_iff.mp (row ▸ hr))

/-- Forget the row tag while retaining the complete physical bit identity. -/
def globalOfRow {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)} {sym : Symbols d} :
    RowCrossBit b s select i sym → GlobalCrossBit b s select i
  | .inl ⟨p,k⟩ => .inl ⟨p.val,k⟩
  | .inr z => .inr ⟨z.val,singleton_ne z.property⟩

private theorem same_single_row {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)}
    {x y : Symbols d} (eq : x = y) (z : SingleSlot n d blocks (h*b))
    (hx : itemRow i (.inr z : Item n d blocks (h*b)) = Sym2.mk x.val.1 x.val.2)
    (hy : itemRow i (.inr z : Item n d blocks (h*b)) = Sym2.mk y.val.1 y.val.2) :
    (⟨x,.inr ⟨z,hx⟩⟩ : Σ t, RowCrossBit b s select i t) = ⟨y,.inr ⟨z,hy⟩⟩ := by
  subst y; rfl

/-- A shared singleton chooses the increasing representative of its two symbols;
a cut supply uses the increasing symbol pair of its physical packet. -/
def globalCrossBitEquiv (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) :
    (Σ sym : Symbols d, RowCrossBit b s select i sym) ≃ GlobalCrossBit b s select i where
  toFun x := globalOfRow x.2
  invFun
    | .inl ⟨p,k⟩ => ⟨p.1.1 i,.inl ⟨⟨p,rfl⟩,k⟩⟩
    | .inr ⟨z,ne⟩ => ⟨sortedSymbols _ _ ne,.inr ⟨z,sortedSymbols_row _ _ ne⟩⟩
  left_inv := by
    rintro ⟨sym,⟨⟨p,hp⟩,k⟩ | ⟨z,hz⟩⟩
    · subst sym; rfl
    · let ne := singleton_ne hz
      have he : sortedSymbols _ _ ne = sym := symbols_inj ((sortedSymbols_row _ _ ne).symm.trans hz)
      exact same_single_row he z _ _
  right_inv := by rintro (⟨p,k⟩|⟨z,hz⟩) <;> rfl

/-- Product of the actual raw suffix types over all strict symbol rows. -/
abbrev StrictCrossWords (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) :=
  (sym : Symbols d) → {xs : List Bool // xs.length = subtotals itemRow (crossCount b s select) i (Sym2.mk sym.val.1 sym.val.2) i}

/-- A single assignment on the physical shared cut is equivalent to arbitrary
raw suffix words of the declared lengths on all strict rows simultaneously. -/
noncomputable def globalCrossEquiv (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) :
    (GlobalCrossBit b s select i → Bool) ≃ StrictCrossWords b s select i :=
  ((globalCrossBitEquiv b s select i).symm.arrowCongr (Equiv.refl Bool)).trans <|
    (Equiv.piCurry (fun (_ : Symbols d) _ => Bool)).trans (Equiv.piCongrRight (rowCrossEquiv b s select i))

/-- Each component of the global equivalence emits the native row keys in order. -/
theorem globalCrossEquiv_apply (b s : ℕ) (select : Packet n d blocks → Selector n K h) (i : Fin (n+1))
    (f : GlobalCrossBit b s select i → Bool) (sym : Symbols d) :
    ((globalCrossEquiv b s select i) f sym).val = (rowCrossKeys b s select i sym).map (fun k => f (globalOfRow k)) := rfl

/-- Native payload identity of an active cut bit. -/
def globalBitIndex {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)} :
    GlobalCrossBit b s select i → Assignment.BitIndex b s select
  | .inl ⟨p,k⟩ => .inr (.inr ⟨p,(k.1,i),k.2⟩)
  | .inr z => .inl z.val

private theorem globalBitIndex_injective {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)} :
    Function.Injective (globalBitIndex (b := b) (s := s) (select := select) (i := i)) := by
  rintro (⟨p,v,j⟩|⟨z,ne⟩) (⟨p',v',j'⟩|⟨z',ne'⟩) he <;> cases he <;> rfl

/-- The region chosen by the paper's physical routing for every shared row key. -/
theorem route_rowBit {Team : Type*} {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)}
    {sym : Symbols d} (owner : Fin d → Team) (x : RowCrossBit b s select i sym) :
    Assignment.route i owner (globalBitIndex (globalOfRow x)) = .inl (Sym2.mk sym.val.1 sym.val.2) := by
  rcases x with ⟨p,k⟩ | z
  · simp only [globalOfRow,globalBitIndex,Assignment.route,ite_true]
    exact congrArg Sum.inl ((packet_itemRow_eq_iff (width := h*b) i sym p.val).mpr p.property)
  · simp only [globalOfRow,globalBitIndex,Assignment.route,ite_eq_right (singleton_ne z.property)]
    exact congrArg Sum.inl z.property

private theorem global_of_shared {Team : Type*} {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)}
    {owner : Fin d → Team} {r : Sym2 (Fin d)} (k : Assignment.BitIndex b s select) (hr : Assignment.route i owner k = .inl r) :
    ∃ x : GlobalCrossBit b s select i, globalBitIndex x = k := by
  rcases k with z | (a | ⟨p,⟨v,j⟩,a⟩)
  · by_cases eq : z.1.val.1 i = z.1.val.2 i
    · simp [Assignment.route,eq] at hr
    · exact ⟨.inr ⟨z,eq⟩,rfl⟩
  · simp [Assignment.route] at hr
  · by_cases eq : j = i
    · subst j; exact ⟨.inl ⟨p,v,a⟩,rfl⟩
    · simp [Assignment.route,eq] at hr

/-- The key type of a strict raw row is exactly the corresponding shared fiber
of `Assignment.Choices`, including when both groups belong to one team. -/
noncomputable def rowChoiceEquiv {Team : Type*} (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (owner : Fin d → Team) (sym : Symbols d) :
    RowCrossBit b s select i sym ≃ {k : Assignment.BitIndex b s select // Assignment.route i owner k = .inl (Sym2.mk sym.val.1 sym.val.2)} := by
  refine Equiv.ofBijective (fun x => ⟨globalBitIndex (globalOfRow x),route_rowBit owner x⟩) ⟨?_,?_⟩
  · intro x y he
    have eq := globalBitIndex_injective (congrArg Subtype.val he)
    have eq' : (⟨sym,x⟩ : Σ t, RowCrossBit b s select i t) = ⟨sym,y⟩ := (globalCrossBitEquiv b s select i).injective eq
    cases eq'; rfl
  · rintro ⟨k,hk⟩
    obtain ⟨x,rfl⟩ := global_of_shared k hk
    obtain ⟨⟨row,key⟩,rfl⟩ := (globalCrossBitEquiv b s select i).surjective x
    have same : row = sym := symbols_inj (Sum.inl.inj ((route_rowBit owner key).symm.trans hk))
    subst row
    exact ⟨key,rfl⟩

/-- The unordered routing row of a shared bit, with its unique increasing representative. -/
def globalRow {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)}
    (x : GlobalCrossBit b s select i) : Symbols d := ((globalCrossBitEquiv b s select i).symm x).1

/-- Every shared bit actually routes to its reconstructed row. -/
theorem route_global {Team : Type*} {b s : ℕ} {select : Packet n d blocks → Selector n K h} {i : Fin (n+1)}
    (owner : Fin d → Team) (x : GlobalCrossBit b s select i) :
    Assignment.route i owner (globalBitIndex x) = .inl (Sym2.mk (globalRow x).val.1 (globalRow x).val.2) := by
  obtain ⟨⟨sym,k⟩,rfl⟩ := (globalCrossBitEquiv b s select i).surjective x
  simp only [globalRow,Equiv.symm_apply_apply]
  exact route_rowBit owner k

/-- The raw common-bit domain accounts for the entire shared half of the
existing physical assignment. Diagonal unordered rows have empty shared fibers. -/
noncomputable def globalSharedIndex {Team : Type*} (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (owner : Fin d → Team) : GlobalCrossBit b s select i ≃
      (Σ r : Sym2 (Fin d), {k : Assignment.BitIndex b s select // Assignment.route i owner k = .inl r}) := by
  let g (x : GlobalCrossBit b s select i) : Σ r : Sym2 (Fin d), {k : Assignment.BitIndex b s select // Assignment.route i owner k = .inl r} :=
    ⟨Sym2.mk (globalRow x).val.1 (globalRow x).val.2,globalBitIndex x,route_global owner x⟩
  refine Equiv.ofBijective g ⟨?_,?_⟩
  · intro x y hxy
    exact globalBitIndex_injective (congrArg (fun q => q.2.val) hxy)
  · rintro ⟨r,k,hr⟩
    obtain ⟨x,rfl⟩ := global_of_shared k hr
    have same : r = Sym2.mk (globalRow x).val.1 (globalRow x).val.2 := Sum.inl.inj (hr.symm.trans (route_global owner x))
    subst r
    exact ⟨x,rfl⟩

/-- The private half of the physical choices, retaining the actual owning team. -/
abbrev PrivateBitChoices {Team : Type*} (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (owner : Fin d → Team) :=
  (t : Team) → {k : Assignment.BitIndex b s select // Assignment.route i owner k = .inr t} → Bool

/-- Physical distributed choices are exactly the raw suffixes for every strict
row and the original private team bits. This includes same-owner strict rows. -/
noncomputable def choiceWordsEquiv {Team : Type*} (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (owner : Fin d → Team) : Assignment.Choices b s select i owner ≃
      StrictCrossWords b s select i × PrivateBitChoices b s select i owner := by
  let Shared := (r : Sym2 (Fin d)) → {k : Assignment.BitIndex b s select // Assignment.route i owner k = .inl r} → Bool
  let split : Assignment.Choices b s select i owner ≃ Shared × PrivateBitChoices b s select i owner :=
    ⟨fun f => (fun r => f (.inl r),fun t => f (.inr t)),fun fg r => match r with
      | .inl r => fg.1 r | .inr t => fg.2 t,
      fun f => by funext r; cases r <;> rfl,fun _ => rfl⟩
  let shared : Shared ≃ (GlobalCrossBit b s select i → Bool) :=
    (Equiv.piCurry (fun (_ : Sym2 (Fin d)) _ => Bool)).symm.trans ((globalSharedIndex b s select i owner).symm.arrowCongr (Equiv.refl Bool))
  exact split.trans ((shared.trans (globalCrossEquiv b s select i)).prodCongr (Equiv.refl _))

private theorem lookup_at_region {Team : Type*} {b s : ℕ} {select : Packet n d blocks → Selector n K h}
    {i : Fin (n+1)} {owner : Fin d → Team} (f : Assignment.Choices b s select i owner) (k : Assignment.BitIndex b s select)
    {r : Assignment.Region d Team} (eq : Assignment.route i owner k = r) : f r ⟨k,eq⟩ = Assignment.lookup f k := by
  subst r; rfl

/-- The common suffix emitted by `choiceWordsEquiv` is exactly the physical
crossing stream formed by lookup in the existing distributed assignment. -/
theorem choiceWordsEquiv_shared {Team : Type*} (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (owner : Fin d → Team) (f : Assignment.Choices b s select i owner) (sym : Symbols d) :
    (((choiceWordsEquiv b s select i owner) f).1 sym).val = commonCrossings b i sym select
      (fun p e j => Assignment.lookup f (.inr (.inr ⟨p,e,j⟩))) (fun z => Assignment.lookup f (.inl z)) := by
  rw [commonCrossings_eq_keys]
  apply List.map_congr_left
  intro x _
  let k := globalOfRow x
  change f (.inl (Sym2.mk (globalRow k).val.1 (globalRow k).val.2)) ⟨globalBitIndex k,route_global owner k⟩ = _
  rw [lookup_at_region f (globalBitIndex k) (route_global owner k)]
  cases x <;> rfl

/-- The team component of the equivalence is the original private routing fiber. -/
theorem choiceWordsEquiv_private {Team : Type*} (b s : ℕ) (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (owner : Fin d → Team) (f : Assignment.Choices b s select i owner) (t : Team) :
    ((choiceWordsEquiv b s select i owner) f).2 t = f (.inr t) := rfl

end Cube.Scatter

end BorderVNP
end Computability
end OAI
