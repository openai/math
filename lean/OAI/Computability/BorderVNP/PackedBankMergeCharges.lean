import OAI.Computability.BorderVNP.CellDirectoryMerge
import OAI.Computability.BorderVNP.PackedBankPacketFields
import OAI.Computability.BorderVNP.PackedBankBoxDirectory

/-! # Static and expanded charges for the merged crossing-bank directory

The new site fragments share the cell's final table order. Their public guard
counts depend only on the fixed profile and gadget shapes. A paid site has
one resolved box block whose factor is visited once for every paid copy.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BankCharges

open CellSparse BankPacket Crossing Shortening Shortening.StaticRows Shortening.CombiningStep
open scoped Classical
open private ordered zero ties from OAI.Computability.BorderVNP.PackedBankPacketProfiles
open private tie from OAI.Computability.BorderVNP.PackedBankPacketBox

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Exact static guard charge of a site's frozen record tape. -/
noncomputable def guardNodes (first : Fin D × Bool) (v : TemplateSite e) : ℕ :=
  Directory.recordNodes ((format e first v).2.map (RecordCode.read (fun _ => 0)))

/-- All operands that vary with the history or the relocation leave the public
guard size fixed, including the profile's selector width. -/
theorem emitted_recordNodes (first : Fin D × Bool) (v : TemplateSite e) (x : (format e first v).1 → ℕ) :
    Directory.recordNodes ((format e first v).2.map (RecordCode.read x)) = guardNodes e first v := by
  rcases v with _ | _ | ⟨i,v⟩ <;>
    simp [guardNodes,Directory.recordNodes,format,origin,terminal,Paid.rows,ordered,zero,ties,tie,
      Record.guardMassBound,RecordCode.read,Word.WidthExpr.eval,List.map_ofFn,Function.comp_def]

/-- Exact charge for the one-copy table entry stored at each seed site. -/
theorem emitted_tableNodes (position : e.Entry → ℕ) (v : TemplateSite e) :
    Directory.tableNodes (metadata e position v) = stored e v := by
  rcases v with _ | _ | ⟨i,v⟩ <;> simp [Directory.tableNodes,metadata,stored,paid_staticMass]

/-- One-copy factor sweep size at the paid sites; origin and terminal profiles
have no private factor sweeps. -/
noncomputable def sweepNodes : TemplateSite e → ℕ
  | .inl _ | .inr (.inl _) => 0
  | .inr (.inr ⟨i,v⟩) =>
    5 + 10000*((PaidBox.arity e i v+1)*(2^(PaidBox.arity e i v)+1))

private def resolve (boxes : List (List Factor)) : Record → Option BoxBlock
  | .box id base copies stride => some ⟨base,copies,stride,boxes.getD id []⟩
  | _ => none

private theorem skip_ofFn {n : ℕ} {α β : Type*} (f : α → Option β) (g : Fin n → α)
    (h : ∀ i, f (g i) = none) : (List.ofFn g).filterMap f = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro b hb
  obtain ⟨a,ha,he⟩ := List.mem_filterMap.mp hb
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  rw [h i] at he
  cases he

private theorem origin_blocks {A : ℕ} (x : SiteInput D A → ℕ) (first : Fin D × Bool)
    (boxes : List (List Factor)) :
    Directory.resolvedRows boxes ((origin m first).map (RecordCode.read x)) = [] := by
  change (_ : List Record).filterMap (resolve boxes) = _
  simp [origin,ordered,zero,ties,List.map_ofFn,Function.comp_def,RecordCode.read,resolve]
  rintro r (⟨_,rfl⟩ | ⟨_,rfl⟩ | ⟨_,rfl⟩) <;> rfl

private theorem terminal_blocks {A : ℕ} (x : SiteInput D A → ℕ) (boxes : List (List Factor)) :
    Directory.resolvedRows boxes ((terminal m).map (RecordCode.read x)) = [] := by
  change (_ : List Record).filterMap (resolve boxes) = _
  simp [terminal,ordered,zero,ties,List.map_ofFn,Function.comp_def,RecordCode.read,resolve]
  rintro r (⟨_,rfl⟩ | rfl | ⟨_,rfl⟩) <;> rfl

/-- Resolution of the sole public paid-box reference in the full cell's
directory; the bundle ties and lane equalities introduce no other block. -/
theorem paid_blocks {n : ℕ} (w : Fin n → ℕ) (x : Paid.Input n (∑ r,w r) → ℕ)
    (boxes : List (List Factor)) :
    Directory.resolvedRows boxes ((Paid.rows w).map (RecordCode.read x)) =
      [⟨x (.inl ()) + x (.inr (.inr (.inl (some none)))), x (.inr (.inr (.inl none))),
        ∑ r,w r, boxes.getD (x (.inr (.inl ()))) []⟩] := by
  change (_ : List Record).filterMap (resolve boxes) = _
  simp [Paid.read_rows,PaidBox.decode,Paid.withBoxID,Record.shift,resolve,List.map_ofFn,Function.comp_def]
  rw [skip_ofFn _ _ (fun _ => rfl),skip_ofFn _ _ (fun _ => rfl)]
  rfl

/-- The runtime operands name the site's own one-copy table in the merged list.
At paid sites they also carry the multiplicity of the selected histogram. -/
def ResolvedOperands (position : e.Entry → ℕ) (first : Fin D × Bool) (boxes : List (List Factor))
    (h : Fin e.count → ℕ) : (v : TemplateSite e) → ((format e first v).1 → ℕ) → Prop
  | .inl _, _ | .inr (.inl _), _ => True
  | .inr (.inr ⟨i,v⟩), x =>
    boxes.getD (x (.inr (.inl ()))) [] = [PaidBox.tableFactor e position i v] ∧
      x (.inr (.inr (.inl none))) = h i

/-- Static resolved sweep cost and expanded traversal count of the actual site
rows, as used in the merged cell compiler. -/
theorem emitted_blocks (position : e.Entry → ℕ) (first : Fin D × Bool) (boxes : List (List Factor))
    (j : ℕ) (h : Fin e.count → ℕ) (v : TemplateSite e) (x : (format e first v).1 → ℕ)
    (hx : ResolvedOperands e position first boxes h v x) :
    let bs := Directory.resolvedRows boxes ((format e first v).2.map (RecordCode.read x))
    Directory.blockNodes bs = sweepNodes e v ∧
      (bs.map fun b => b.copies*b.factors.length).sum = bankUses e j h v := by
  rcases v with _ | _ | ⟨i,v⟩
  · dsimp only [format]
    rw [origin_blocks (m := m) (A := e.count) x first boxes]
    exact ⟨rfl,rfl⟩
  · dsimp only [format]
    rw [terminal_blocks (m := m) (D := D) (A := e.count) x boxes]
    exact ⟨rfl,rfl⟩
  · obtain ⟨hid,hcount⟩ := hx
    dsimp only [format]
    rw [paid_blocks (PaidBox.widths (e.net i) v) x boxes,hid,hcount]
    simp [Directory.blockNodes,sweepNodes,bankUses,paid_staticMass]

open CellSparse.Packet.Source ParseBatchSort BankBoxOrdinal

/-- The stable public box-number scan establishes the lookup and count conditions
for the installed paid packet in a cell containing both inherited and paid boxes. -/
theorem ordinal_resolvedOperands {Site : Type} {s k w : ℕ}
    (position : e.Entry → ℕ) (first : Fin D × Bool) (h : Fin e.count → ℕ)
    (i : Fin e.count) (v : (e.net i).Site) (r : Fin s)
    (x : BankBoxOrdinal.Input s k w → Bool) (owner : Fin s → ℕ)
    (boxes : Fin s → List (Box Site)) (fs : Site → List Factor)
    (ho : ∀ a, ownerWord x a = owner a) (hc : ∀ a, countWord x a = (boxes a).length)
    (room : ∀ c, (table owner boxes c).length < 2^w)
    (atSite : boxes r = [.inl [PaidBox.tableFactor e position i v]]) (off : ℕ)
    (physical : Fin (Fintype.card (PaidBox.Bundle (e.net i) v)) → ℕ) :
    let id := value (fun b => (frame s k w).eval x (r,b))
    let merged := resolved owner boxes fs (owner r)
    ResolvedOperands e position first merged h (.inr (.inr ⟨i,v⟩))
      (PaidBinding.fields (PaidBox.widths (e.net i) v) (h i) off id physical) := by
  dsimp only [ResolvedOperands]
  refine ⟨?_,rfl⟩
  let j : Fin (boxes r).length := ⟨0,by simp [atSite]⟩
  have hj : (boxes r).get j = .inl [PaidBox.tableFactor e position i v] := by
    change (boxes r)[0]'j.isLt = _
    simp only [atSite,List.getElem_cons_zero]
  have he := resolved_getD x owner boxes ho hc room fs r j
  simpa only [j,Nat.add_zero,hj,factors,Sum.elim_inl,id_eq,PaidBinding.fields,
    Sum.elim_inr] using he

variable [NeZero D] {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
    {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev L := (output e p bin perm positive first q).layout

/-- Static sums of the actual resolved rows and stored tables on a tested set
of physical sites. The constants depend only on the paid identity's template. -/
theorem merged_static_tile_le (position : e.Entry → ℕ)
    (x : ∀ (_ : A) (v : TemplateSite e), (format e first v).1 → ℕ)
    (tables : A → TemplateSite e → List (List Factor))
    (hx : ∀ a v, ResolvedOperands e position first (tables a v) (q a).val v (x a v))
    (prior payload : (L e p bin perm positive first q).Site → ℕ)
    (test : (L e p bin perm positive first q).Site → Prop) :
    let rows := fun (z : Σ _ : A, TemplateSite e) =>
      (format e first z.2).2.map (RecordCode.read (x z.1 z.2))
    let mass := localRecords (L e p bin perm positive first q) false prior payload test
    let tested := fun (cost : (Σ _ : A, TemplateSite e) → ℕ) =>
      testedWidth (Sum.elim (fun _ : p.layout.Site => 0) cost) test
    tested (fun z => Directory.recordNodes (rows z)) ≤ (∑ v, guardNodes e first v) * mass ∧
      tested (fun z => Directory.blockNodes (Directory.resolvedRows (tables z.1 z.2) (rows z))) ≤
        (∑ v, sweepNodes e v) * mass ∧
      tested (fun z => Directory.tableNodes (metadata e position z.2)) ≤ (∑ v, stored e v) * mass := by
  intro rows mass tested
  have hg (z : Σ _ : A, TemplateSite e) : Directory.recordNodes (rows z) = guardNodes e first z.2 :=
    emitted_recordNodes e first _ _
  have hs (z : Σ _ : A, TemplateSite e) :
      Directory.blockNodes (Directory.resolvedRows (tables z.1 z.2) (rows z)) = sweepNodes e z.2 :=
    (emitted_blocks e position first _ 0 (q z.1).val _ _ (hx z.1 z.2)).1
  have ht (z : Σ _ : A, TemplateSite e) : Directory.tableNodes (metadata e position z.2) = stored e z.2 :=
    emitted_tableNodes e position _
  rw [funext hg, funext hs, funext ht]
  exact ⟨static_tile_le e p bin perm positive first q _ false prior payload test,
    static_tile_le e p bin perm positive first q _ false prior payload test,
    static_tile_le e p bin perm positive first q _ false prior payload test⟩

/-- The expanded paid visits are counted once per actual copy at its own
site, and fit directly in the local payload charge of the physical output. -/
theorem merged_visits_tile_le (position : e.Entry → ℕ)
    (x : ∀ (_ : A) (v : TemplateSite e), (format e first v).1 → ℕ)
    (tables : A → TemplateSite e → List (List Factor))
    (hx : ∀ a v, ResolvedOperands e position first (tables a v) (q a).val v (x a v))
    (prior payload : p.layout.Site → ℕ) (test : (L e p bin perm positive first q).Site → Prop) :
    let j := SeedIntervals.blocks p.layout bin perm m
    let visits := fun (z : Σ _ : A, TemplateSite e) =>
      ((Directory.resolvedRows (tables z.1 z.2)
        ((format e first z.2).2.map (RecordCode.read (x z.1 z.2)))).map fun b => b.copies*b.factors.length).sum
    let uses := fun (z : Σ _ : A, TemplateSite e) => bankUses e (j z.1) (q z.1).val z.2
    testedWidth (Sum.elim (fun _ : p.layout.Site => 0) visits) test ≤
      localRecords (L e p bin perm positive first q) true (Sum.elim prior (fun _ => 0)) (Sum.elim payload uses) test := by
  intro j visits uses
  have hu : visits = uses := funext fun z => (emitted_blocks e position first _ (j z.1) _ _ _ (hx z.1 z.2)).2
  rw [hu]
  have h : testedWidth (Sum.elim (fun _ : p.layout.Site => 0) uses) test ≤
      testedWidth (fun v => boxCost true (Sum.elim prior (fun _ => 0) v) (Sum.elim payload uses v)) test := by
    apply Finset.sum_le_sum
    intro v _
    by_cases ht : test v
    · simp only [ht,ite_true]
      rcases v with old | seed <;> simp [boxCost,recordCost]
    · simp only [ht,ite_false,le_refl]
  exact h.trans (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _))

end Packing.BankCharges

end BorderVNP
end Computability
end OAI
