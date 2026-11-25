import OAI.Hierarchy.DescentPackedIssuedFallback
import OAI.Hierarchy.DescentFallbackItemSelect

namespace OAI
/-! # Exact selection of an old item in every reached fallback cell -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentIssuedFallbackPanel DescentSharedCableNames.Stage DescentGL DescentColonies DescentChosenRouter
open DescentResetAttachments StarKeys DescentTreePrefixIntervals DescentContactTree DescentRouterSlots
open DescentPackedFallbackTree
open DescentFallbackItemSelect DescentContactTree
open scoped Classical BigOperators
noncomputable section
variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k i m g h C Ht : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε J V k) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃J×Block k) (native : W.graph.Edge↪ℕ)
variable (Z : ResetInput (F:=F) (W.granular A.grainCount (A.z*G.b) (A.grainCount_fit S ready))
    (q*A.wire) ε h C Ht) (T : ResetInput.Terminals (F:=F) Z)
variable (frame : ResetInput.SourceFrame (F:=F) (V:=V) (k:=m) Z T (fun u=>(A.pos u).2)
    (StarKeys.filled W.graph A.pos A.block digits) A.hub g)
local notation "R" => Z.placement
local notation "E" => Grain A


local notation "slots" => 2^(m-T.commonDepth)*(2*A.cap)

local notation "treeBook" => Z.placement.fallbackBook
set_option quotPrecheck false in
local notation "dest" => fun (s : Bool) (t : Z.Fallback) => (Z.placement.fallbackBook s t).codes
local notation "item" => fun (s : Bool) (t : Z.Fallback) =>
  DescentRouterSlots.Item Z.placement.contact Z.placement.owner s (Sum.inr t)
local notation "spatial" => fun (s : Bool) (t : Z.Fallback) =>
  DescentFixedNamedContact.code (dest s t) (DescentRouterSlots.link Z.placement.contact Z.placement.owner s (Sum.inr t))
local notation "row" => fun (s : Bool) (e : Grain A) =>
  finProdFinEquiv (localAddress (c:=T.commonDepth) A native S ready digits frame.basis s e)

private theorem list_path_read {d₀ : ℕ} (a : DescentTreePrefixIntervals.Bits d₀) (l : ℕ) (it : DescentFallbackItemSelect.Item)
    (live : it.leaf=some l) : inCell Ht (List.ofFn a) it=true ↔
      d₀≤Ht ∧ start Ht a≤l ∧ l<stop Ht a := by
  have pair := (List.equivSigmaTuple (α:=Bool)).apply_symm_apply
    (⟨d₀,a⟩ : Σ n, Fin n → Bool)
  let valid (p : Σ n, Fin n → Bool) := p.1 ≤ Ht ∧ start Ht p.2 ≤ l ∧ l < stop Ht p.2
  simp only [inCell,live,decide_eq_true_eq]
  exact Iff.of_eq (congrArg valid pair)

private theorem seen_in_cell (s : Bool) (t : Z.Fallback) (depth : ℕ)
    (ok : depth≤(treeBook s t).height) (a : DescentTreePrefixIntervals.Bits depth)
    (it : Fin slots→DescentFallbackItemSelect.Item) (measured : ∀j,(it j).leaf=
      (leafPanel A S ready digits native Z T frame s t j).map Fin.val) (j : Fin slots) :
    j∈rows Ht (List.ofFn a) it ↔ ∃e : Cell (spatial s t) depth a, row s e.val.val=j := by
  classical
  let box : (Fin (2^(m-T.commonDepth)) × Fin (2*A.cap)) ≃ Fin slots := finProdFinEquiv
  let addr (e : Grain A) := localAddress (c:=T.commonDepth) A native S ready digits frame.basis s e
  let panelAt := fallbackPanel A S ready digits native Z T frame s t
  let p := panelAt (box.symm j)
  have recover (u : item s t) (eqn : box (addr u.val) = j) : p = some u.val :=
    (congrArg panelAt ((congrArg box.symm eqn).symm.trans (box.symm_apply_apply _))).trans
      (fallbackPanel_at A S ready digits native Z T frame s t u.val u.property)
  have leafAt := measured j
  change (it j).leaf=(p.bind (arrivedLeaf A S ready Z T s t)).map Fin.val at leafAt
  have hw:=(T.bookHeight s t)
  have locate (e : item s t) :
      cut ok (dest s t (DescentRouterSlots.link (R).contact (R).owner s (Sum.inr t) e))=
        prefixAt (spatial s t) depth e := by
    funext k
    have lt : k.val<(treeBook s t).height:=lt_of_lt_of_le k.isLt ok
    simp [cut,prefixAt,DescentFixedNamedContact.code,lt,Fin.castLE]
  cases orig : p with
  | none=>
    have empty : (it j).leaf=none:=by simpa [orig] using leafAt
    constructor
    · simp [rows,inCell,empty]
    · rintro ⟨e,eqn⟩
      have impossible := orig.symm.trans (recover e.val eqn)
      cases impossible
  | some e=>
    have occ:=fallbackPanel_sound A S ready digits native Z T frame (s:=s) (t:=t) (j:=box.symm j) (e:=e) orig
    let u : item s t:=⟨e,occ.1⟩
    let x:=dest s t (DescentRouterSlots.link (R).contact (R).owner s (Sum.inr t) u)
    have live : (it j).leaf=some (start Ht x):=by
      refine leafAt.trans ?_
      rw [orig]
      change (arrivedLeaf A S ready Z T s t e).map Fin.val = some (start Ht x)
      rw [arrivedLeaf, dite_eq_left occ.1]; rfl
    have adr : row s e=j:=(congrArg box occ.2.symm).trans (box.apply_symm_apply j)
    have rowHit : j ∈ rows Ht (List.ofFn a) it ↔ cut ok x = a := by
      simp only [rows,Finset.mem_filter,Finset.mem_univ,true_and]
      exact (list_path_read (Ht:=Ht) a _ (it j) live).trans
        ⟨fun h => (member ok hw x a).mp h.2, fun eqn => ⟨ok.trans hw,(member ok hw x a).mpr eqn⟩⟩
    constructor
    · intro inside
      exact ⟨⟨u,(locate u).symm.trans (rowHit.mp inside)⟩,adr⟩
    · rintro ⟨e',eqn⟩
      have same : e'.val=u := Subtype.ext (Option.some.inj ((recover e'.val eqn).symm.trans orig))
      exact rowHit.mpr ((locate u).trans (same ▸ e'.property))

/-- Every old item in this particular tree cell occurs at one of the bounded
    signed panel addresses and every occupied address has exactly one old item. -/
def fallbackCellEquiv (s : Bool) (t : Z.Fallback) (depth : ℕ)
    (ok : depth≤(treeBook s t).height) (a : DescentTreePrefixIntervals.Bits depth)
    (it : Fin slots→DescentFallbackItemSelect.Item) (measured : ∀j,(it j).leaf=
      (leafPanel A S ready digits native Z T frame s t j).map Fin.val) :
    Cell (spatial s t) depth a ≃ ↥(rows Ht (List.ofFn a) it) := by
  classical
  let position (u : Cell (spatial s t) depth a) : ↥(rows Ht (List.ofFn a) it) :=
    ⟨row s u.val.val,(seen_in_cell A S ready digits native Z T frame s t depth ok a it measured _).mpr ⟨u,rfl⟩⟩
  refine Equiv.ofBijective position ⟨?_,?_⟩
  · intro x y eqn
    have packed : row s x.val.val = row s y.val.val := congrArg Subtype.val eqn
    have xy := finProdFinEquiv.injective packed
    have x0:=fallbackPanel_at A S ready digits native Z T frame s t x.val.val x.val.property
    have y0:=fallbackPanel_at A S ready digits native Z T frame s t y.val.val y.val.property
    rw [xy] at x0
    exact Subtype.ext (Subtype.ext (Option.some.inj (x0.symm.trans y0)))
  · intro j
    obtain ⟨e,e'⟩:=(seen_in_cell A S ready digits native Z T frame s t depth ok a it measured j.val).mp j.property
    exact ⟨e,Subtype.ext e'⟩

/-- The true node index (chronological cell rank times batches, plus batch)
    reads back the exact old item's slot, including cells with a single item. -/
theorem flattened_item {N : ℕ} (key : E↪Fin N) (s : Bool) (t : Z.Fallback) (depth : ℕ)
    (ok : depth≤(treeBook s t).height) (a : DescentTreePrefixIntervals.Bits depth)
    (it : Fin slots→DescentFallbackItemSelect.Item) (measured : ∀j,(it j).leaf=
      (leafPanel A S ready digits native Z T frame s t j).map Fin.val)
    (chronological : ∀i j : Cell (spatial s t) depth a,
      DescentFallbackItemSelect.before it (row s i.val.val) (row s j.val.val) ↔ key i.val.val<key j.val.val)
    (e : Cell (spatial s t) depth a) (m₀ : ℕ) (batch : Fin m₀) :
    let printed := (Finset.univ.filter (fun j : Cell (spatial s t) depth a=>key j.val.val<key e.val.val)).card*m₀+batch.val
    select it (rows Ht (List.ofFn a) it) (printed/m₀)=some (row s e.val.val) := by
  let equiv:=fallbackCellEquiv A S ready digits native Z T frame s t depth ok a it measured
  let old: (Cell (spatial s t) depth a)↪Fin N :=
    (Function.Embedding.subtype _).trans ((Function.Embedding.subtype _).trans key)
  have rankEq:=rank_of_equiv it _ equiv old chronological e
  have get := select_nth it _ (equiv e).property m₀ batch
  rw [rankEq] at get
  exact get

end
end Hierarchy.DescentSixParty.GroupStage

end OAI
