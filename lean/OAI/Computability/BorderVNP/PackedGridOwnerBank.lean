import OAI.Computability.BorderVNP.PackedGridWitnessUse

/-! # Physical private bank addresses of the chosen grid term's fine assignments -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.GridBoxes

open Crossing CellSparse CellAddresses Diagonal.CellEntries
open scoped Classical
variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    {Cell Q : Type} [Fintype Cell] [DecidableEq Cell]
    (cell : N.Site → Cell) (position : Cell → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (hidden : ∀ i, N.InsideAssignment cell i) {src dst : Q → Cell} {H : ℕ}
    (packing : (N.cellNetwork cell position).ChannelPacking src dst H)
    {m n : ℕ} (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- Public supplied cable subwords and external inputs in one actual private cell. -/
noncomputable def publicWords (c : Cell) (a : {q : Q // src q = c ∨ dst q = c} → Fin H → Bool)
    (x : ∀ p : {p : P // cell (N.attach p) = c}, Fin (bits p.val) → Bool) :
    ∀ u : Supplied N cell c, Fin (suppliedWidth N cell c u) → Bool
  | .inl e, i => a ⟨packing.channel e.val, e.property.imp
        ((packing.src_eq e.val).trans) ((packing.dst_eq e.val).trans)⟩ (packing.address ⟨e.val,i⟩).2
  | .inr p, i => x p i

/-- The actual one-copy storage of the chosen seed term: guessed internal words,
followed by the corresponding actual public boundary subwords. -/
noncomputable def physicalBits (c : Cell) (a : {q : Q // src q = c ∨ dst q = c} → Fin H → Bool)
    (x : ∀ p : {p : P // cell (N.attach p) = c}, Fin (bits p.val) → Bool) : Fin (stride N cell c) → Bool :=
  copyBits N cell c ((guessedWords N cell c edgeID).symm (hidden c))
    ((suppliedWords N cell c edgeID portID).symm (publicWords cell position packing c a x))

/-- Each address read by the actual sparse fine-site descriptor sees precisely
the wire or argument named by the fixed grid term at that vertex. -/
theorem accepts_ownerRead (rules : ∀ v, Rule N v) (v : N.Site) (a x) (bank : ℕ → Bool) (off copy : ℕ)
    (aligned : ∀ i, bank (off+i.val) = physicalBits cell position hidden packing edgeID portID (cell v) a x i) :
    accepts N cell (cell v) edgeID portID ⟨v,rfl⟩ bank off copy (rules v) =
      ownerRead cell position hidden packing (guard rules (fun p => bank (p.atBit copy 0))) v a x := by
  let c := cell v
  let values := publicWords cell position packing c a x
  let gs := (guessedWords N cell c edgeID).symm (hidden c)
  let xs := (suppliedWords N cell c edgeID portID).symm values
  have gx (e : N.InsideEdge cell c) (k : Fin (N.width e.val)) :
      guessedWords N cell c edgeID gs e k = hidden c e k :=
    congrFun (congrFun ((guessedWords N cell c edgeID).apply_symm_apply (hidden c)) e) k
  have sx (u : Supplied N cell c) (k : Fin (suppliedWidth N cell c u)) :
      xs (suppliedOrdinal N cell c edgeID portID u k) = values u k :=
    congrFun (congrFun ((suppliedWords N cell c edgeID portID).apply_symm_apply values) u) k
  rw [accepts_passes]
  unfold ownerRead fineFactor guard
  apply congrArg (fun read => (rules v).passes read (fun p => bank (p.atBit copy 0)))
  funext l
  rw [aligned]
  rcases l with ⟨e,k⟩ | ⟨p,k⟩
  · simp only [physicalBits,lane,copyBits,Equiv.symm_apply_apply,readLane]
    by_cases h : cell (N.src e.val) = cell (N.dst e.val)
    · simp only [wire,h,dite_true]
      apply gx
    · simp only [wire,h,dite_false,Sum.elim_inr]
      exact sx (.inl _) _
  · simp only [physicalBits,lane,copyBits,Equiv.symm_apply_apply,Sum.elim_inr,readLane,port]
    exact sx (.inr _) _

end Packing.GridBoxes

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes Diagonal.CellEntries GridPlacement Cover TeamContraction
open ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar
open scoped Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    {Gadget : Type}

/-- Use the same equality instance as the actual conditioned deck-grid table. -/
noncomputable local instance ownerBankDeckEq : DecidableEq (Fin q → Deck (depth+2)) := Classical.decEq _

/-- All true fine verifier sites, including the equality sites on its chosen paths. -/
noncomputable abbrev routedFine := (wiredFine G d D W.trees).subdivide (wireRoutes position W.route)

/-- The named physical weight vertex remains an original site after subdivision. -/
noncomputable abbrev routedPowerSite (j : WeightSites n g r d) : (W.routedFine position).Site :=
  .inl (BooleanLayout.weightSite (wiredCircuit G d W.trees) (wiredWeight (Edge := Edge) d) j)

/-- The exact sparse Boolean and unary rules on the retained physical fine vertices. -/
noncomputable abbrev routedRules (report : WeightSites n g r d → Port) :=
  routedRule (wiredFine G d D W.trees) (wireRoutes position W.route) (W.originalRule report)

/-- Reading the physical report lane of a passing sparse site gives exactly the
selected bit of the corresponding named seed term. The fine data slab can start
at any offset in the surrounding bank, for any copy. -/
theorem seed_report_bank (z : W.Hidden position) (report : WeightSites n g r d → Port) (j : WeightSites n g r d)
    {m p : ℕ} (edgeID : (W.routedFine position).Edge ↪ Fin m) (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p)
    (bank : ℕ → Bool) (off copy : ℕ) (a x)
    (hp : W.seedTags (Gadget := Gadget) position z ((W.seedWords (Gadget := Gadget) position z).site ((),j)) a x ≠ 0)
    (aligned : ∀ i, bank (off+i.val) = physicalBits (cell position W.route) position z
      (routedPacking position W.route (fun _ => le_rfl)) edgeID portID (cell position W.route (W.routedPowerSite position j)) a x i)
    (ok : accepts (W.routedFine position) (cell position W.route) (cell position W.route (W.routedPowerSite position j))
      edgeID portID ⟨W.routedPowerSite position j,rfl⟩ bank off copy (W.routedRules position report (W.routedPowerSite position j)) = true) :
    bank ((report j).atBit copy 0) =
      (W.seedWords (Gadget := Gadget) position z).selected ((W.seedWords (Gadget := Gadget) position z).site ((),j)) a x ((),j) :=
  W.seed_report position report z j (fun p => bank (p.atBit copy 0)) a x hp
    ((accepts_ownerRead (cell position W.route) position z (routedPacking position W.route (fun _ => le_rfl))
      edgeID portID (W.routedRules position report) (W.routedPowerSite position j) a x bank off copy aligned).symm.trans ok)

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
