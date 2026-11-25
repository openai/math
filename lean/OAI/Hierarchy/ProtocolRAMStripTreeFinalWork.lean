import OAI.Hierarchy.ProtocolRAMCalendarStripTrees

namespace OAI
/-! # Work of the physical strip edge decoder and broadcast trees -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open ProbeStage CoreBoard AdaptiveProbe CatalogueRows BoughtSockets StockCommit StripDirectory PortPadding

variable {z W k n q depth : ℕ}

private theorem extend_work {m D u : ℕ} {terms : Fin m → Expr} {padding : Expr}
    (small : ∀ i, (terms i).work ≤ u) (dead : padding.work ≤ u) (i : Fin D) :
    (extend terms padding i).work ≤ u := by
  unfold extend
  split
  · exact small _
  · exact dead

private theorem mate_of_primary_work {S : PurchaseSampler} {C H A B : Type*}
    (p : StripPorts S z (2^W) k C H B) (b : Board) {u : ℕ} (one : 1 ≤ u)
    (small : ∀ r : ColumnWires.Role C H (A ⊕ B) k, (p.primary b r).work ≤ u)
    (r : ColumnWires.Role C H (A ⊕ B) k) : (p.mate b r).work ≤ u := by
  cases r with
  | catalyst c j => exact small (.radius c j true)
  | radius | cross | horizontal | extra => exact one

private theorem treeTerm_work {S : PurchaseSampler} {A B : Type*}
    (p : StripPorts S z (2^W) k (Strip.TreeColumn n) (Fin n) B) (b : Board) {u : ℕ}
    (small : ∀ r : ColumnWires.Role (Strip.TreeColumn n) (Fin n) (A ⊕ B) k,
      (p.primary b r).work ≤ u) (e : Strip.TreeLink n k) : (treeTerm p b e).work ≤ u := by
  rcases e with i | ⟨c, j, side⟩
  · exact small (.horizontal i none)
  · exact small (.radius c j side)

private theorem checked_work_of_le (b : Board) (e : Expr) {u flags : ℕ}
    (small : e.work ≤ u) (flag : b.bought.flag.work ≤ flags) :
    (b.checkedEdge e).work ≤ edgeWork u flags := by
  apply (b.checkedEdge_work e).trans
  exact Nat.add_le_add_right (Nat.add_le_add
    (Nat.mul_le_mul_left 8 (Nat.add_le_add_right small 1))
    (Nat.mul_le_mul (Nat.add_le_add_right small 3) flag)) 8

private def linkWork (links u : ℕ) := 1 + links * (7 + (2*u+3)*8 + 2)

private theorem stripTree_work {S : PurchaseSampler} {A B : Type*}
    (p : StripPorts S z (2^W) k (Strip.TreeColumn n) (Fin n) B) (b : Board)
    (start rows : ℕ) {links u : ℕ} (size : Fintype.card (Strip.TreeLink n k) ≤ links)
    (small : ∀ r : ColumnWires.Role (Strip.TreeColumn n) (Fin n) (A ⊕ B) k,
      (p.primary b r).work ≤ u) :
    (stripTree p b start rows).edge.work ≤ linkWork links u ∧
      (stripTree p b start rows).sourceRow.work = 7 := by
  let h := treeHeader start rows n k
  have terms (i : Fin (Fintype.card (Strip.TreeLink n k))) :
      (((b.treeEdge (treeTerm p b ((Fintype.equivFin _).symm i))).atRow h.ballTerm)).work ≤ (2*u+3)*8 := by
    apply (substitute_work _ h.ballTerm).trans
    apply Nat.mul_le_mul_right 8
    have bound := treeTerm_work p b small ((Fintype.equivFin _).symm i)
    simp only [Board.treeEdge, Expr.work]
    omega
  exact ⟨(choose_work_bound _ 0 ((2*u+3)*8) _ h.fieldTerm terms).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ size) 1), rfl⟩

namespace StripChart
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]

local notation "N" => Stages z (2^W)
local notation "bs" => withPorts s c b G
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))

def DatePortWork (u : ℕ) : Attempt → Prop
  | .outer .. => ∀ r : PayloadRole N k, ((payloadPortsAt s c G).primary b r).work ≤ u
  | .inner p t .. => ∀ r : PurchasedRole depth k, ((boughtPortsAt s c b G p t).primary b r).work ≤ u

omit [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] in
theorem raw_port_work (a : Attempt) (u : ℕ) (one : 1 ≤ u)
    (ports : DatePortWork s c b G u a) (i : Fin D) : (rawEdge bs b.rows a i).work ≤ u := by
  cases a with
  | outer p t =>
    change (extend (payloadEdge (payloadPortsAt s c G) b) (.lit b.rows) i).work ≤ u
    exact extend_work (padding:=.lit b.rows) (fun j=>ports ((Fintype.equivFin (PayloadRole N k)).symm j)) one i
  | inner p t j l =>
    change (extend (purchaseEdge (boughtPortsAt s c b G p t) b) (.lit b.rows) i).work ≤ u
    exact extend_work (padding:=.lit b.rows) (fun j=>ports ((Fintype.equivFin (PurchasedRole depth k)).symm j)) one i

omit [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] in
private theorem mate_port_work (a : Attempt) (u : ℕ) (one : 1 ≤ u)
    (ports : DatePortWork s c b G u a) (i : Fin D) : (radiusMate s c b G a i).work ≤ u := by
  cases a with
  | outer p t =>
    unfold radiusMate
    apply extend_work
    · exact fun j=>mate_of_primary_work (payloadPortsAt s c G) b one ports ((Fintype.equivFin (PayloadRole N k)).symm j)
    · exact one
  | inner p t j l =>
    unfold radiusMate
    apply extend_work
    · exact fun j=>mate_of_primary_work (boughtPortsAt s c b G p t) b one ports ((Fintype.equivFin (PurchasedRole depth k)).symm j)
    · exact one

omit [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] in
private theorem flag_work (a : Attempt) (i : Fin D) :
    (catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a i).work ≤ 1 := by
  cases a <;> unfold catalystFlag <;> apply extend_work <;> intros <;> exact le_rfl

/-- A bound for the guarded broadcast edge, source row, catalyst mask and its mate. -/
def finalTreeWork (roles links u flags : ℕ) :=
  edgeWork (linkWork links u) flags + 7 + (1 + roles*(7+1+2)) +
    edgeWork (1 + roles*(7+u*8+2)) flags

set_option maxHeartbeats 1400000 in
theorem final_tree_work (base : ℕ) (a : Attempt) (u flags links : ℕ) (one : 1 ≤ u)
    (flag : b.bought.flag.work ≤ flags)
    (outerLinks : Fintype.card (Strip.TreeLink (PayloadStrip.edgeCount N) k) ≤ links)
    (innerLinks : Fintype.card (Strip.TreeLink (ChainStrip.edgeCount depth) k) ≤ links)
    (ports : DatePortWork s c b G u a) :
    let tree := withTrees s c b G F base a
    let bound := finalTreeWork D links u flags
    tree.edge.work ≤ bound ∧ tree.sourceRow.work ≤ bound ∧
      ∀ mask mate, tree.catalystMate = some (mask, mate) → mask.work ≤ bound ∧ mate.work ≤ bound := by
  let h := header F bs a
  have array : (originalTree s c b G F base a).edge.work ≤ linkWork links u ∧
      (originalTree s c b G F base a).sourceRow.work = 7 := by
    cases a with
    | outer p t => exact stripTree_work _ b _ _ outerLinks ports
    | inner p t j l => exact stripTree_work _ b _ _ innerLinks ports
  have original := checked_work_of_le b _ array.1 flag
  have maskBound := choose_work_bound D 0 1 _ h.fieldTerm (flag_work (z:=z) (W:=W) (k:=k) (depth:=depth) a)
  have mateBound := choose_work_bound D 0 (u*8) (fun i=>(radiusMate s c b G a i).atRow h.ballTerm) h.fieldTerm
    (fun i => (substitute_work _ h.ballTerm).trans (Nat.mul_le_mul_right 8 (mate_port_work s c b G a u one ports i)))
  have checked := checked_work_of_le b _ mateBound flag
  let B := finalTreeWork D links u flags
  change _ ≤ B ∧ _ ≤ B ∧ _
  refine ⟨original.trans ?_, ?_, ?_⟩
  · dsimp only [B,finalTreeWork]; omega
  · change (originalTree s c b G F base a).sourceRow.work ≤ B
    rw [array.2]; dsimp only [B,finalTreeWork]; omega
  · intro mask mate eqn
    rw [withTrees,forest_mask] at eqn
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj eqn)
    exact ⟨maskBound.trans (by change 1+D*(7+1+2) ≤ B; dsimp only [B,finalTreeWork]; omega),
      checked.trans (by change edgeWork (1+D*(7+u*8+2)) flags ≤ B; dsimp only [B,finalTreeWork]; omega)⟩

/-- Address placement leaves the cost of decoding a bounded original edge unchanged. -/
theorem id_work_of_raw (a : Attempt) (u : ℕ) (i : Fin D)
    (raw : (rawEdge s b.rows a i).work ≤ u) : (id F s b a i).work ≤ 4*(u*8)+22 := by
  have decoded : (edge F s b.rows a i).work ≤ u*8 :=
    (substitute_work _ _).trans (Nat.mul_le_mul_right 8 raw)
  have keep : (retainedAt F s a).work ≤ 12 := by
    cases a with
    | outer => exact (by decide : 1 ≤ 12)
    | inner => exact le_rfl
  simp only [id,physicalEdge,Expr.work]
  omega

/-- Cost of the dated common edge identifier before the final role lookup. -/
theorem final_id_work (a : Attempt) (u : ℕ) (one : 1 ≤ u)
    (ports : DatePortWork s c b G u a) (i : Fin D) : (id F bs b a i).work ≤ 4*(u*8)+22 :=
  id_work_of_raw bs b F a u i (raw_port_work s c b G a u one ports i)

end StripChart
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
