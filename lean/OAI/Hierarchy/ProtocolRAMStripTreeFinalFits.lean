import OAI.Hierarchy.ProtocolRAMCalendarStripTrees
import OAI.Hierarchy.ProtocolRAMStripNativeFits
import OAI.Hierarchy.ProtocolRAMOccurrenceBounds

namespace OAI
/-! # Address bounds for the emitted direct, catalyst and broadcast edge operands -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar
open AdaptiveProbe ProbeStage CoreBoard BoughtSockets CatalogueRows StockCommit StripDirectory PortPadding
open scoped Fin.CommRing
variable {w limit z W k n q depth : ℕ}

theorem CatalogueRows.Board.checked_fits (b : Board) (x : Expr)
    (value : x.Fits w limit) (flag : b.bought.flag.Fits w limit) :
    (b.checkedEdge x).Fits w limit :=
  ⟨value,trivial,value,value,trivial,⟨fits_atRow _ _ flag ⟨value,trivial⟩,trivial,trivial,value⟩,trivial⟩

private theorem mate_of_primary {S : PurchaseSampler} {C H A B : Type*}
    (p : StripPorts S z (2^W) k C H B) (b : Board)
    (all : ∀r : ColumnWires.Role C H (A⊕B) k,(p.primary b r).Fits w limit)
    (r : ColumnWires.Role C H (A⊕B) k) : (p.mate b r).Fits w limit := by
  cases r with
  | catalyst c j => exact all (.radius c j true)
  | _ => trivial

private theorem tree_of_primary {S : PurchaseSampler} {A B : Type*}
    (p : StripPorts S z (2^W) k (Strip.TreeColumn n) (Fin n) B) (b : Board)
    (all : ∀r : ColumnWires.Role (Strip.TreeColumn n) (Fin n) (A⊕B) k,(p.primary b r).Fits w limit)
    (e : Strip.TreeLink n k) : (treeTerm p b e).Fits w limit := by
  rcases e with i|⟨c,j,s⟩
  · exact all (.horizontal i none)
  · exact all (.radius c j s)

theorem CatalogueRows.stripTree_fits {S : PurchaseSampler} {A B : Type*}
    (p : StripPorts S z (2^W) k (Strip.TreeColumn n) (Fin n) B)
    (b : Board) (start rows : ℕ) (head : (treeHeader start rows n k).stop≤limit)
    (word : limit<2^w)
    (all : ∀r : ColumnWires.Role (Strip.TreeColumn n) (Fin n) (A⊕B) k,(p.primary b r).Fits w limit) :
    (stripTree p b start rows).edge.Fits w limit ∧ (stripTree p b start rows).sourceRow.Fits w limit := by
  let h:=treeHeader start rows n k
  have bounds:=h.input_ends head
  have ball:=h.ballTerm.fits_of_inputEnd bounds.1 word
  refine ⟨choose_fits_bound _ _ _ _ ?_ (h.fieldTerm.fits_of_inputEnd bounds.2.1 word),ball⟩
  intro i
  have val:=tree_of_primary p b all ((Fintype.equivFin _).symm i)
  exact fits_atRow _ _ ⟨val,trivial,val,trivial⟩ ball

namespace StripChart
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : Board) (G : PortBanks ((c.inject+c.cool)*c.outerFuel))
variable (F : Type*) [Field F] [SiteNaming (ColumnSite (PayloadStrip.Columns (Stages z (2^W))) k)]
  [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)]
local notation "N" => Stages z (2^W)
local notation "bs" => withPorts s c b G
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))

theorem treeHeader_bound (base n : ℕ) (a : Attempt) (date : Event.attempt a∈events c) :
    let t:=treePage s c b G F base n
    (treeHeader (pageStart t c a) (treeRows s c b G F a) n k).stop≤t.stop := by
  intro t
  let i : Fin (events c).length:=⟨(events c).idxOf (.attempt a),List.idxOf_lt_length_of_mem date⟩
  have atDate : (events c)[i]=Event.attempt a:=List.getElem_idxOf i.isLt
  have count : t.rows i=treeRows s c b G F a := by
    change (match (events c)[i] with | .attempt r=>_ | .feed _=>0)=_
    rw [atDate]
  have equal : t.header i=treeHeader (pageStart t c a) (treeRows s c b G F a) n k := by
    change PortHeader.mk _ (t.rows i) _=_
    rw [count]
    rfl
  rw [←equal]
  exact t.end_le i

private theorem extend_fits {m slots : ℕ} {terms : Fin m→Expr} {x : Expr}
    (fields : ∀i,(terms i).Fits w limit) (dead : x.Fits w limit) (i : Fin slots) :
    (extend terms x i).Fits w limit := by
  unfold extend
  split
  · exact fields _
  · exact dead

omit [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] in
/-- Every output of a radius-mate operand names either a core edge or the
one-past-the-end sentinel, independently of the acquired flag table. -/
private theorem mate_range {S : PurchaseSampler} {C H A B : Type*} (p : StripPorts S z (2^W) k C H B)
    (b : Board) (role : ColumnWires.Role C H (A⊕B) k) (m : Computability.VPVNP.BurstRAM.Memory w)
    (r : Computability.VPVNP.BurstRAM.Word w) (room : b.rows<2^w) :
    ((p.mate b role).eval m r).val<b.coreRows ∨ ((p.mate b role).eval m r).val=b.rows := by
  have core : b.coreRows<2^w:=by unfold Board.rows at room;omega
  cases role with
  | catalyst c j =>
    simp only [StripPorts.mate,Board.coreOnly,Expr.eval,ThreeFlat.RAM.DescriptorExpr.Comparison.test,
      Fin.lt_def,decide_eq_true_eq,Fin.val_cast_of_lt core]
    split
    · exact Or.inl (by assumption)
    · exact Or.inr (Fin.val_cast_of_lt room)
  | _ => exact Or.inr (Fin.val_cast_of_lt room)

theorem choice_has {n w : ℕ} (base : ℕ) (terms : Fin n→Expr) (which : Expr)
    (m : Computability.VPVNP.BurstRAM.Memory w) (r : Computability.VPVNP.BurstRAM.Word w) (P : Computability.VPVNP.BurstRAM.Word w→Prop)
    (zero : P 0) (each : ∀i,P ((terms i).eval m r)) : P ((chooseField n base terms which).eval m r) := by
  induction n generalizing base with
  | zero => exact zero
  | succ n ih =>
    by_cases hit : which.eval m r = (base : Computability.VPVNP.BurstRAM.Word w)
    · simpa only [chooseField,Expr.eval,ThreeFlat.RAM.DescriptorExpr.Comparison.test,
        beq_iff_eq,hit,ite_true] using each 0
    · simpa only [chooseField,Expr.eval,ThreeFlat.RAM.DescriptorExpr.Comparison.test,
        beq_iff_eq,hit,ite_false] using ih (base+1) (fun i=>terms i.succ) (fun i=>each i.succ)

def DatePortFits (w limit : ℕ) : Attempt → Prop
  | .outer .. => ∀r : PayloadRole N k,((payloadPortsAt s c G).primary b r).Fits w limit
  | .inner p t .. => ∀r : PurchasedRole depth k,((boughtPortsAt s c b G p t).primary b r).Fits w limit

set_option maxHeartbeats 800000 in
omit [SiteNaming (ColumnSite (PayloadStrip.Columns N) k)] [SiteNaming (ColumnSite (ChainStrip.Columns depth) k)] in
private theorem port_selections (a : Attempt) (ports : DatePortFits s c b G w limit a) :
    (∀i : Fin D,(rawEdge bs b.rows a i).Fits w limit) ∧
    (∀i : Fin D,(radiusMate s c b G a i).Fits w limit) ∧
    (∀i : Fin D,(catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a i).Fits w limit) := by
  refine ⟨?_,?_,?_⟩
  · intro i
    cases a with
    | outer phase trial =>
      change (extend (payloadEdge (payloadPortsAt s c G) b) (.lit b.rows) i).Fits w limit
      apply extend_fits
      · intro j
        exact ports ((Fintype.equivFin (PayloadRole N k)).symm j)
      · trivial
    | inner phase trial slice tick =>
      change (extend (purchaseEdge (boughtPortsAt s c b G phase trial) b) (.lit b.rows) i).Fits w limit
      apply extend_fits
      · intro j
        exact ports ((Fintype.equivFin (PurchasedRole depth k)).symm j)
      · trivial
  · intro i
    cases a with
    | outer phase trial =>
      unfold radiusMate
      apply extend_fits
      · intro j
        exact mate_of_primary (payloadPortsAt s c G) b ports ((Fintype.equivFin (PayloadRole N k)).symm j)
      · trivial
    | inner phase trial slice tick =>
      unfold radiusMate
      apply extend_fits
      · intro j
        exact mate_of_primary (boughtPortsAt s c b G phase trial) b ports ((Fintype.equivFin (PurchasedRole depth k)).symm j)
      · trivial
  · intro i
    cases a <;> unfold catalystFlag <;> apply extend_fits <;> intros <;> trivial

set_option maxHeartbeats 1400000 in
theorem elapsed_pair (base : ℕ) (a : Attempt) (headerBound : (header F bs a).stop≤limit)
    (word : limit<2^w) (boardRoom : b.rows<2^w) (coreLive : 0<b.coreRows)
    (keep : (retainedAt F bs a).Fits w limit)
    (ports : DatePortFits s c b G w limit a) :
    (∀i : Fin D,(id F bs b a i).Fits w limit) ∧ ∀mask mate,
      (withTrees s c b G F base a).catalystMate=some (mask,mate) →
      mask.Fits w limit ∧ ∃raw : Expr,mate=b.checkedEdge raw ∧ raw.Fits w limit ∧
        ∀(m : Computability.VPVNP.BurstRAM.Memory w) (r : Computability.VPVNP.BurstRAM.Word w),
          (raw.eval m r).val<b.coreRows ∨ (raw.eval m r).val=b.rows := by
  let h:=header F bs a
  have bounds:=h.input_ends headerBound
  have ball:=h.ballTerm.fits_of_inputEnd bounds.1 word
  have field:=h.fieldTerm.fits_of_inputEnd bounds.2.1 word
  have ⟨primary,mates,bits⟩:=port_selections s c b G a ports
  constructor
  · intro i
    have raw:=fits_atRow _ _ (primary i) ball
    exact ⟨trivial,raw,trivial,raw,raw,trivial,⟨keep,trivial,trivial,raw⟩,trivial⟩
  · intro mask mate printed
    rw [withTrees,forest_mask] at printed
    obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Option.some.inj printed)
    refine ⟨choose_fits_bound _ _ _ _ bits field,_,rfl,
      choose_fits_bound _ _ _ _ (fun i=>fits_atRow _ _ (mates i) ball) field,?_⟩
    intro m reg
    apply choice_has 0 _ _ m reg (fun x=> x.val<b.coreRows ∨ x.val=b.rows) (Or.inl coreLive)
    intro i
    rw [eval_atRow]
    cases a <;> simp only [radiusMate,extend] <;> split
    all_goals first | exact mate_range _ b _ _ _ boardRoom | exact Or.inr (Fin.val_cast_of_lt boardRoom)

set_option maxHeartbeats 1000000 in
/-- Every physical address used at this attempt, including the padded case and
the second radius, is bounded by the same public memory extent. -/
theorem final_operands (base : ℕ) (a : Attempt) (date : Event.attempt a∈events c)
    (word : limit<2^w) (headerBound : (header F bs a).stop≤limit)
    (tables : (boughtPage s c b G F base).stop≤limit) (flag : b.bought.flag.Fits w limit)
    (keep : (retainedAt F bs a).Fits w limit)
    (ports : DatePortFits s c b G w limit a) :
    let t:=withTrees s c b G F base a
    (∀i : Fin D,(id F bs b a i).Fits w limit) ∧ t.edge.Fits w limit ∧ t.sourceRow.Fits w limit ∧
      ∀ mask mate,t.catalystMate=some (mask,mate)→mask.Fits w limit ∧ mate.Fits w limit := by
  let h:=header F bs a
  have bounds:=h.input_ends headerBound
  have ball:=h.ballTerm.fits_of_inputEnd bounds.1 word
  have field:=h.fieldTerm.fits_of_inputEnd bounds.2.1 word
  have below : (payloadPage s c b G F base).stop≤(boughtPage s c b G F base).stop:=Nat.le_add_right _ _
  have ⟨raw,mates,bits⟩:=port_selections s c b G a ports
  have arrays : (originalTree s c b G F base a).edge.Fits w limit ∧
      (originalTree s c b G F base a).sourceRow.Fits w limit := by
    cases a with
    | outer p t =>
      exact stripTree_fits _ b _ _ ((treeHeader_bound s c b G F base _ _ date).trans (below.trans tables)) word ports
    | inner p t j u =>
      exact stripTree_fits _ b _ _ ((treeHeader_bound s c b G F (payloadPage s c b G F base).stop _ _ date).trans tables) word ports
  refine ⟨?_,b.checked_fits _ arrays.1 flag,arrays.2,?_⟩
  · intro i
    have r:=fits_atRow _ _ (raw i) ball
    exact ⟨trivial,r,trivial,r,r,trivial,⟨keep,trivial,trivial,r⟩,trivial⟩
  · intro mask mate eqn
    rw [withTrees,forest_mask] at eqn
    obtain ⟨rfl,rfl⟩:=Prod.mk.inj (Option.some.inj eqn)
    exact ⟨choose_fits_bound _ _ _ _ bits field,b.checked_fits _
      (choose_fits_bound _ _ _ _ (fun i=>fits_atRow _ _ (mates i) ball) field) flag⟩


end StripChart
end Hierarchy.ProtocolRAM.Calendar
end

end OAI
