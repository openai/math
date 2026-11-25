import OAI.Hierarchy.GridThroughPlacement
import OAI.Hierarchy.GridLensCalibrated
import OAI.Hierarchy.CatalystExpose
import OAI.Hierarchy.UniversalTick
import OAI.Hierarchy.GridDescription

namespace OAI
/-! # Selecting the actual universal tick, approximation and checked grid

The deterministic controller acts on its own program bits and selector.
Whenever it produces a setting the geometry follows from the verified
one-touch placement, with the same replacement as in the evaluator. -/

noncomputable section
namespace Hierarchy
open LinearAlgebra.SpectralBooks ThreeFlat Filter
open UniversalGrid GridScale
open scoped Classical

namespace GridScale

/-- The actual public pin budget contains every width-bounded instruction
header and still fits the rounded clock. This selection precedes the program
descriptions and the replacement network. -/
theorem tick_fits {Q : ℕ → ℕ} {D : ℕ → ℝ} (env : Envelopes Q D)
    {F : Type*} [Fintype F] :
    ∀ᶠ w : ℕ in atTop, let S := pins w (overhead Q D w)
      S ≤ UniversalTick.clock w UniversalTick.saving ∧ Fintype.card F ≤ 2^(64*w) ∧
      ∀ p r k, 0<p → p≤w → r≤w → k≤w →
      ∀ M : Computability.VPVNP.BurstRAM.PrivateRAM.Machine (64*w) p r k,
        Diagonal.NativeTrace.Fits M S 0 (UniversalTick.depth w UniversalTick.saving)
          (UniversalTick.clock w UniversalTick.saving) := by
  filter_upwards [sublinear env 8,polynomial env 1 (UniversalTick.saving+1),
    polynomial env 512 2,(grows env).eventually_ge_atTop 2,
    UniversalTick.fits_round UniversalTick.saving,eventually_ge_atTop (max 16 (Fintype.card F))]
    with w am pow text two fit large
  let a := overhead Q D w
  intro S
  have wp : 0<w := by omega
  have pow' : w^UniversalTick.saving < 2^a := by
    have a1 := Nat.pow_le_pow_left (Nat.le_succ w) (UniversalTick.saving+1)
    have h : w^(UniversalTick.saving+1) ≤ 2^a := a1.trans (by simpa [a] using pow)
    have strict : w^UniversalTick.saving < w^(UniversalTick.saving+1) := by
      rw [pow_succ]
      exact lt_mul_of_one_lt_right (Nat.pow_pos wp) (by omega)
    exact strict.trans_le h
  have log := (Nat.log2_lt (Nat.pow_pos wp).ne').mpr pow'
  have cap : S ≤ UniversalTick.clock w UniversalTick.saving := by
    change 2^(w-4*a) ≤ 2^(w-((w^UniversalTick.saving).log2+1))
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have small : UniversalTick.clock w UniversalTick.saving ≤ 2^(64*w) := by
    apply Nat.pow_le_pow_right (by decide)
    dsimp [UniversalTick.depth]
    omega
  have age : w ≤ 2^(64*w) := Nat.lt_two_pow_self.le.trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  have hf : Fintype.card F ≤ 2^(64*w) := (le_trans (le_max_right _ _) large).trans age
  refine ⟨cap,hf,?_⟩
  intro p r k hp ps rs ks M
  have bits : (1+6*p+k)*(64*w) ≤ S := calc
    _ ≤ 512*(w+1)^2 := by
      have e : 1+6*p+k ≤ 8*(w+1) := by omega
      have upper := Nat.mul_le_mul_right (64*w) e
      nlinarith only [upper]
    _ ≤ 2^a := text
    _ ≤ S := by change 2^a ≤ 2^(w-4*a); apply Nat.pow_le_pow_right (by decide); change 8*a≤w at am; omega
  have modl := (Nat.pow_le_pow_right (n:=2) (by decide) (Nat.le_succ (64*w)))
  have header := cap.trans small
  refine ⟨by omega,(ps.trans age).trans modl,hp,header,small.trans modl,?_,⟨by omega,rs.trans age,?_⟩,by simpa using bits⟩
  · rw [pow_add,pow_one]
    change S+UniversalTick.clock w UniversalTick.saving ≤ 2*UniversalTick.clock w UniversalTick.saving
    omega
  · exact (Nat.le_mul_of_pos_right _ (show 0<64*w by omega)).trans (bits.trans header)

end GridScale

namespace GridThrough

variable {F : Type*} [Field F] {k p copies n e : ℕ}

/-- Output of a successfully verified controller, with the exterior directions
fixed before the choice of code. -/
abbrev Setting (X : Catalyst.Approximation F k (copies*p)) (n e : ℕ) (dir : Fin e → Fin k) :=
  {s : Program (Fin e) n (copies*p) X.width // s.direction=dir}

def grid (N : BitNetwork F p) (X : Catalyst.Approximation F k (copies*p))
    (dir : Fin e → Fin k) {a ell : ℕ}
    (controller : Bits a → Bits ell → Option (Setting X n e dir)) : Grid F k where
  pins := p
  copies := copies
  g := n+1
  rails := e
  codeBits := a
  selectorBits := ell
  tick := N
  replacement := X
  direction := dir
  wiring code sel := (controller code sel).map (fun v => v.1.wiring)

/-- The physical settings returned by a program supply every geometry
premise of the lens bound, for every controller description including
descriptions that time out on all selectors. -/
theorem strict {Q : ℕ → ℕ} {D : ℕ → ℝ} (env : Envelopes Q D) (A : ℕ)
    (hk : 0<k) (P : SpectralPlacementPrices F (EuclideanSpace ℝ (Fin k))) :
    ∀ᶠ w : ℕ in atTop, ∀ q, 0<q → q≤Q w → let a := overhead Q D w
      let p := pins w a
      let e := external k a (pairs A w q)
      let n := side a - 1
      ∀ (N : BitNetwork F p) (X : Catalyst.Approximation F k (q*p)) (dir : Fin e → Fin k),
      X.Gap (Catalyst.tickProduct N q) (D w/2) →
      ∀ controller : Bits (w^2) → Bits (selector k w a) → Option (Setting X n e dir),
      let G := grid N X dir controller
      let ends := fun u : GridDiagonal.Ends (Fin e) => GridDiagonal.focus (radius k a) (dir u.1,u.2)
      ∀ code, G.exactGrid code-G.accelerated code=0 ∨
        P.price (GridDiagonal.raw (G.exactGrid code-G.accelerated code)) ends <
        P.price (GridDiagonal.raw (GridDiagonal.identity F)) ends := by
  filter_upwards [UniversalGrid.Grid.calibrated_strict env A hk P,GridScale.header_room env k A hk]
    with w price room
  intro q hq qtop a p e n N X dir gap controller G ends code
  have ep : 0<e := (room q hq qtop e (by simp [e,a])).1
  let : Nonempty (Fin G.rails) := ⟨⟨0,ep⟩⟩
  have sg : 0<side a := Nat.two_pow_pos _
  exact price q hq qtop G (le_refl _) (by change side a-1+1 ≤ side a; omega) (le_refl _) gap code (by
    intro s W ok
    change (controller code s).map (fun v => v.1.wiring) = some W at ok
    rcases Option.map_eq_some_iff.mp ok with ⟨v,_,rfl⟩
    have placed:=v.1.placement X (radius k a)
    rw [v.property] at placed
    exact ⟨placed⟩)

end GridThrough

namespace Catalyst

/-- Literal size and width bounds for the selected stored replacement. The
through program uses exactly its actual widths in each direction. -/
theorem Approximation.width_le_size {k p : ℕ} {F : Type*} [Field F]
    (X : Approximation F k p) (i : Fin k) : X.width i ≤ X.size := by
  let e : Fin (X.width i) ↪ Port p X.width :=
    ⟨fun j => .inr (⟨i,j⟩,false), fun _ _ h => by simpa using h⟩
  exact (show X.width i ≤ Fintype.card (Port p X.width) by
    simpa using Fintype.card_le_of_embedding e).trans (Nat.le_add_left _ _)

/-- Selecting a tick and exposing the selected pointwise approximation loses
at most half the gap, while preserving the original finite table. -/
theorem select_exposed {F : Type*} [Field F] {k : ℕ} [NeZero k] (A A' : ℕ)
    {Q : ℕ → ℕ} {D : ℕ → ℝ} (env : Envelopes Q D)
    (collapse : ∀ᶠ w : ℕ in atTop, ∀ (p : ℕ) (N : BitNetwork F p),
      N.cells+N.internal+p≤2^w → p*w^A'≤2^w → ∃ q, 0<q ∧ q≤Q w ∧
      ∃ X : Approximation F k (q*p), X.size*w^A≤q*2^w ∧ X.PointwiseGap (tickProduct N q) (D w)) :
    ∀ᶠ w : ℕ in atTop, let a := overhead Q D w
      ∀ N : BitNetwork F (pins w a), N.cells+N.internal+pins w a≤2^w →
      ∃ q, 0<q ∧ q≤Q w ∧ ∃ X : Approximation F k (q*pins w a),
        X.size≤pairs A w q ∧ (∀ i, X.width i≤pairs A w q) ∧ X.Gap (tickProduct N q) (D w/2) := by
  filter_upwards [collapse,pin_room env k 1 A',eventually_ge_atTop 1] with w pick loss wp
  intro a N price
  have pinBudget : pins w a*w^A' ≤ 2^w := calc
    _ ≤ 1*(w+1)^A'*pins w a := by rw [one_mul,Nat.mul_comm]; gcongr; omega
    _ ≤ _ := loss.1
  obtain ⟨q,hq,top,X,cost,pg⟩ := pick _ N price pinBudget
  have den : 0<w^A := Nat.pow_pos wp
  have bank := (ceilDiv_le_iff_le_mul den).mp (le_refl (pairs A w q))
  have sizeX : X.size ≤ pairs A w q := Nat.le_of_mul_le_mul_left (c:=w^A)
    ((by simpa only [Nat.mul_comm (w^A)] using cost : w^A*X.size ≤ q*2^w).trans bank) den
  refine ⟨q,hq,top,X,sizeX,fun i => (X.width_le_size i).trans sizeX,?_⟩
  intro P
  rcases X.expose _ pg P with zero | bound
  · exact Or.inl zero
  right
  have spend := (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (show (q:ℝ)≤Q w by exact_mod_cast top)
      (show 0≤4*(k:ℝ) by positivity)) (Nat.cast_nonneg (α:=ℝ) (pins w a))).trans loss.2
  rw [Nat.cast_mul] at bound
  exact bound.trans (by linarith)

end Catalyst
/-- Hardware capacities and input layout are determined before choosing the
replacement. In particular this record has no field for a controller, an
evaluator, or their outputs. -/
structure TickSelection (F : Type*) [Field F] [Fintype F] (k A w : ℕ) (Q : ℕ→ℕ) (D : ℕ→ℝ) where
  active : 0 < GridDescription.capacity w
  fieldRoom : Fintype.card F≤2^(64*w)
  tickFit : Diagonal.NativeTrace.Fits
    (UniversalTick.accept (64*w) (GridDescription.capacity w) (GridDescription.capacity w)
      (GridDescription.capacity w) active) (GridScale.pins w (GridScale.overhead Q D w)) 0
    (UniversalTick.depth w UniversalTick.saving) (UniversalTick.clock w UniversalTick.saving)
  copies : ℕ
  copies_pos : 0<copies
  copies_le : copies≤Q w
  replacement : Catalyst.Approximation F k (copies*GridScale.pins w (GridScale.overhead Q D w))
  size_le : replacement.size≤GridScale.pairs A w copies
  gap : replacement.Gap (Catalyst.tickProduct (UniversalTick.tick fieldRoom tickFit.width tickFit.labels
    0 0 tickFit.header tickFit.time (GridDescription.capacity w) (GridDescription.capacity w)) copies) (D w/2)

/-- A saving exponent can be selected after all fixed machine costs are
known. All subsequent controller and evaluator programs share the same
universal tick and the same selected replacement. -/
theorem choose_tick {F : Type*} [Field F] [Fintype F] {k : ℕ} [NeZero k]
    (collapse : Catalyst.HasPointwiseCollapse F k) (costExponent : ℕ) :
    ∃ A>costExponent, ∃ Q : ℕ→ℕ, ∃ D : ℕ→ℝ, GridScale.Envelopes Q D ∧
      ∀ᶠ w : ℕ in atTop, Nonempty (TickSelection F k A w Q D) := by
  obtain ⟨A,data,age⟩ := (collapse.and (eventually_gt_atTop costExponent)).exists
  rcases data with ⟨A',_,Q,D,env,shrinks⟩
  refine ⟨A,age,Q,D,env,?_⟩
  filter_upwards [GridScale.tick_fits (F:=F) env,Catalyst.select_exposed A A' env shrinks,
    UniversalTick.fits_round UniversalTick.saving,eventually_ge_atTop
      (max (max 1024 (Fintype.card F)) (4*(10^26*65^14+400*66^3+1)))] with w bounds choose round good
  let arch := GridDescription.capacity w
  let V := GridScale.pins w (GridScale.overhead Q D w)
  have cap : arch≤w := Nat.div_le_self _ _
  have active : 0<arch := by dsimp [arch,GridDescription.capacity]; omega
  have fit := bounds.2.2 arch arch arch active cap cap cap (UniversalTick.accept (64*w) arch arch arch active)
  let tick := UniversalTick.tick bounds.2.1 fit.width fit.labels 0 0 fit.header fit.time arch arch
  have size : tick.cells+tick.internal+V≤2^w := UniversalTick.size bounds.2.1 fit.width fit.labels 0 0
    fit.header fit.time arch arch (by omega) (by omega) (by omega) (by omega) (by omega) round bounds.1
  obtain ⟨q,hq,top,X,small,_,gap⟩ := choose tick size
  exact ⟨⟨active,bounds.2.1,fit,q,hq,top,X,small,gap⟩⟩

end Hierarchy
end

end OAI
