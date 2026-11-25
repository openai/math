import OAI.Hierarchy.GridControllerIdle
import OAI.Hierarchy.GridSimRailScan
import OAI.Hierarchy.GridPinPublisher
import OAI.Hierarchy.GridThroughPinAssignment

namespace OAI
/-! # Publishing simulation rail geometry from the allocated tick pins

Each rail's negative endpoint has already been assigned its flattened pin in
the destination page. Dividing its address by the number of pins per cell
recovers the receiving cell. The corresponding radix digit is the touch.
The external label alone selects the direction. -/

namespace Hierarchy.GridControllerSimGeometry
open ThreeFlat RAM RAM.PhysicalProcedure
open Computability.VPVNP.BurstRAM GridThrough
open scoped Fin.CommRing
noncomputable section

abbrev Arena := GridOrderedSources.Arena
abbrev Shape := GridControllerIdle.Shape

def banks (A : Arena) : GridSimRailScan.Banks :=
  ⟨9*A.J,A.railMap.dir,A.railMap.cell,A.railMap.powers,A.railMap.touch⟩

def seed (W : ℕ) (A : Arena) (b : Shape) : Procedure W :=
  (GridControllerIdle.scan W A b .direction).seq (GridControllerIdle.scan W A b .powers)

def seedCost (W : ℕ) (A : Arena) (b : Shape) :=
  GridControllerIdle.fee W A b .direction + GridControllerIdle.fee W A b .powers

def seeded {W : ℕ} (A : Arena) (b : Shape) (m : Memory W) :=
  GridControllerIdle.update A b .powers (GridControllerIdle.update A b .direction m)

theorem seed_exec {W : ℕ} {A : Arena} {b : Shape} (fit : GridControllerIdle.Fits W A b) (m : Memory W) :
    (seed W A b).Exec m (seeded A b m) (seedCost W A b) :=
  Procedure.Exec.then (GridControllerIdle.scan_run fit .direction m) (GridControllerIdle.scan_run fit .powers _)

private theorem update_outside {W : ℕ} (A : Arena) (b : Shape) (col : GridControllerIdle.Column)
    (m : Memory W) (a : ℕ) (off : ¬ (GridControllerIdle.base A col ≤ a ∧
      a < GridControllerIdle.base A col+GridControllerIdle.count b col)) :
    GridControllerIdle.update A b col m a=m a := ite_eq_right off

private theorem update_at {W : ℕ} (A : Arena) (b : Shape) (col : GridControllerIdle.Column)
    (m : Memory W) (i : ℕ) (hi : i < GridControllerIdle.count b col) :
    GridControllerIdle.update A b col m (GridControllerIdle.base A col+i)=(GridControllerIdle.word W b i col : Word W) := by
  let start := GridControllerIdle.base A col
  have seen : start ≤ start+i ∧ start+i < start+GridControllerIdle.count b col := ⟨by omega,by omega⟩
  have value : GridControllerIdle.update A b col m (start+i)=
      (GridControllerIdle.word W b (start+i-start) col : Word W) := ite_eq_left seen
  simpa only [Nat.add_sub_cancel_left] using value

theorem seeded_dir {W : ℕ} {A : Arena} {b : Shape} (room : GridControllerIdle.Room A b)
    (m : Memory W) (i : ℕ) (hi : i < b.rails) :
    seeded A b m (A.railMap.dir+i)=(i/b.railsPer : ℕ) := by
  have hr := room.rails
  have pass := update_outside A b .powers (GridControllerIdle.update A b .direction m) (A.railMap.dir+i) (by
    change ¬ (5*A.J+2*(A.J/8) ≤ 5*A.J+i ∧ 5*A.J+i < 5*A.J+2*(A.J/8)+b.axes)
    omega)
  exact pass.trans (update_at A b .direction m i hi)

theorem seeded_power {W : ℕ} (A : Arena) (b : Shape) (m : Memory W) (j : ℕ) (hj : j < b.axes) :
    seeded A b m (A.railMap.powers+j)=(b.radix^j : ℕ) :=
  update_at A b .powers (GridControllerIdle.update A b .direction m) j hj

theorem seeded_frame {W : ℕ} {A : Arena} {b : Shape} (room : GridControllerIdle.Room A b)
    (m : Memory W) (i : ℕ) (outside : i < 5*A.J ∨ 6*A.J ≤ i) : seeded A b m i=m i := by
  have hr := room.rails
  have hk := room.axes
  have pass := update_outside A b .powers (GridControllerIdle.update A b .direction m) i (by
    change ¬ (5*A.J+2*(A.J/8) ≤ i ∧ i < 5*A.J+2*(A.J/8)+b.axes)
    omega)
  exact pass.trans (update_outside A b .direction m i (by
    change ¬ (5*A.J ≤ i ∧ i < 5*A.J+b.rails)
    omega))

/-- The actual emitted address of the negative side determines the cell even
when two adjacent endpoints have different replica-local pin numbers. -/
theorem dest_cell {r k n q d : ℕ} (P : PinAssignment (Fin r) k n q d)
    (e : Fin r) (hp : 0 < q*d) :
    GridOrderedPinOrigins.slot P (2*e.val)/(q*d)=(finFunctionFinEquiv (P.row e)).val := by
  let j := Ordered.sides (e,false)
  have jv : j.val=2*e.val := by simp [j,Ordered.exterior_number]
  rw [←jv,GridOrderedPinOrigins.slot,dite_eq_left j.isLt]
  change (GridOrderedPinOrigins.address P (Ordered.sides (e,false))).val / _ = _
  rw [GridOrderedPinOrigins.address_val]
  have bound : (P.tick e).2.val*d+(P.slot (e,false)).val < q*d := by
    simpa only [finProdFinEquiv_apply_val,Nat.mul_comm d,Nat.add_comm (P.slot (e,false)).val] using
      (finProdFinEquiv ((P.tick e).2,P.slot (e,false))).isLt
  rw [Nat.add_assoc,Nat.mul_comm (finFunctionFinEquiv (P.row e)).val,
    Nat.mul_add_div hp,Nat.div_eq_of_lt bound,Nat.add_zero]

def program (W : ℕ) (A : Arena) (b : Shape) : Procedure W :=
  (seed W A b).seq (GridSimRailScan.build W (banks A) b.rails b.radix (b.q*b.pins))

def cost (W : ℕ) (A : Arena) (b : Shape) :=
  seedCost W A b + GridSimRailScan.cost b.rails

def output {W : ℕ} (A : Arena) (b : Shape) (m : Memory W) :=
  GridSimRailScan.image (banks A) b.rails b.radix (b.q*b.pins) (seeded A b m)

/-- All four geometry banks are confined to page five. Other controller
banks, the compact table, and the original exterior bits keep their values. -/
theorem frame {W : ℕ} {A : Arena} {b : Shape} (room : GridControllerIdle.Room A b)
    (m : Memory W) (i : ℕ) (outside : i < 5*A.J ∨ 6*A.J ≤ i) : output A b m i=m i := by
  have hr := room.rails
  rw [output,GridSimRailScan.frame,seeded_frame room m i outside] <;>
    dsimp only [banks,GridOrderedSources.Arena.railMap] <;> omega

theorem cost_bound (W : ℕ) (A : Arena) (b : Shape) :
    cost W A b ≤ 16+400*(b.rails+b.axes) := by
  have hd : (GridControllerIdle.expr W A b .direction).work ≤ 128 :=
    GridControllerIdle.work_bound W A b .direction
  have hp : (GridControllerIdle.expr W A b .powers).work ≤ 128 :=
    GridControllerIdle.work_bound W A b .powers
  have d := Nat.mul_le_mul_left b.rails (show 2*(GridControllerIdle.expr W A b .direction).work+4 ≤ 260 by omega)
  have p := Nat.mul_le_mul_left b.axes (show 2*(GridControllerIdle.expr W A b .powers).work+4 ≤ 260 by omega)
  dsimp only [cost,seedCost,GridControllerIdle.fee,GridControllerIdle.count,GridSimRailScan.cost]
  omega

/-- The preexisting destination page is the output of the endpoint publisher.
The rail-number slab provides each direction and the destination provides
both the full cell and its longitudinal touch coordinate. -/
theorem publish {W m n B q d h pc : ℕ} (A : Arena)
    (P : PinAssignment (GridIdleLayout.Rails m n B) (m+1) n q d)
    (heading : P.direction=GridIdleLayout.direction)
    (mem : Memory W) (positive : 0 < q*d) (high : 12*A.J < 2^W)
    (fit : GridControllerIdle.Fits W A (GridControllerIdle.shape m n B h q d pc))
    (room : GridControllerIdle.Room A (GridControllerIdle.shape m n B h q d pc))
    (published : ∀ i < (m+1)*GridIdleLayout.each m n B*2,
      mem (9*A.J+i)=(GridOrderedPinOrigins.slot P i:Word W)) :
    let b := GridControllerIdle.shape m n B h q d pc
    let out := output A b mem
    (program W A b).Exec mem out (cost W A b) ∧
      (∀ e : GridIdleLayout.Rails m n B, GridPassageRAMRow.DecodeReads out A.railMap.dir A.railMap.cell A.railMap.powers A.railMap.touch
        e.val (P.direction e) (P.row e) (P.touch e)) ∧
      (∀ j : Fin (m+1), out (A.railMap.powers+j.val)=((n+1)^j.val : Word W)) ∧
      ∀ i, (i < 5*A.J ∨ 6*A.J ≤ i) → out i=mem i := by
  dsimp only
  let b := GridControllerIdle.shape m n B h q d pc
  let src := seeded A b mem
  let out := output A b mem
  have rroom : b.rails ≤ A.J/8 := room.rails
  have kroom : m+1 ≤ A.J/8 := room.axes
  have data : (n+1)^(m+1)*(q*d) ≤ A.J := room.data
  have cells := (Nat.le_mul_of_pos_right ((n+1)^(m+1)) positive).trans data
  have pfit := (Nat.le_mul_of_pos_left (q*d) (by positivity : 0 < (n+1)^(m+1))).trans data
  have gfit : n+1 ≤ (n+1)^(m+1) := by
    simpa using Nat.pow_le_pow_right (Nat.succ_pos n) (show 1 ≤ m+1 by omega)
  have scan : GridSimRailScan.Fits W (banks A) b.rails (m+1) (n+1) (q*d) := by
    constructor <;> (try dsimp only [banks,GridOrderedSources.Arena.railMap]) <;> omega
  have dir (e : GridIdleLayout.Rails m n B) :
      src (A.railMap.dir+e.val)=((P.direction e).val:Word W) := by
    rw [heading,GridIdleLayout.direction_val]
    exact seeded_dir room mem _ e.isLt
  have dirval (e : GridIdleLayout.Rails m n B) :
      (src (A.railMap.dir+e.val)).val=(P.direction e).val := by
    rw [dir,Fin.val_cast_of_lt (by have := (P.direction e).isLt; omega)]
  have stride (j : Fin (m+1)) : src (A.railMap.powers+j.val)=(((n+1)^j.val : ℕ) : Word W) :=
    seeded_power A b mem j.val j.isLt
  have strideval (j : Fin (m+1)) : (src (A.railMap.powers+j.val)).val=(n+1)^j.val := by
    have le : (n+1)^j.val ≤ (n+1)^(m+1) := Nat.pow_le_pow_right (Nat.succ_pos n) j.isLt.le
    rw [stride,Fin.val_cast_of_lt (by omega)]
  have original (e : GridIdleLayout.Rails m n B) :
      (src ((banks A).dest+2*e.val)).val=GridOrderedPinOrigins.slot P (2*e.val) := by
    have valid : 2*e.val < (m+1)*GridIdleLayout.each m n B*2 := by have := e.isLt; omega
    have inside : GridOrderedPinOrigins.slot P (2*e.val) < (n+1)^(m+1)*(q*d) := by
      rw [GridOrderedPinOrigins.slot,dite_eq_left valid]
      exact (GridOrderedPinOrigins.address P _).isLt
    change (seeded A b mem (9*A.J+2*e.val)).val=_
    rw [seeded_frame room mem _ (.inr (by omega)),published _ valid,Fin.val_cast_of_lt (by omega)]
  have cell (e : GridIdleLayout.Rails m n B) :
      GridSimRailScan.cellWord (banks A) (q*d) src e.val=(finFunctionFinEquiv (P.row e)).val := by
    rw [GridSimRailScan.cellWord,original,dest_cell P e positive]
  have touch (e : GridIdleLayout.Rails m n B) :
      GridSimRailScan.touchWord (banks A) (n+1) (q*d) src e.val=((P.row e) (P.direction e)).val := by
    unfold GridSimRailScan.touchWord
    change GridSimRailScan.cellWord (banks A) (q*d) src e.val /
        (src (A.railMap.powers+(src (A.railMap.dir+e.val)).val)).val % (n+1)=_
    rw [cell,dirval,strideval,GridLens.ordinal_digit]
  have before (i : ℕ) (hc : i < (banks A).cell ∨ (banks A).cell+b.rails ≤ i)
      (ht : i < (banks A).touch ∨ (banks A).touch+b.rails ≤ i) : out i=src i :=
    GridSimRailScan.frame (banks A) b.rails (n+1) (q*d) src i hc ht
  have powers (j : Fin (m+1)) : out (A.railMap.powers+j.val)=(((n+1)^j.val : ℕ) : Word W) := by
    have hj := j.isLt
    refine (before _ (.inr ?_) (.inl ?_)).trans (stride j) <;>
      dsimp only [banks,GridOrderedSources.Arena.railMap] <;> omega
  refine ⟨Procedure.Exec.then (seed_exec fit mem) (GridSimRailScan.execute scan src ?_),?_,
    (fun j => by simpa only [Nat.cast_pow,Nat.cast_add,Nat.cast_one] using powers j),frame room mem⟩
  · intro i hi
    let e : GridIdleLayout.Rails m n B := ⟨i,hi⟩
    exact (dirval e).trans_lt (P.direction e).isLt
  · intro e
    have er : e.val < b.rails := e.isLt
    refine ⟨(before _ (.inl ?_) (.inl ?_)).trans (dir e),?_,powers _,?_⟩
    · dsimp only [banks,GridOrderedSources.Arena.railMap]; omega
    · dsimp only [banks,GridOrderedSources.Arena.railMap]; omega
    · exact (GridSimRailScan.cell_at (banks A) b.rails (n+1) (q*d) src
        (scan.cellPower.trans (by have := scan.powerTouch; omega)) e.val er).trans (congrArg (fun a : ℕ => (a : Word W)) (cell e))
    · exact (GridSimRailScan.touch_at (banks A) b.rails (n+1) (q*d) src e.val er).trans
        (congrArg (fun a : ℕ => (a : Word W)) (touch e))

theorem text_bound (W : ℕ) (A : Arena) (b : Shape) :
    let M := program W A b
    M.labels+M.registers+M.slots ≤ 3000 := by
  let D := GridControllerIdle.scan W A b .direction
  let H := GridControllerIdle.scan W A b .powers
  let S := GridSimRailScan.build W (banks A) b.rails b.radix (b.q*b.pins)
  have size (c : GridControllerIdle.Column) (h : (GridControllerIdle.expr W A b c).work ≤ 128) :
      let T := GridControllerIdle.scan W A b c
      T.labels+T.registers+T.slots ≤ 1400 := by
    simp only [GridControllerIdle.scan,PhysicalInputPhases.writing,DescriptorExpr.Term.labels_eq,
      HeaderScan.binds_closed]
    omega
  have hd : D.labels+D.registers+D.slots ≤ 1400 := size .direction (GridControllerIdle.work_bound W A b .direction)
  have hh : H.labels+H.registers+H.slots ≤ 1400 := size .powers (GridControllerIdle.work_bound W A b .powers)
  have hs : S.labels+S.registers+S.slots=158 := GridSimRailScan.text_size ..
  change (D.labels+H.labels+S.labels)+(D.registers+H.registers+S.registers)+
    (D.slots+H.slots+S.slots) ≤ 3000
  omega

abbrev railCount (m n B : ℕ) := (m+1)*GridIdleLayout.each m n B

/-- After the factor allocator's genuine publication, this fixed procedure
delivers all inputs of the SIM source scatter, using the public direction
order. Frame equations protect the compact advice and exterior data. -/
theorem scheduled_input {F : Type} [Field F] [Fintype F] {W m n B q d h pc S N : ℕ}
    (A : Arena) (X : Catalyst.Approximation F (m+1) (q*d)) (code : RAM.FieldCode F W)
    (Q : FactorPinIntervals.Layout (Cell (m+1) n × Fin q) S N d)
    (port : GridIdleLayout.Rails m n B × Bool ↪ Fin S)
    (paired : ∀ e, Q.origin (port (e,true))=Q.origin (port (e,false)))
    (plan : GridPinPublisher.Plan) (dest : plan.source.dest=9*A.J)
    (literal : plan.source.literal=10*A.J)
    (mem original : Memory W) (positive : 0 < q*d)
    (fit : GridControllerIdle.Fits W A (GridControllerIdle.shape m n B h q d pc))
    (room : GridControllerIdle.Room A (GridControllerIdle.shape m n B h q d pc))
    (fits : GridOrderedSources.Fits (r:=railCount m n B) (n:=n) (w:=W) X A B)
    (count : Fin (m+1) → GridTicks.Tick (m+1) (n+1) q → ℕ)
    (published : GridPinPublisher.Published
      (PinAssignment.ofFactorIntervals Q GridIdleLayout.direction port paired) plan mem)
    (packed : ∀ i < GridApproximationAdvice.wordCount X, mem (A.pins.compact+i)=
      GridApproximationAdvice.paddedMemory X code B A.pins.compact original (A.pins.compact+i))
    (conserve : ∀ j t,(GridTicks.pairFiber GridIdleLayout.direction
      (fun e => GridTicks.index (Q.tick (port (e,false)))) j t).card=count j t)
    (enough : ∀ c j,X.width j ≤ ((GridTicks.pairsOn (count j) (GridTicks.lineTicks j c)) \
      (GridTicks.pairsOn (count j) (GridTicks.cellTicks c))).card) :
    let P := PinAssignment.ofFactorIntervals Q GridIdleLayout.direction port paired
    let b := GridControllerIdle.shape m n B h q d pc
    let D := A.data (railCount m n B) n
    let M := (program W A b).seq (GridOrderedDataRAM.prepare W D b.data (b.rails*2))
    let out := GridOrderedDataRAM.prepared D b.data (b.rails*2) (GridOrderedPinOrigins.slot P) (output A b mem)
    M.Exec mem out (cost W A b + (9+5*b.data+11*(b.rails*2))) ∧
      GridOrderedSources.Input X (Program.ofScheduled P X.width count conserve enough) code A B out original ∧
      ∀ i, i < 5*A.J → out i=mem i := by
  dsimp only
  let P := PinAssignment.ofFactorIntervals Q GridIdleLayout.direction port paired
  let b := GridControllerIdle.shape m n B h q d pc
  let mid := output A b mem
  let D := A.data (railCount m n B) n
  let out := GridOrderedDataRAM.prepared D b.data (b.rails*2) (GridOrderedPinOrigins.slot P) mid
  have endWord (i : ℕ) (hi : i < b.rails*2) :
      mem (9*A.J+i)=(GridOrderedPinOrigins.slot P i : Word W) := by
    rw [← dest]; exact published.1 i hi
  obtain ⟨geo,dec,pows,kept⟩ := publish A P rfl mem positive fits.high fit room endWord
  have data : b.data ≤ A.J := room.data
  have rails : b.rails ≤ A.J/8 := room.rails
  have axes : m+1 ≤ A.J/8 := room.axes
  have high := fits.high
  have gates := fits.words
  have origins (i : ℕ) (hi : i < b.rails*2) :
      mid (D.dest+i)=(GridOrderedPinOrigins.slot P i : Word W) := by
    change mid (9*A.J+i)=_
    exact (kept _ (.inr (by omega))).trans (endWord i hi)
  have literals (ci : Cell (m+1) n × Fin (q*d)) :
      mid (D.literal+(Ordered.dataCode ci).val)=((P.literal ci).toNat:Word W) := by
    change mid (10*A.J+_)=_
    refine (kept (10*A.J+(Ordered.dataCode ci).val) (.inr (by omega))).trans ?_
    rw [←literal]
    exact published.2 ci
  have compact (i : ℕ) (hi : i < GridApproximationAdvice.wordCount X) :
      mid (A.pins.compact+i)=GridApproximationAdvice.paddedMemory X code B A.pins.compact original
        (A.pins.compact+i) := (kept _ (.inl (by dsimp [GridOrderedSources.Arena.pins]; omega))).trans (packed i hi)
  have doubleRails : ((m+1)*GridIdleLayout.each m n B)*2 ≤ A.J := by
    change (m+1)*GridIdleLayout.each m n B ≤ A.J/8 at rails
    omega
  have after := GridOrderedSources.scatter_input X A P B code mid original count conserve enough
    fits data (by omega) doubleRails (by change 11*A.J+b.data < _; omega) dec pows origins literals compact
  refine ⟨Procedure.Exec.then geo after.1,after.2,?_⟩
  intro i hi
  have fr : out i=mid i := GridOrderedDataRAM.prepared_frame D _ _ _ mid i (fun j hj => by
    change j < (m+1)*GridIdleLayout.each m n B*2 at hj
    unfold GridOrderedPinOrigins.slot
    rw [dite_eq_left hj]
    exact (GridOrderedPinOrigins.address P ⟨j,hj⟩).isLt)
    (.inl (by change i < 11*A.J; omega))
  exact fr.trans (kept _ (.inl hi))

theorem receiver_text (W : ℕ) (A : Arena) (b : Shape) (D : GridOrderedDataRAM.Banks) :
    let M := (program W A b).seq (GridOrderedDataRAM.prepare W D b.data (b.rails*2))
    M.labels+M.registers+M.slots ≤ 3041 := by
  let G := program W A b
  have bound : G.labels+G.registers+G.slots ≤ 3000 := text_bound W A b
  change G.labels+(10+13)+(G.registers+(5+6))+(G.slots+(3+4)) ≤ 3041
  omega

theorem receiver_cost (W : ℕ) (A : Arena) (b : Shape) :
    cost W A b + (9+5*b.data+11*(b.rails*2)) ≤ 25+422*b.rails+400*b.axes+5*b.data := by
  have := cost_bound W A b
  omega

/-- The four controller scans, literal copy, and indexed endpoint scatter
fit the same cell-volume bound as the emitting controller. -/
theorem receiver_work_in_cells (W : ℕ) (A : Arena) (m n B h q d pc : ℕ)
    (sized : q*d ≤ B) (pos : 0 < B) :
    let b := GridControllerIdle.shape m n B h q d pc
    cost W A b + (9+5*b.data+11*(b.rails*2)) ≤ 25+1250*(m+1)*((n+1)^(m+1)*B) := by
  dsimp only
  let V := (m+1)*((n+1)^(m+1)*B)
  have unit : 1 ≤ (n+1)^(m+1)*B := Nat.mul_pos (Nat.pow_pos (Nat.succ_pos n)) pos
  have smaller : (n+1)^m ≤ (n+1)^(m+1) := Nat.pow_le_pow_right (Nat.succ_pos n) (Nat.le_succ m)
  have rails : (m+1)*(2*(n+1)^m*B) ≤ 2*V := by
    calc
      _ = 2*((m+1)*((n+1)^m*B)) := by ring
      _ ≤ 2*((m+1)*((n+1)^(m+1)*B)) :=
        Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left (m+1) (Nat.mul_le_mul_right B smaller))
  have ax : m+1 ≤ V := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (m+1) unit
  have pins : (n+1)^(m+1)*(q*d) ≤ V :=
    (Nat.mul_le_mul_left _ sized).trans (Nat.le_mul_of_pos_left _ (Nat.succ_pos m))
  have bound := receiver_cost W A (GridControllerIdle.shape m n B h q d pc)
  dsimp only [GridControllerIdle.shape,GridControllerIdle.Shape.data,GridControllerIdle.Shape.rails,
    GridIdleLayout.each] at bound ⊢
  apply bound.trans
  calc
    _ ≤ 25+422*(2*V)+400*V+5*V := by gcongr
    _ ≤ 25+1250*V := by omega
    _ = 25+1250*(m+1)*((n+1)^(m+1)*B) := by simp only [V,Nat.mul_assoc]

/-- Fixed native receiver phase with a composable postcondition on its complete rail map and exterior prefix. -/
theorem raw_spec {F : Type} [Field F] [Fintype F] {W m n B q d h pc S N : ℕ}
    (A : Arena) (X : Catalyst.Approximation F (m+1) (q*d)) (code : RAM.FieldCode F W)
    (Q : FactorPinIntervals.Layout (Cell (m+1) n × Fin q) S N d)
    (port : GridIdleLayout.Rails m n B × Bool ↪ Fin S)
    (paired : ∀ e, Q.origin (port (e,true))=Q.origin (port (e,false)))
    (plan : GridPinPublisher.Plan) (dest : plan.source.dest=9*A.J)
    (literal : plan.source.literal=10*A.J)
    (original : Memory W) (pin : Fin (railCount m n B*2) → Bool) (positive : 0 < q*d)
    (fit : GridControllerIdle.Fits W A (GridControllerIdle.shape m n B h q d pc))
    (room : GridControllerIdle.Room A (GridControllerIdle.shape m n B h q d pc))
    (fits : GridOrderedSources.Fits (r:=railCount m n B) (n:=n) (w:=W) X A B)
    (count : Fin (m+1) → GridTicks.Tick (m+1) (n+1) q → ℕ)
    (conserve : ∀ j t,(GridTicks.pairFiber GridIdleLayout.direction
      (fun e => GridTicks.index (Q.tick (port (e,false)))) j t).card=count j t)
    (enough : ∀ c j,X.width j ≤ ((GridTicks.pairsOn (count j) (GridTicks.lineTicks j c)) \
      (GridTicks.pairsOn (count j) (GridTicks.cellTicks c))).card) :
    let P := PinAssignment.ofFactorIntervals Q GridIdleLayout.direction port paired
    let b := GridControllerIdle.shape m n B h q d pc
    let D := A.data (railCount m n B) n
    ((program W A b).seq (GridOrderedDataRAM.prepare W D b.data (b.rails*2))).Spec
      (fun mem => GridPinPublisher.Published P plan mem ∧
        (∀ i < GridApproximationAdvice.wordCount X, mem (A.pins.compact+i)=
          GridApproximationAdvice.paddedMemory X code B A.pins.compact original (A.pins.compact+i)) ∧
        ∀ i : Fin (railCount m n B*2),mem i.val=RAM.BitLayout.bitWord W (pin i))
      (fun _ out => GridOrderedSources.Raw X (Program.ofScheduled P X.width count conserve enough)
        code A B pin out original)
      (cost W A b + (9+5*b.data+11*(b.rails*2))) := by
  dsimp only
  intro pcs regs pubs machine pcEntry reg pub exit rom hardware cfg mem start pre
  obtain ⟨published,compact,exterior⟩ := pre
  obtain ⟨run,installed,low⟩ := scheduled_input A X code Q port paired plan dest literal mem original
    positive fit room fits count published compact conserve enough
  obtain ⟨t,le,c,o,advance,atExit,eqn⟩ := run machine pcEntry reg pub exit rom hardware cfg mem start rfl
  subst o
  refine ⟨t,le,c,_,advance,atExit,installed,?_⟩
  intro i
  have roomRails := room.rails
  change railCount m n B ≤ A.J/8 at roomRails
  have bound : i.val < railCount m n B*2 := i.isLt
  have below : i.val < 5*A.J := by omega
  exact (low i.val below).trans (exterior i)


end
end Hierarchy.GridControllerSimGeometry

end OAI
