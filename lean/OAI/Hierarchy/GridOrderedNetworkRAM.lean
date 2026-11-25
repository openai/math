import OAI.ThreeFlat.RAM.PhysicalExactRun
import OAI.Hierarchy.GridOrderedRowRAM
import OAI.Hierarchy.GridWiringNetwork

namespace OAI
/-! # Native assembly of the physical table of the programmed wiring -/

namespace Hierarchy.GridOrderedNetworkRAM
open UniversalGrid ThreeFlat
open RAM RAM.BitLayout RAM.PhysicalProcedure RAM.GuardedDescriptor GridOrderedRowRAM
open Computability.VPVNP.BurstRAM
open scoped Fin.CommRing

variable {F : Type} [Field F] [Fintype F] {r L w : ℕ} {P : Type} [Fintype P]
variable (W : Wiring (Fin r) P L) (N : BitNetwork F (Fintype.card P)) (code : FieldCode F w)
noncomputable section


/-- Real memory intervals furnished by the port/equality emitter and X loader. -/
structure Mounted (S : Layout) (m : Memory w) : Prop where
  gate : ∀ (i : Fin N.cells) (j : Fin 11), m (S.gate+11*i.val+j.val) = record N code i j
  pin : ∀ (c : Fin L) (i : Fin (Fintype.card P)), m (S.pin+(Fintype.card P)*c.val+i.val) =
    (sourceAddress (W.copyInput c i):Word w)
  left : ∀ a : Fin W.equal.length, m (S.edge+2*a.val+0) =
    (sourceAddress (Wiring.source (W.equal.get a).1):Word w)
  right : ∀ a : Fin W.equal.length, m (S.edge+2*a.val+1) =
    (sourceAddress (Wiring.source (W.equal.get a).2):Word w)

def rowStart := cellsBase (r*2) (W.network N).internal
def edgeStart := rowStart W N+11*(L*N.cells)
def rowStop := edgeStart W N+11*W.equal.length

def copyLayout (S : Layout) : Layout := { S with output := rowStart W N }
def edgeLayout (S : Layout) : Layout := { S with output := edgeStart W N }

def build (S : Layout) : Procedure w :=
  (procedure (copyLayout W N S) (Fintype.card P) N.cells N.internal 0 (r*2) W.internal (11*(L*N.cells))
    (code.encode 0) (code.encode 1)).seq
  (procedure (edgeLayout W N S) 0 0 0 1 (r*2) W.internal (11*W.equal.length)
    (code.encode 0) (code.encode 1))

private theorem dest_index {base n stride a : ℕ} (lo : base ≤ a) (hi : a < base+stride*n) :
    ∃ i : Fin n, ∃ j : Fin stride, a=base+stride*i.val+j.val := by
  have h : stride>0 := by by_contra! trivial; simp [show stride=0 by omega] at hi; omega
  have val : a-base < stride*n := by omega
  have iv : (a-base)/stride < n := (Nat.div_lt_iff_lt_mul h).mpr (by simpa [Nat.mul_comm] using val)
  exact ⟨⟨_,iv⟩,⟨_,Nat.mod_lt (a-base) h⟩,by dsimp; have := Nat.div_add_mod (a-base) stride; omega⟩

omit [Field F] [Fintype F] in
private theorem mounted_frame (S : Layout) (m m₀ : Memory w) (mounted : Mounted W N code S m₀)
    (lo hi : ℕ) (frame : DescriptorScan.agreesOutside lo hi m m₀)
    (away : hi ≤ S.gate ∧ hi ≤ S.pin ∧ hi ≤ S.edge) : Mounted W N code S m where
  gate i j := (frame _ (Or.inr (by omega))).trans (mounted.gate i j)
  pin c i := (frame _ (Or.inr (by omega))).trans (mounted.pin c i)
  left i := (frame _ (Or.inr (by omega))).trans (mounted.left i)
  right i := (frame _ (Or.inr (by omega))).trans (mounted.right i)

/-- Decode an absolute copy address against the compact gate and port banks. -/
theorem copy_word_at (S : Layout) (m : Memory w) (mounted : Mounted W N code S m)
    (pin : Fin (r*2) → Bool) (a : Word w)
    (ha : rowStart W N ≤ a.val) (hb : a.val < rowStart W N+11*(L*N.cells))
    (gateFit : S.gate+11*N.cells ≤ 2^w) (pinFit : S.pin+(Fintype.card P)*L ≤ 2^w)
    (sourceFit : 2+(Fintype.card P)+N.internal < 2^w) (widthFit : N.cells < 2^w) (eleven : 11 < 2^w) :
    (program w).eval (operands (copyLayout W N S) (Fintype.card P) N.cells N.internal 0 (r*2) W.internal
      (code.encode 0) (code.encode 1)) m (fun _ => a) =
      memory (W.network N) code pin (fun _=>false) a.val := by
  obtain ⟨i,j,hij⟩ := dest_index ha hb
  obtain ⟨⟨c,u⟩,rfl⟩ := finProdFinEquiv.surjective i
  have loc : a.val=recordAddress (rowStart W N) N.cells 0 c.val u.val j.val := by
    simpa [recordAddress,copyLayout,finProdFinEquiv_apply_val,Nat.mul_comm,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using hij
  have answer := copy_at (copyLayout W N S) N W.copyInput code m mounted.gate mounted.pin
    gateFit pinFit sourceFit widthFit eleven c u j (loc ▸ a.isLt)
  have dest : memory (W.network N) code pin (fun _=>false) a.val = record (W.network N) code (W.copyRow N c u) j := by
    rw [loc]
    have pos := read_record (W.network N) code pin (fun _=>false) (W.copyRow N c u) j
    simpa [recordAddress,Wiring.copyRow_val,rowStart,Nat.mul_comm,Nat.add_comm,
      Nat.add_left_comm,Nat.add_assoc] using pos
  have addr : (recordAddress (copyLayout W N S).output N.cells 0 c.val u.val j.val : Word w)=a := by
    change ((recordAddress (rowStart W N) N.cells 0 c.val u.val j.val : ℕ):Word w)=a
    rw [←loc]
    exact Fin.ext (Fin.val_cast_of_lt a.isLt)
  rw [addr] at answer
  exact answer.trans ((W.copy_record N code c u j).symm.trans dest.symm)

/-- Decode an absolute appended equality address against its two physical pointers. -/
theorem edge_word_at (S : Layout) (m : Memory w) (mounted : Mounted W N code S m)
    (pin : Fin (r*2) → Bool) (a : Word w)
    (ha : edgeStart W N ≤ a.val) (hb : a.val < edgeStart W N+11*W.equal.length)
    (edgeFit : S.edge+2*W.equal.length ≤ 2^w) (eleven : 11 < 2^w) :
    (program w).eval (operands (edgeLayout W N S) 0 0 0 1 (r*2) W.internal
      (code.encode 0) (code.encode 1)) m (fun _ => a) =
      memory (W.network N) code pin (fun _=>false) a.val := by
  obtain ⟨i,j,hij⟩ := dest_index ha hb
  have loc : a.val=recordAddress (edgeStart W N) 0 1 i.val 0 j.val := by
    simpa [edgeLayout,recordAddress,Nat.add_assoc] using hij
  let left := fun u : Fin W.equal.length => Wiring.source (W.equal.get u).1
  let right := fun u : Fin W.equal.length => Wiring.source (W.equal.get u).2
  have answer := edge_at (edgeLayout W N S) left right code m mounted.left mounted.right
    edgeFit eleven i j (loc ▸ a.isLt)
  have dest : memory (W.network N) code pin (fun _=>false) a.val = record (W.network N) code (W.edgeRow N i) j := by
    rw [loc]
    have pos := read_record (W.network N) code pin (fun _=>false) (W.edgeRow N i) j
    simpa [recordAddress,Wiring.edgeRow_val,edgeStart,rowStart,Nat.mul_add,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using pos
  have addr : (recordAddress (edgeLayout W N S).output 0 1 i.val 0 j.val : Word w)=a := by
    change ((recordAddress (edgeStart W N) 0 1 i.val 0 j.val : ℕ):Word w)=a
    rw [←loc]
    exact Fin.ext (Fin.val_cast_of_lt a.isLt)
  rw [addr] at answer
  exact answer.trans ((W.edge_record N code i j).symm.trans dest.symm)

def target := memory (W.network N) code (fun _=>false) (fun _=>false)

def image (m : Memory w) :=
  fillSegment (edgeStart W N) (11*W.equal.length) (target W N code)
    (fillSegment (rowStart W N) (11*(L*N.cells)) (target W N code) m)

/-- Every actual instruction path initializes the eleven-word records of the
flattened network. Only the two source maps and the one small template are
required in the initial memory. -/
theorem build_spec (S : Layout) (fit : rowStop W N < 2^w)
    (away : rowStop W N ≤ S.gate ∧ rowStop W N ≤ S.pin ∧ rowStop W N ≤ S.edge)
    (gateFit : S.gate+11*N.cells ≤ 2^w) (pinFit : S.pin+(Fintype.card P)*L ≤ 2^w)
    (edgeFit : S.edge+2*W.equal.length ≤ 2^w) (sourceFit : 2+(Fintype.card P)+N.internal < 2^w)
    (widthFit : N.cells < 2^w) (eleven : 11 < 2^w) :
    (build W N code S).Spec (Mounted W N code S)
      (fun m o => o=image W N code m) (8+11*(L*N.cells+W.equal.length)*284) := by
  let dst := target W N code
  have end1 : rowStart W N+11*(L*N.cells) ≤ rowStop W N := by unfold rowStop edgeStart; omega
  have stop1 := lt_of_le_of_lt end1 fit
  have C : Procedure.Spec _ _ _ _ := scan_spec (copyLayout W N S) (Fintype.card P) N.cells N.internal 0 (r*2) W.internal
    (11*(L*N.cells)) (code.encode 0) (code.encode 1) (Mounted W N code S) dst stop1 (by
      intro initial mounted a m ha hb frame
      have reads := mounted_frame W N code S m initial mounted _ _ frame
        ⟨end1.trans away.1,end1.trans away.2.1,end1.trans away.2.2⟩
      exact copy_word_at W N code S m reads _ a ha hb gateFit pinFit sourceFit widthFit eleven)
  have D : Procedure.Spec _ _ _ _ := scan_spec (edgeLayout W N S) 0 0 0 1 (r*2) W.internal
    (11*W.equal.length) (code.encode 0) (code.encode 1) (Mounted W N code S) dst fit (by
      intro initial mounted a m ha hb frame
      have reads := mounted_frame W N code S m initial mounted _ _ frame away
      exact edge_word_at W N code S m reads _ a ha hb edgeFit eleven)
  -- Keep the mounted banks in the intermediate postcondition for sequential linking.
  intro PP RR K M pc reg pub exit installed data c m start mounted
  let A := procedure (copyLayout W N S) (Fintype.card P) N.cells N.internal 0 (r*2) W.internal
    (11*(L*N.cells)) (code.encode 0) (code.encode 1)
  let B := procedure (edgeLayout W N S) 0 0 0 1 (r*2) W.internal
    (11*W.equal.length) (code.encode 0) (code.encode 1)
  let mid := fillSegment (rowStart W N) (11*(L*N.cells)) dst m
  have cc : A.Exec m mid (4+(11*(L*N.cells))*(2*(program w).binds+4)) := Procedure.Spec.exec C m mounted
  have next : Mounted W N code S mid := by
    apply mounted_frame W N code S mid m mounted (rowStart W N) (edgeStart W N)
    · intro i outside
      apply ite_eq_right
      change ¬(rowStart W N ≤ i ∧ i < edgeStart W N)
      omega
    · exact ⟨end1.trans away.1,end1.trans away.2.1,end1.trans away.2.2⟩
  have dc : B.Exec mid (image W N code m) (4+(11*W.equal.length)*(2*(program w).binds+4)) := Procedure.Spec.exec D mid next
  obtain ⟨t,ht,cf,mm,run,stop,final⟩ := Procedure.Exec.then cc dc M pc reg pub exit installed data c m start rfl
  refine ⟨t,ht.trans ?_,cf,mm,run,stop,final⟩
  rw [program_size]
  omega

end
end Hierarchy.GridOrderedNetworkRAM

end OAI
