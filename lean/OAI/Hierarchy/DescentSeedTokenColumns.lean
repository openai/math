import OAI.Hierarchy.DescentSeedTokenROM
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # Native one-based seed tokens for old, hub and unoccupied actor rows -/

namespace Hierarchy.DescentSeedTokenColumns
open DescentSixParty.Chronology DescentSIMDLookup DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

def out (base a M H G : ℕ) := base+size a M (H*chunks G M)

def page (base a M H G q : ℕ) : Bank :=
  ⟨out base a M H G+q*(H*chunks G M),Nat.clog 2 (H*chunks G M)⟩

def body (base a M n : ℕ) (old : Bank) : Expr :=
  let t := fun j => Expr.lookup (column base a M n j) .row
  .branch .eq (t 0) (.lit 0) (t 2)
    (.op .mask (.lookup (dictionary base a M) (.lookup old (t 1))) (t 3))

def expressions {X : ℕ} (base a M n : ℕ) (columns : Fin X→Bank) :=
  List.ofFn (fun q => body base a M n (columns q))

def scanPhase {X : ℕ} (w G M a base H : ℕ) (columns : Fin X→Bank) : NativePhase w :=
  let n := H*chunks G M
  let ps := ProbeStage.Native.columns n (out base a M H G) (expressions base a M n columns)
  ⟨program w ps,clock ps,result ps,@program_cheap w ps⟩

def phase {X O H b : ℕ} (w G M a base : ℕ) (src : Fin H→Option (Option (Fin O))) (hub : Cell b)
    (columns : Fin X→Bank) : NativePhase w :=
  (prepare w G M a base src hub).seq (scanPhase w G M a base H columns)

private theorem geometry {a M base n w : ℕ} (room : base+size a M n<2^w) :
    (dictionary base a M).Fits w (base+size a M n) ∧
    ∀ t : ℕ, t<4 → (column base a M n t).Fits w (base+size a M n) := by
  change base+(2^(a*M)+4*span n)<2^w at room
  constructor
  · change 0<2^(a*M) ∧ 2^(a*M)<2^w ∧ base+2^(a*M) ≤ base+(2^(a*M)+4*span n)
    exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
  · intro t ht
    have place := Nat.mul_le_mul_right (span n) (show t+1≤4 by omega)
    rw [Nat.add_mul,Nat.one_mul] at place
    change 0 < span n ∧ span n<2^w ∧ base+2^(a*M)+t*span n+span n ≤ base+(2^(a*M)+4*span n)
    have dictPos := Nat.two_pow_pos (a*M)
    exact ⟨span_pos _,by omega,by omega⟩

private theorem safe_body {base a M n w : ℕ} (old : Bank) (safe : old.Fits w base)
    (room : base+size a M n<2^w) : (body base a M n old).Fits w (base+size a M n) := by
  obtain ⟨dict,sheet⟩ := geometry room
  have earlier : old.Fits w (base+size a M n) :=
    ⟨safe.1,safe.2.1,safe.2.2.trans (Nat.le_add_right ..)⟩
  exact ⟨⟨sheet 0 (by decide),trivial⟩,trivial,⟨sheet 2 (by decide),trivial⟩,
    ⟨dict,earlier,sheet 1 (by decide),trivial⟩,sheet 3 (by decide),trivial⟩

private theorem all_safe {X a base M n w : ℕ} (columns : Fin X→Bank) (safe : ∀ q,(columns q).Fits w base)
    (room : base+size a M n<2^w) :
    ∀ e∈expressions base a M n columns,e.Fits w (base+size a M n) := by
  intro e he
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp he
  exact safe_body _ (safe q) room

theorem any {X O H b : ℕ} (w G M a base : ℕ) (src : Fin H→Option (Option (Fin O))) (hub : Cell b)
    (columns : Fin X→Bank) (m : Memory w) (safe : ∀ q,(columns q).Fits w base)
    (room : out base a M H G+X*(H*chunks G M)<2^w) :
    let p := phase w G M a base src hub columns
    p.Runs m ∧ ∀ z,z < base ∨ out base a M H G+X*(H*chunks G M) ≤ z → p.image m z=m z := by
  let n := H*chunks G M
  let output := out base a M H G
  let es := expressions base a M n columns
  let old := prepare w G M a base src hub
  have len : es.length=X := List.length_ofFn
  have low : base+size a M n<2^w := (Nat.le_add_right _ _).trans_lt room
  have earlier : base ≤ output := Nat.le_add_right ..
  obtain ⟨pre,_,frame⟩ := prepared w G M a base src hub m low
  have runs : (scanPhase w G M a base H columns).Runs (old.image m) := by
    intro P R K machine
    exact ProbeStage.Native.columns_exec es (old.image m)
      (ProbeStage.Native.columns_safe es le_rfl (all_safe columns safe low)
        (by simpa only [len] using room : output+es.length*n<2^w)) machine
  refine ⟨NativePhase.seq_runs old _ m pre runs,?_⟩
  intro z hz
  change z < base ∨ output+X*n ≤ z at hz
  have stay := ProbeStage.Native.columns_frame (n:=n) (base:=output) es (old.image m) (address:=z)
    (by rw [len]; exact hz.imp (fun h=>h.trans_le earlier) id : z < output ∨ output+es.length*n ≤ z)
  exact stay.trans (frame z (hz.imp id (fun h=>(Nat.le_add_right output _).trans h)))

private theorem read_body {a b w X O H G M base : ℕ} (src : Fin H→Option (Option (Fin O))) (hub : Cell b)
    (columns : Fin X→Bank) (xs : Fin X→Fin O→Fin G→Cell a) (m : Memory w)
    (tables : Tables G M a base src hub m) (safe : ∀q,(columns q).Fits w base)
    (space : out base a M H G<2^w) (width : b*M ≤ w) (capacity : ∀q,O*chunks G M≤(columns q).size)
    (reads : ∀q (p : Row O G M),m ((columns q).base+(row O G M p).val)=((data (xs q) p).val : Word w))
    (q : Fin X) (p : Row H G M) :
    (body base a M (H*chunks G M) (columns q)).eval m ((row H G M p).val : Word w)=
      ((data (values src hub xs q) p).val : Word w) := by
  let n := H*chunks G M
  let idx : Word w := ((row H G M p).val : Word w)
  obtain ⟨dict,sheet⟩ := geometry (show base+size a M n<2^w from space)
  have get (t : ℕ) (ht : t<4) : (column base a M n t).read m idx =
      m ((column base a M n t).base+(row H G M p).val) :=
    DescentPackedZip.bank_read _ m ((row H G M p).isLt.trans_le (span_ge n)) (sheet t ht)
  have flag := (get 0 (by decide)).trans (tables.flag p)
  have addr := (get 1 (by decide)).trans (tables.addr p)
  have fallbackRead := (get 2 (by decide)).trans (tables.other p)
  have mask := (get 3 (by decide)).trans (tables.mask p)
  let pass := (column base a M n 0).read m idx
  change (if (pass == (0 : Word w)) then (column base a M n 2).read m idx else
    BinaryOp.bitAnd.eval ((dictionary base a M).read m ((columns q).read m ((column base a M n 1).read m idx)))
      ((column base a M n 3).read m idx)) = _
  have blank (h : oldFlag (src p.1)=0) :
      (if (pass == (0 : Word w)) then (column base a M n 2).read m idx else
        BinaryOp.bitAnd.eval ((dictionary base a M).read m ((columns q).read m ((column base a M n 1).read m idx)))
          ((column base a M n 3).read m idx)) = (fallback src hub p : Word w) := by
    have zero : pass=0 := by simpa only [h,Nat.cast_zero] using flag
    simp only [zero,beq_self_eq_true,ite_true]; exact fallbackRead
  cases hs : src p.1 with
  | none =>
    rw [blank (by simp [hs,oldFlag])]
    simp only [fallback,data,values,hs]
  | some opt =>
    cases opt with
    | none =>
      rw [blank (by simp [hs,oldFlag])]
      simp only [fallback,data,values,hs]
    | some v =>
      let r : Row O G M := (v,p.2)
      have nonzero : (1 : ℕ)<2^w := by
        change base+(2^(a*M)+4*span n)<2^w at space
        have spanPos := span_pos n
        have dictPos := Nat.two_pow_pos (a*M)
        omega
      have one : pass=(1 : Word w) := by simpa only [hs,oldFlag,Nat.cast_one] using flag
      have miss : ¬(pass == (0 : Word w))=true := by
        rw [one,beq_iff_eq]
        intro eq
        have bad := congrArg Fin.val eq
        change ((1:ℕ):Word w).val=((0:ℕ):Word w).val at bad
        rw [Fin.val_cast_of_lt nonzero,Fin.val_cast_of_lt (by omega)] at bad
        omega
      have iread : (column base a M n 1).read m idx=((row O G M r).val : Word w) := by
        simpa only [oldRow,hs,r] using addr
      have donor := (DescentPackedZip.bank_read (columns q) m
        ((row O G M r).isLt.trans_le (capacity q)) (safe q)).trans (reads q r)
      have look := (DescentPackedZip.bank_read (dictionary base a M) m (data (xs q) r).isLt dict).trans
        (tables.dict (data (xs q) r))
      rw [ite_eq_right miss,iread,donor,look,mask]
      have wordFit := (table (M:=M) (bump b) (data (xs q) r)).isLt.trans_le (Nat.pow_le_pow_right (by decide) width)
      have maskFit : maskWord b M G p.2.val<2^w :=
        (Nat.pred_lt (Nat.two_pow_pos _).ne').trans_le (Nat.pow_le_pow_right (by decide)
          ((Nat.mul_le_mul_left b (Nat.min_le_left ..)).trans width))
      let resultWord := (table (M:=M) (bump b) (data (xs q) r)).val
      change (((resultWord : Word w).val &&& ((maskWord b M G p.2.val : Word w).val) : ℕ) : Word w) = _
      change resultWord < 2^w at wordFit
      rw [Fin.val_cast_of_lt wordFit,Fin.val_cast_of_lt maskFit]
      have same : data (fun v g=>bump b (xs q v g)) r=data (values src hub xs q) p := by
        simp only [r,data,values,hs]
      exact congrArg (fun x : ℕ => (x : Word w)) ((mask_bump (b:=b) (xs q) r).trans (congrArg Fin.val same))

/-- One literal dictionary and row directory serve every old role page.
The selected old, hub, and ghost output words are all written by the physical scan. -/
theorem run {X O H b : ℕ} (w G M a base : ℕ) (src : Fin H→Option (Option (Fin O))) (hub : Cell b)
    (columns : Fin X→Bank) (xs : Fin X→Fin O→Fin G→Cell a) (m : Memory w)
    (safe : ∀q,(columns q).Fits w base) (room : out base a M H G+X*(H*chunks G M)<2^w)
    (width : b*M ≤ w) (capacity : ∀q,O*chunks G M≤(columns q).size)
    (reads : ∀q (p : Row O G M),m ((columns q).base+(row O G M p).val)=((data (xs q) p).val : Word w)) :
    let p := phase w G M a base src hub columns
    p.Runs m ∧ (∀ q (r : Row H G M),p.image m ((page base a M H G q.val).base+(row H G M r).val)=
      ((data (values src hub xs q) r).val : Word w)) ∧
      (∀ z,z < base ∨ out base a M H G+X*(H*chunks G M) ≤ z → p.image m z=m z) := by
  let n := H*chunks G M
  let es := expressions base a M n columns
  let prep := prepare w G M a base src hub
  have len : es.length=X := List.length_ofFn
  have low : out base a M H G < 2^w := (Nat.le_add_right _ _).trans_lt room
  obtain ⟨runs,kept⟩ := any w G M a base src hub columns m safe room
  obtain ⟨_,tables,frame⟩ := prepared w G M a base src hub m low
  have old (q : Fin X) (p : Row O G M) :
      prep.image m ((columns q).base+(row O G M p).val)=((data (xs q) p).val : Word w) := by
    have bound := (Nat.add_lt_add_left ((row O G M p).isLt.trans_le (capacity q)) (columns q).base).trans_le (safe q).2.2
    exact (frame _ (Or.inl bound)).trans (reads q p)
  refine ⟨runs,?_,kept⟩
  intro q r
  have here := ProbeStage.Native.columns_read es (prep.image m) le_rfl (all_safe columns safe low)
    q.val (by simpa only [len] using q.isLt) (row H G M r)
  simp only [es,expressions,List.getElem_ofFn] at here
  exact here.trans (read_body src hub columns xs (prep.image m) tables safe low width capacity old q r)

private theorem work {X : ℕ} (base a M n : ℕ) (columns : Fin X→Bank) :
    ∀ e∈expressions base a M n columns,e.work≤41 := by
  intro e h
  obtain ⟨q,rfl⟩ := List.mem_ofFn.mp h
  exact le_rfl

theorem ticks_le {X O H b : ℕ} (w G M a base : ℕ) (src : Fin H→Option (Option (Fin O)))
    (hub : Cell b) (columns : Fin X→Bank) :
    (phase w G M a base src hub columns).ticks ≤
      4+10*size a M (H*chunks G M)+(4+X*(4+86*(H*chunks G M))) := by
  apply Nat.add_le_add_left
  simpa only [scanPhase,expressions,List.length_ofFn,show 2*41+4=86 by decide,Nat.mul_comm 86] using
    ProbeStage.Native.columns_clock (H*chunks G M) (out base a M H G) 41
      (expressions base a M (H*chunks G M) columns) (work base a M (H*chunks G M) columns)

theorem names_le {X O H b : ℕ} (w G M a base : ℕ) (src : Fin H→Option (Option (Fin O)))
    (hub : Cell b) (columns : Fin X→Bank) :
    DescentStaticWordColumn.names (phase w G M a base src hub columns).program ≤
      15*(size a M (H*chunks G M)+1)+(15+X*(11+4*41)) := by
  change DescentStaticWordColumn.names ((prepare w G M a base src hub).program.seq
    (scanPhase w G M a base H columns).program) ≤ _
  rw [DescentStaticWordColumn.names_seq]
  change DescentStaticWordColumn.names (DescentStaticWordColumn.program _ _ _ _) + _ ≤ _
  rw [DescentStaticWordColumn.names_mount]
  apply Nat.add_le_add_left
  simpa only [scanPhase,ProbeStage.Native.text,DescentStaticWordColumn.names,expressions,List.length_ofFn] using
    ProbeStage.Native.columns_text w (H*chunks G M) (out base a M H G) 41
      (expressions base a M (H*chunks G M) columns) (work base a M (H*chunks G M) columns)


end
end Hierarchy.DescentSeedTokenColumns

end OAI
