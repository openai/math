import OAI.Hierarchy.DescentResetStemRaw
import OAI.Hierarchy.DescentResetStemHeaderROM
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.ProbeStageProgramSize

namespace OAI
/-! # Broadcast runtime reset descriptors over the packed groups of each actor -/
namespace Hierarchy.DescentResetStemHeaders
open DescentSixParty.Chronology DescentSIMDLookup DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section

def outputBase (H G M b base : ℕ) := base+romSize b (H*chunks G M)

def body (H G M b raw base j : ℕ) : Expr :=
  let n := H*chunks G M
  .op .mask (.lookup (wideBank base b) (.lookup (rawBank raw H j) (.lookup (actorBank base b n) .row)))
    (.lookup (maskBank base b n) .row)

def passes (K H G M b raw base : ℕ) : List Pass :=
  ProbeStage.Native.columns (H*chunks G M) (outputBase H G M b base)
    (List.ofFn (fun j : Fin K => body H G M b raw base j.val))

def publish (w K H G M b raw base : ℕ) : NativePhase w :=
  let ps := passes K H G M b raw base
  ⟨program w ps, clock ps, result ps, @program_cheap w ps⟩

def phase (w K H G M b raw base : ℕ) : NativePhase w :=
  (prepare w H G M b base).seq (publish w K H G M b raw base)

def outBank (H G M b base j : ℕ) : Bank :=
  ⟨outputBase H G M b base+j*(H*chunks G M), Nat.clog 2 (H*chunks G M)⟩

def expr (H G M b base j : ℕ) : Expr := .lookup (outBank H G M b base j) .row

theorem romSize_le (b n : ℕ) : romSize b n ≤ 2^b+4*n+2 := by
  have h := span_le n
  unfold romSize
  omega

theorem expr_fits {w K H G M b base limit : ℕ} (j : Fin K)
    (room : outputBase H G M b base+K*(H*chunks G M)+span (H*chunks G M) ≤ limit)
    (word : limit < 2^w) : (expr H G M b base j.val).Fits w limit := by
  let n := H*chunks G M
  have below : j.val*n ≤ K*n := Nat.mul_le_mul_right n (Nat.le_of_lt j.isLt)
  change (0 < span n ∧ span n < 2^w ∧ outputBase H G M b base+j.val*n+span n ≤ limit) ∧ True
  change outputBase H G M b base+K*n+span n ≤ limit at room
  exact ⟨⟨span_pos _, by omega, by omega⟩, trivial⟩

theorem ticks (w K H G M b raw base : ℕ) :
    (phase w K H G M b raw base).ticks ≤
      4+10*romSize b (H*chunks G M)+(4+K*(4+54*(H*chunks G M))) := by
  let es := List.ofFn (fun j : Fin K => body H G M b raw base j.val)
  have cap : ∀ e ∈ es, e.work ≤ 25 := by
    intro e member
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
    exact le_rfl
  have work := ProbeStage.Native.columns_clock (H*chunks G M) (outputBase H G M b base) 25 es cap
  simpa only [phase, NativePhase.seq, prepare, publish, passes, es, List.length_ofFn, Nat.mul_comm 54] using
    Nat.add_le_add_left work (4+10*romSize b (H*chunks G M))

theorem names_le (w K H G M b raw base : ℕ) :
    DescentStaticWordColumn.names (phase w K H G M b raw base).program ≤
      15*(romSize b (H*chunks G M)+1)+(15+K*(11+4*25)) := by
  let es := List.ofFn (fun j : Fin K => body H G M b raw base j.val)
  have cap : ∀ e∈es, e.work ≤ 25 := by
    intro e member
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp member
    exact le_rfl
  change DescentStaticWordColumn.names ((DescentStaticWordColumn.program w base (literals H G M b)
    (romSize b (H*chunks G M))).seq (program w (passes K H G M b raw base))) ≤ _
  rw [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount]
  apply Nat.add_le_add_left
  simpa only [DescentStaticWordColumn.names,ProbeStage.Native.text,passes,es,List.length_ofFn] using
    ProbeStage.Native.columns_text w (H*chunks G M) (outputBase H G M b base) 25 es cap

theorem body_fits {w K H G M b raw base : ℕ}
    (rawRoom : raw+K*H+span H ≤ base) (space : outputBase H G M b base+K*(H*chunks G M) < 2^w)
    (j : Fin K) : (body H G M b raw base j.val).Fits w (outputBase H G M b base) := by
  let n := H*chunks G M
  let out := outputBase H G M b base
  have endMask : base+2^b+span n+span n = out := by
    change base+2^b+span n+span n=base+(2^b+2*span n)
    omega
  have endActor : base+2^b+span n ≤ out := (Nat.le_add_right _ _).trans endMask.le
  have endWide : base+2^b ≤ out := (Nat.le_add_right _ _).trans endActor
  have before : base ≤ out := (Nat.le_add_right _ _).trans endWide
  have outFit : out < 2^w := (Nat.le_add_right _ _).trans_lt space
  have spanFit : span n < 2^w := (Nat.le_add_left _ _).trans_lt (endActor.trans_lt outFit)
  have rawEnd : raw+j.val*H+span H ≤ out := by
    have below : raw+j.val*H+span H ≤ raw+K*H+span H :=
      Nat.add_le_add_right (Nat.add_le_add_left (Nat.mul_le_mul_right H j.isLt.le) raw) _
    exact below.trans (rawRoom.trans before)
  have rawFit : (rawBank raw H j.val).Fits w out := by
    change 0 < span H ∧ span H < 2^w ∧ raw+j.val*H+span H ≤ out
    exact ⟨span_pos _,(Nat.le_add_left _ _).trans_lt (rawEnd.trans_lt outFit),rawEnd⟩
  have wFit : (wideBank base b).Fits w out := by
    change 0 < 2^b ∧ 2^b < 2^w ∧ base+2^b ≤ out
    exact ⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (endWide.trans_lt outFit),endWide⟩
  have aFit : (actorBank base b n).Fits w out := ⟨span_pos _,spanFit,endActor⟩
  have mFit : (maskBank base b n).Fits w out := ⟨span_pos _,spanFit,endMask.le⟩
  exact ⟨⟨wFit,rawFit,aFit,trivial⟩,mFit,trivial⟩

/-- Execution and the untouched memory frame hold on arbitrary input words. -/
theorem any {w K H G M b raw base : ℕ} (m : Memory w)
    (rawRoom : raw+K*H+span H ≤ base)
    (space : outputBase H G M b base+K*(H*chunks G M) < 2^w) :
    let p := phase w K H G M b raw base
    p.Runs m ∧ (∀ a, a < base ∨ outputBase H G M b base+K*(H*chunks G M) ≤ a → p.image m a=m a) := by
  let n := H*chunks G M
  let out := outputBase H G M b base
  let prep := prepare w H G M b base
  let es := List.ofFn (fun j : Fin K => body H G M b raw base j.val)
  have len : es.length=K := List.length_ofFn
  have low : out < 2^w := (Nat.le_add_right _ _).trans_lt space
  obtain ⟨pre, _, frame⟩ := prepared w H G M b base m low
  have safe : ∀ e∈es, e.Fits w out := by
    intro e he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    exact body_fits rawRoom space j
  have room : out+es.length*n < 2^w := by simpa only [len] using space
  have cpu : (publish w K H G M b raw base).Runs (prep.image m) := by
    intro nPC nReg nPub machine
    exact ProbeStage.Native.columns_exec es (prep.image m)
      (ProbeStage.Native.columns_safe es le_rfl safe room) machine
  refine ⟨NativePhase.seq_runs prep (publish w K H G M b raw base) m pre cpu,?_⟩
  intro a away
  change a < base ∨ out+K*n ≤ a at away
  have start : base ≤ out := Nat.le_add_right ..
  have keep := ProbeStage.Native.columns_frame (n:=n) (base:=out) es (prep.image m) (address:=a)
    (by rw [len]; exact away.imp (fun h=>h.trans_le start) id : a < out ∨ out+es.length*n ≤ a)
  exact keep.trans (frame a (away.imp id (fun h=>(Nat.le_add_right out _).trans h)))

theorem runtime_word {w K H G M b raw base : ℕ} (β : Fin K→Fin H→Cell b) (m : Memory w)
    (stored : Raw raw β m) (tables : TablesOK H G M b base m)
    (rawRoom : raw+K*H+span H ≤ base) (space : outputBase H G M b base+K*(H*chunks G M) < 2^w)
    (bits : b*M ≤ w) (j : Fin K) :
    (body H G M b raw base j.val).Fits w (outputBase H G M b base) ∧
      DescentPackedZip.Source (body H G M b raw base j.val) (fun v (_ : Fin G) => β j v) M m := by
  let n := H*chunks G M
  have geom := body_fits rawRoom space j
  refine ⟨geom,?_⟩
  obtain ⟨⟨wFit,rawFit,aFit,_⟩,mFit,_⟩ := geom
  intro p
  let u := row H G M p
  have ur : u.val < span n := u.isLt.trans_le (span_ge n)
  have ai := DescentPackedZip.bank_read (actorBank base b n) m ur aFit
  have ra := DescentPackedZip.bank_read (rawBank raw H j.val) m (p.1.isLt.trans_le (span_ge H)) rawFit
  have ww := DescentPackedZip.bank_read (wideBank base b) m (β j p.1).isLt wFit
  have ma := DescentPackedZip.bank_read (maskBank base b n) m ur mFit
  have wordLim : (DescentSeedSignedBroadcast.wide M (β j p.1)).val < 2^w :=
    (DescentSeedSignedBroadcast.wide M (β j p.1)).isLt.trans_le (Nat.pow_le_pow_right (by decide) bits)
  have maskLim : maskWord b M G p.2.val < 2^w :=
    (Nat.pred_lt (Nat.two_pow_pos _).ne').trans_le (Nat.pow_le_pow_right (by decide)
      ((Nat.mul_le_mul_left b (Nat.min_le_left ..)).trans bits))
  rw [←DescentSeedSignedBroadcast.last_word (β j) p]
  change BinaryOp.bitAnd.eval ((wideBank base b).read m ((rawBank raw H j.val).read m
      ((actorBank base b n).read m (u.val : Word w)))) ((maskBank base b n).read m (u.val : Word w)) = _
  have ac := ai.trans (tables.actor p)
  have field := ra.trans (stored j p.1)
  have wide := ww.trans (tables.word (β j p.1))
  have mask := ma.trans (tables.mask p)
  rw [ac,field,wide,mask]
  exact DescentSeedSignedBroadcast.mask_eval _ _ wordLim maskLim

/-- The shape program reads the physical runtime directory, stores each packed column,
and preserves the surrounding RAM for the next native stage. -/
theorem run {w K H G M b raw base : ℕ} (β : Fin K→Fin H→Cell b) (m : Memory w)
    (stored : Raw raw β m) (rawRoom : raw+K*H+span H ≤ base)
    (space : outputBase H G M b base+K*(H*chunks G M) < 2^w) (bits : b*M ≤ w) :
    let p := phase w K H G M b raw base
    p.Runs m ∧ (∀ j : Fin K, DescentPackedZip.Source (expr H G M b base j.val)
      (fun v (_ : Fin G) => β j v) M (p.image m)) ∧
    (∀ a, a < base ∨ outputBase H G M b base+K*(H*chunks G M) ≤ a → p.image m a=m a) := by
  let n := H*chunks G M
  let out := outputBase H G M b base
  let prep := prepare w H G M b base
  let es := List.ofFn (fun j : Fin K => body H G M b raw base j.val)
  have len : es.length=K := List.length_ofFn
  have low : out < 2^w := (Nat.le_add_right _ _).trans_lt space
  obtain ⟨pre, tables, frame⟩ := prepared w H G M b base m low
  have still : Raw raw β (prep.image m) := by
    intro j v
    have jj := Nat.mul_le_mul_right H (Nat.le_of_lt j.isLt)
    have vv := v.isLt.trans_le (span_ge H)
    exact (frame _ (.inl (by omega))).trans (stored j v)
  have cols := runtime_word (G:=G) (M:=M) β (prep.image m) still tables rawRoom space bits
  have safe : ∀ e∈es, e.Fits w out := by
    intro e he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    exact (cols j).1
  have room : out+es.length*n < 2^w := by simpa only [len] using space
  have cpu : (publish w K H G M b raw base).Runs (prep.image m) := by
    intro nPC nReg nPub machine
    exact ProbeStage.Native.columns_exec es (prep.image m)
      (ProbeStage.Native.columns_safe es le_rfl safe room) machine
  refine ⟨NativePhase.seq_runs prep (publish w K H G M b raw base) m pre cpu,?_,?_⟩
  · intro j
    have ss : span n < 2^w := by
      change base+(2^b+2*span n) < 2^w at low
      have twice : span n ≤ 2*span n := by omega
      exact twice.trans_lt ((Nat.le_add_left _ _).trans_lt ((Nat.le_add_left _ _).trans_lt low))
    apply DescentPackedZip.source_column (outBank H G M b base j.val)
      ((outBank H G M b base j.val).base+span n)
      ⟨span_pos _,ss,le_rfl⟩ _ _ (span_ge n)
    intro q
    have read := ProbeStage.Native.columns_read es (prep.image m) le_rfl safe j.val (by simpa only [len] using j.isLt)
      (row H G M q)
    simp only [es, List.getElem_ofFn] at read
    exact read.trans ((cols j).2 q)
  · intro a away
    change a < base ∨ out+K*n ≤ a at away
    have start : base ≤ out := Nat.le_add_right ..
    have keep := ProbeStage.Native.columns_frame (n:=n) (base:=out) es (prep.image m) (address:=a)
      (by rw [len]; exact away.imp (fun h=>h.trans_le start) id : a < out ∨ out+es.length*n ≤ a)
    exact keep.trans (frame a (away.imp id (fun h=>(Nat.le_add_right out _).trans h)))

end
end Hierarchy.DescentResetStemHeaders

end OAI
