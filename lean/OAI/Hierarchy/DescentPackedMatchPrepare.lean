import OAI.Hierarchy.DescentPackedMatchActorGate
import OAI.Hierarchy.DescentPackedMatchSenderPins
import OAI.Hierarchy.DescentIssuedHostRoster

namespace OAI
/-! # One native predecessor image for the complete matching gather -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSharedCableNames
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {k D cap d a M H G w : ℕ}
local notation "r" => 2^k
local notation "p" => 2*cap
local notation "N" => r+r*p
local notation "rows" => H*chunks G M

structure Chart (k cap : ℕ) where
  actor : Bank
  winner : Fin (2^k)→Bank
  signed : Fin (2^k)→Fin (2*cap)→Bank
  shift : Bank
  gate : Fin (2^k)→Bank
  dictionary : Bank
  mask : Bank

def gates (C : Chart k cap) (x : Fin r) : Tables := ⟨C.shift,C.gate x⟩
def chips (C : Chart k cap) (x : Fin r) (j : Fin p) : Banks := ⟨C.signed x j,C.dictionary,C.mask⟩

def expr (C : Chart k cap) : Fin N→Expr := Fin.addCases
  (ActorGate.expression (gates C) C.actor C.winner)
  (fun z=>DescentSIMDLookup.lookup (chips C (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2))

def fieldBase (base H D : ℕ) := base+H*D

def bank (base H D G M bits j : ℕ) : Bank := ⟨fieldBase base H D+j*(H*chunks G M),bits⟩

def gatedBank (base H G M D bits : ℕ) (x : Fin r) := bank base H D G M bits x.val

def markedBank (base H G M D bits : ℕ) (x : Fin r) (j : Fin p) := bank base H D G M bits (r+(finProdFinEquiv (x,j)).val)

def passes (C : Chart k cap) (R : DescentSortedRoster.Chart) (base H G M D : ℕ) : List Pass :=
  ⟨base,H*D,DescentSortedRoster.code R D H⟩::ProbeStage.Native.columns (H*chunks G M) (fieldBase base H D) (List.ofFn (expr C))

def stop (k H G M D cap base : ℕ) := fieldBase base H D+(2^k+2^k*(2*cap))*(H*chunks G M)

def staticWords (k D cap a M H G : ℕ) :=
  2^((1*2^k)*M)+2^k*2^((1*2^k+a)*M)+2^(DescentSignedCableCodec.width D cap*M)+H*chunks G M+2*H*D

/-- One shift table, one truth table per old block, a shared signed-chip table,
row masks and the two fixed indices used to sort the previous raw rotor table. -/
abbrev StaticCells (k D cap a M H G : ℕ) :=
  Cell ((1*2^k)*M) ⊕ ((Fin (2^k)×Cell ((1*2^k+a)*M)) ⊕ (Cell (DescentSignedCableCodec.width D cap*M) ⊕
    (Fin (H*chunks G M) ⊕ (Fin 2×Fin (H*D)))))

theorem static_card (k D cap a M H G : ℕ) : Fintype.card (StaticCells k D cap a M H G)=staticWords k D cap a M H G := by
  simp only [StaticCells,Cell,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin,staticWords];ring

structure Room (C : Chart k cap) (D a d M H G w base : ℕ) : Prop where
  gate : ∀x,DescentPackedZip.Fits (gates C x) (.lookup C.actor .row) (.lookup (C.winner x) .row) (1*2^k) a M base w
  chip : ∀x j,DescentSIMDLookup.Fits (chips C x j) (DescentSignedCableCodec.width D cap) d M H G w base
  actorRows : H*chunks G M≤C.actor.size
  winRows : ∀x,H*chunks G M≤(C.winner x).size
  finish : stop k H G M D cap base<2^w

structure Frame (C : Chart k cap) (active : Fin H→Fin G→Cell (1*r)) (win : Fin r→Fin H→Fin G→Cell a)
    (signed : Fin r→Fin p→Fin H→Fin G→Option (DescentSharedCableNames.Stage.Live D cap)) (d M : ℕ) (m : Memory w) : Prop where
  actor : DescentPackedColony.Reads C.actor active M m
  winner : ∀x,DescentPackedColony.Reads (C.winner x) (win x) M m
  gates : ∀x,DescentPackedZip.Static (gates C x) (fun u (v : Cell a) => Stage.gated (s:=d) u x v) M m
  signed : ∀x j,DescentSIMDLookup.PinFrame (M:=M) (chips C x j) (DescentPackedMatchSenderPins.table D cap d)
    (fun h g=>DescentSignedCableCodec.encode (signed x j h g)) m

private theorem fit_expr (C : Chart k cap) (base : ℕ) (fit : Room C D a d M H G w base) (j : Fin N) : (expr C j).Fits w base := by
  induction j using Fin.addCases with
  | left x =>
    simp only [expr,Fin.addCases_left,ActorGate.expression]
    exact ⟨(fit.gate x).apply,(fit.gate x).right,(fit.gate x).shift,(fit.gate x).left⟩
  | right z =>
    simp only [expr,Fin.addCases_right]
    have f := fit.chip (finProdFinEquiv.symm z).1 (finProdFinEquiv.symm z).2
    exact ⟨⟨f.dictionary,f.source,trivial⟩,f.mask,trivial⟩

theorem work_expr (C : Chart k cap) (j : Fin N) : (expr C j).work≤25 := by
  induction j using Fin.addCases with
  | left x=>simp only [expr,Fin.addCases_left,ActorGate.expression,Tables.read,Expr.work];decide
  | right z=>simp only [expr,Fin.addCases_right,DescentSIMDLookup.lookup,Expr.work];decide

theorem ticks (C : Chart k cap) (R : DescentSortedRoster.Chart) (base H G M D : ℕ) :
    clock (passes C R base H G M D)≤4+(H*D)*(2*(DescentSortedRoster.code R D H).work+4)+4+N*(4+(H*chunks G M)*54) := by
  have bound:=ProbeStage.Native.columns_clock (H*chunks G M) (fieldBase base H D) 25 (List.ofFn (expr C)) (by
    intro e he;obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he;exact work_expr C j)
  simp only [List.length_ofFn] at bound
  change clock _ ≤ 4 + N*(4+(H*chunks G M)*54) at bound
  change (4+(H*D)*(2*(DescentSortedRoster.code R D H).work+4))+clock _ ≤ _
  exact (Nat.add_le_add_left bound _).trans_eq (Nat.add_assoc _ _ _).symm

/-- The predecessor raster scan terminates with its exact compiled clock
on every input word, including a malformed selector. -/
theorem exec (C : Chart k cap) (R : DescentSortedRoster.Chart) (base : ℕ) (m : Memory w)
    (fit : Room C D a d M H G w base) (rf : DescentSortedRoster.Room R D H w base) :
    let ps := passes C R base H G M D
    (ProtocolRAM.program w ps).Exec m (ProtocolRAM.result ps m) (ProtocolRAM.clock ps) := by
  intro ps
  let es := List.ofFn (expr C)
  let head : ProtocolRAM.Pass := ⟨base,H*D,DescentSortedRoster.code R D H⟩
  have headFit : head.Fits w :=
    ⟨DescentSortedRoster.built_fits R base rf,rf.endFit⟩
  have before : base ≤ fieldBase base H D := Nat.le_add_right base (H*D)
  have readers : ∀ e ∈ es, e.Fits w base := by
    intro e he
    change e ∈ List.ofFn (expr C) at he
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp he
    exact fit_expr C base fit j
  have room : fieldBase base H D + es.length * (H*chunks G M) < 2^w := by
    simpa only [es,List.length_ofFn,stop] using fit.finish
  have tailFit := ProbeStage.Native.columns_safe (n:=H*chunks G M) (src:=base)
    (base:=fieldBase base H D) (w:=w) es before readers room
  have safe : ∀ q ∈ ps, q.Fits w := by
    intro q hq
    change q ∈ head :: ProbeStage.Native.columns (H*chunks G M) (fieldBase base H D) es at hq
    rcases List.mem_cons.mp hq with eq | hm
    · subst q
      exact headFit
    · exact tailFit q hm
  exact @ProtocolRAM.program_exec w ps m safe

/-- Sort the actual old rotor, then put all gated winners and all marked-edge
neighbor words into fresh successive columns without disturbing any old pins. -/
theorem run (C : Chart k cap) (R : DescentSortedRoster.Chart) (P : Ports D) (out : Bank) (bits : ℕ) (m : Memory w)
    (active : Fin H→Fin G→Cell (1*r)) (win : Fin r→Fin H→Fin G→Cell a)
    (signed : Fin r→Fin p→Fin H→Fin G→Option (DescentSharedCableNames.Stage.Live D cap)) (rs : Fin H→Fin D→Option (Fin H))
    (fit : Room C D a d M H G w out.base) (frame : Frame C active win signed d M m)
    (rf : DescentSortedRoster.Room R D H w out.base) (raw : DescentSortedRoster.Raw R rs m)
    (old : Mounted P rs m G M) (ids : ∀j,(P.ids j).base+rows≤out.base) (off : P.offsets.base+H≤out.base) (ch : P.chunks.base+rows≤out.base) :
    let ps:=passes C R out.base H G M D;let final:=ProtocolRAM.result ps m
    (ProtocolRAM.program w ps).Exec m final (clock ps) ∧ (∀x : Fin r,Reads (gatedBank (k:=k) out.base H G M D bits x)
      (fun h g=>Stage.gated (s:=d) (active h g) x (win x h g)) M final) ∧
      (∀(x : Fin r) (j : Fin p),Reads (markedBank (k:=k) (cap:=cap) out.base H G M D bits x j) (fun h g=>Stage.marked d (signed x j h g)) M final) ∧
      Mounted {P with roster:=out} (DescentSortedRoster.indexed rs) final G M ∧
      (∀z<out.base,final z=m z) ∧ CheapCode (ProtocolRAM.program w ps) := by
  intro ps final
  let es : List Expr := List.ofFn (expr C)
  let after : Memory w := ProtocolRAM.image out.base (H*D) (DescentSortedRoster.code R D H) m
  let start : ℕ := fieldBase out.base H D
  have sep : out.base ≤ start := Nat.le_add_right out.base (H*D)
  have len : es.length = N := List.length_ofFn
  have enc (e : Expr) (he : e ∈ es) : e.Fits w out.base := by
    change e ∈ List.ofFn (expr C) at he
    obtain ⟨j, rfl⟩ := List.mem_ofFn.mp he
    exact fit_expr C out.base fit j
  have prior (z : ℕ) (hz : z < out.base) : after z = m z :=
    ProtocolRAMGeneratedWrite.frame_image out.base (H*D) (DescentSortedRoster.code R D H) m z (Or.inl hz)
  have below (z : ℕ) (hz : z < start) : final z = after z := by
    change ProtocolRAM.result (ProbeStage.Native.columns rows start es) after z = after z
    exact ProbeStage.Native.columns_frame (w:=w) (n:=rows) (base:=start) (address:=z) es after (Or.inl hz)
  have stored (j : Fin N) (pos : Row H G M) :
      final (start+j.val*rows+(row H G M pos).val) =
        (expr C j).eval m ((row H G M pos).val : Word w) := by
    let i : Fin rows := row H G M pos
    change ProtocolRAM.result (ProbeStage.Native.columns rows start es) after (start+j.val*rows+i.val) =
      (expr C j).eval m (i.val : Word w)
    have hj : j.val < es.length := j.isLt.trans_eq len.symm
    refine (ProbeStage.Native.columns_read (w:=w) (n:=rows) (src:=out.base) (base:=start)
      es after sep enc j.val hj i).trans ?_
    simpa only [es, List.getElem_ofFn] using
      (ProtocolRAM.eval_below (w:=w) (out:=out.base) (expr C j) (i.val : Word w) m after
        (fit_expr C out.base fit j) prior)
  have sorted : Mounted {P with roster:=out} (DescentSortedRoster.indexed rs) after G M :=
    DescentSortedRoster.ports (D:=D) (H:=H) (w:=w) (G:=G) (M:=M) R rs m P out rf raw old ids off ch
  refine ⟨exec C R out.base m fit rf, ?_, ?_, ?_,
    fun z hz => (below z (hz.trans_le sep)).trans (prior z hz), @ProtocolRAM.program_cheap w ps⟩
  · intro x pos
    have actorFits : C.actor.Fits w out.base := (fit.gate x).left.1
    have winnerFits : (C.winner x).Fits w out.base := (fit.gate x).right.1
    have zero : Stage.gated (s:=d) (0 : Cell (1 * 2^k)) x (0 : Cell a) = 0 := by
      simp [Stage.gated,digit]
    have readGate := DescentPackedZip.read_data (gates C x)
      (.lookup C.actor .row) (.lookup (C.winner x) .row) out.base (fit.gate x)
      (fun (u : Cell (1 * 2^k)) (v : Cell a) => Stage.gated (s:=d) u x v)
      zero m (frame.gates x) active (win x)
      (DescentPackedZip.source_column C.actor out.base actorFits m active fit.actorRows frame.actor)
      (DescentPackedZip.source_column (C.winner x) out.base winnerFits m (win x) (fit.winRows x) (frame.winner x)) pos
    refine (stored (Fin.castAdd (r*p) x) pos).trans ?_
    simpa only [expr,Fin.addCases_left,ActorGate.expression] using readGate
  · intro x j pos
    let b : Fin (r*p) := finProdFinEquiv (x,j)
    have readChip := DescentSIMDLookup.lookup_read (chips C x j) out.base (fit.chip x j)
      (DescentPackedMatchSenderPins.table D cap d)
      (fun h g => DescentSignedCableCodec.encode (signed x j h g)) m (frame.signed x j) pos
    refine (stored (Fin.natAdd r b) pos).trans ?_
    simpa only [expr,Fin.addCases_right,b,Equiv.symm_apply_apply,
      DescentSIMDLookup.masked_eq_data,DescentPackedMatchSenderPins.table_at] using readChip
  · refine ⟨?_,?_,?_,?_⟩
    · intro pos j
      have low := (Nat.add_lt_add_left (row H G M pos).isLt (P.ids j).base).trans_le
        ((ids j).trans sep)
      exact (below _ low).trans (sorted.ids pos j)
    · intro v j
      have atRow : v.val*D+j.val<H*D :=
        (Nat.add_lt_add_left j.isLt _).trans_le
          (by rw [←Nat.succ_mul]; exact Nat.mul_le_mul_right _ v.isLt)
      have low : out.base+(v.val*D+j.val)<start := Nat.add_lt_add_left atRow out.base
      exact (below _ low).trans (sorted.roster v j)
    · intro v
      have low := (Nat.add_lt_add_left v.isLt P.offsets.base).trans_le (off.trans sep)
      exact (below _ low).trans (sorted.offsets v)
    · intro pos
      have low := (Nat.add_lt_add_left (row H G M pos).isLt P.chunks.base).trans_le
        (ch.trans sep)
      exact (below _ low).trans (sorted.chunks pos)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage.Prepare

end OAI
