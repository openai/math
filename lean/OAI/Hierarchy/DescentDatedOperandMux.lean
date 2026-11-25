import OAI.Hierarchy.DescentResetStemMuxROM
import OAI.Hierarchy.DescentSignedPrefixInvoice

namespace OAI
/-! # Publish all per-operand choices from one shared physical selection table -/
namespace Hierarchy.DescentDatedOperandMux
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty.Chronology
open DescentDatedAddressBook DescentPackedFlowBatch ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

structure Layout where
  hosts : ℕ
  groups : ℕ
  lanes : ℕ
  pages : ℕ
  candidates : ℕ
  keyBits : ℕ
  fieldBits : ℕ

variable (l : Layout)
local notation "H₀" => l.hosts
local notation "G₀" => l.groups
local notation "M₀" => l.lanes
local notation "N" => l.pages
local notation "C" => l.candidates
local notation "a" => l.keyBits
local notation "b" => l.fieldBits
local notation "n" => H₀*chunks G₀ M₀

def span := 2^Nat.clog 2 n
def tables := DescentResetStemMux.words C a b M₀
def start (base : ℕ) := base+tables l
def endAddress (base : ℕ) := start l base+N*span l
def bank (base : ℕ) (f : Fin N) : Bank := ⟨start l base+f.val*span l,Nat.clog 2 n⟩

variable (key : Fin l.pages → Expr) (head : Fin l.pages → Fin l.candidates → Expr)
def cell (base : ℕ) (f : Fin N) : Expr :=
  DescentResetStemMux.assemble (DescentResetStemMux.tableFor C a b M₀ base)
    (DescentResetStemMux.mergeTable C a b M₀ base) (key f) (head f)
def rowJob (base i : ℕ) : Expr :=
  if h : i<N then cell l key head base ⟨i,h⟩ else .lit 0
def job (base : ℕ) : SignedPrefix.Job := .columns N n (span l) (rowJob l key head base)
def boot (base w : ℕ) : NativePhase w :=
  ⟨Book.install (DescentResetStemMux.gates C a b) (DescentResetStemMux.unit a b) M₀ w base,4+10*tables l,
    Book.image (DescentResetStemMux.gates C a b) (DescentResetStemMux.unit a b) M₀ base,
    DescentStaticWordColumn.cheap _ _ _ _⟩
def phase (base w : ℕ) : NativePhase w :=
  (boot l base w).seq ((job l key head base).atBase (start l base) w)

theorem bank_room {w : ℕ} (base : ℕ) (space : endAddress l base<2^w) (f : Fin N) :
    (bank l base f).Fits w (endAddress l base) ∧ n≤(bank l base f).size := by
  have top:=Nat.mul_le_mul_right (span l) f.isLt
  rw [Nat.succ_mul] at top
  have high : (bank l base f).base+(bank l base f).size≤endAddress l base := by
    change start l base+f.val*span l+span l ≤ start l base+N*span l
    omega
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (high.trans_lt space),high⟩,Nat.le_pow_clog (by decide) _⟩

variable {base w : ℕ} (keys : ∀f,(key f).Fits w base) (heads : ∀f i,(head f i).Fits w base)
    (space : endAddress l base<2^w)

include keys heads space in
private theorem fits (f : Fin N) :
    DescentResetStemMux.Fits (DescentResetStemMux.tableFor C a b M₀ base)
      (DescentResetStemMux.mergeTable C a b M₀ base) (key f) (head f) a b M₀ w (start l base) := by
  have room: start l base<2^w:=(Nat.le_add_right ..).trans_lt space
  have g:=DescentResetStemMux.geometry C a b M₀ base (start l base) w le_rfl room
  exact ⟨g.1,g.2,ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (keys f),
    fun i=>ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (heads f i)⟩

include keys heads space in
theorem any (m : Memory w) :
    let run:=phase l key head base w
    run.Runs m ∧ (∀i,i<base ∨ endAddress l base ≤ i → run.image m i=m i) := by
  have high : start l base≤endAddress l base:=Nat.le_add_right ..
  have warm:=DescentResetStemMux.mount C a b M₀ base m (high.trans_lt space)
  have geo (i : ℕ) (hi : i<N) : (rowJob l key head base i).Fits w (start l base) := by
    rw [rowJob,dite_eq_left hi]
    exact DescentResetStemMux.assemble_fits _ _ _ _ (fits l key head keys heads space ⟨i,hi⟩)
  have act:=SignedPrefix.Job.any (job l key head base) (start l base) ((boot l base w).image m)
    ⟨Nat.le_pow_clog (by decide) _,geo⟩ space
  refine ⟨NativePhase.seq_runs _ _ m warm.1 act.1,?_⟩
  rintro i (pre|post)
  · exact (act.2 i (.inl (pre.trans_le (Nat.le_add_right ..)))).trans (warm.2.2.2.1 i (.inl pre))
  · exact (act.2 i (.inr post)).trans (warm.2.2.2.1 i (.inr (high.trans post)))

include keys heads space in
theorem emitted (m : Memory w) (code : Fin N→Fin H₀→Fin G₀→Cell a)
    (values : Fin N→Fin C→Fin H₀→Fin G₀→Cell b)
    (readKey : ∀f,Source (key f) (code f) M₀ m)
    (readInputs : ∀f i,Source (head f i) (values f i) M₀ m) :
    ∀f : Fin N,Reads (bank l base f) (fun h g=>DescentResetStemMux.pick (code f h g) (fun i=>values f i h g))
      M₀ ((phase l key head base w).image m) := by
  have high : start l base≤endAddress l base:=Nat.le_add_right ..
  let mid:=(boot l base w).image m
  have warm:=DescentResetStemMux.mount C a b M₀ base m (high.trans_lt space)
  have stable (i : ℕ) (low : i<base) : mid i=m i:=warm.2.2.2.1 i (.inl low)
  have read (f : Fin N) : Source (cell l key head base f)
      (fun h g=>DescentResetStemMux.pick (code f h g) (fun i=>values f i h g)) M₀ mid := by
    apply DescentResetStemMux.read_lanes _ _ _ _ (fits l key head keys heads space f) (code f) (values f) mid warm.2.1 warm.2.2.1
    · intro p
      exact (ProtocolRAM.eval_below _ _ _ _ (keys f) stable).trans (readKey f p)
    · intro i p
      exact (ProtocolRAM.eval_below _ _ _ _ (heads f i) stable).trans (readInputs f i p)
  have geo (i : ℕ) (hi : i<N) : (rowJob l key head base i).Fits w (start l base) := by
    rw [rowJob,dite_eq_left hi]
    exact DescentResetStemMux.assemble_fits _ _ _ _ (fits l key head keys heads space ⟨i,hi⟩)
  have act:=execute (start l base) n (span l) N (rowJob l key head base) mid geo space (Nat.le_pow_clog (by decide) _)
  intro f p
  exact (act.2.1 f (row H₀ G₀ M₀ p)).trans (by simpa only [rowJob,dite_eq_left f.isLt] using read f p)

theorem physical_cost (base w oldKey oldHead : ℕ)
    (keyWork : ∀f,(key f).work≤oldKey) (headWork : ∀f i,(head f i).work≤oldHead) :
    let work:=1+C*(oldKey+oldHead+22)
    let kernel:=job l key head base
    (phase l key head base w).ticks≤4+10*tables l+kernel.clocks work ∧
      DescentStaticWordColumn.names (phase l key head base w).program≤15*(tables l+1)+kernel.textSize work := by
  have bounded : (job l key head base).within (1+C*(oldKey+oldHead+22)) := by
    intro i hi
    let f : Fin N:=⟨i,hi⟩
    rw [rowJob,dite_eq_left hi]
    have size:=DescentResetStemMux.work_le (DescentResetStemMux.tableFor C a b M₀ base)
      (DescentResetStemMux.mergeTable C a b M₀ base) (key f) (head f) oldHead (headWork f)
    exact size.trans (by gcongr;exact keyWork f)
  have bill:=SignedPrefix.Job.invoice w (start l base) _ _ bounded
  refine ⟨Nat.add_le_add_left bill.1 _,?_⟩
  change DescentStaticWordColumn.names ((boot l base w).program.seq _)≤_
  rw [DescentStaticWordColumn.names_seq]
  exact Nat.add_le_add (DescentResetStemMux.names C a b M₀ base w).le bill.2

end
end Hierarchy.DescentDatedOperandMux

end OAI
