import OAI.Hierarchy.DescentTerminalEmitter
import OAI.Hierarchy.DescentStaticWordCheap
import OAI.Hierarchy.ProtocolRAMPortRanks
import Mathlib.Data.Nat.Log

namespace OAI
/-! # Ordered input columns of the terminal scatter, gather, route and leaf passes -/
namespace Hierarchy.DescentTerminalEmitterSources
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

abbrev Field := Fin 43

/-- The numbered inputs are the actual bank projections of the five passes. The book output
feeds the route, and the leaf occupancy is the newly assigned cell bank. -/
def readings (index format : DescentTerminalScatterChip.Layout) (book : DescentTerminalLocalPortBook.Gather)
    (route : DescentTerminalRouteIssue.Layout) (leaf : DescentTerminalLeafFold.Layout) : Field → Bank :=
  ![index.half,index.lane,index.live,index.directory,index.chunk,index.publicMode,index.owner,index.siteFirst,
    index.groupFirst,index.sourceFirst,index.privateWords,index.publicWords,
    format.half,format.lane,format.live,format.directory,format.chunk,format.publicMode,format.owner,format.siteFirst,
    format.groupFirst,format.sourceFirst,format.privateWords,format.publicWords,
    book.occupied,book.site,book.head,book.localRow,book.homeOffset,book.low,book.high,book.menu,
    route.offset,route.phase,route.update,route.lastRow,route.decode,
    leaf.half,leaf.lanes,leaf.home,leaf.event,leaf.weight,leaf.table]

def count (bits : Field → ℕ) (j : Field) := 2^(bits j)
def offsetAt (size : Field → ℕ) := ProtocolRAMPortRanks.«prefix» size Fin.val
def offset (bits : Field → ℕ) := offsetAt (count bits)
def total (bits : Field → ℕ) := ∑ j,count bits j
def finish (base : ℕ) (bits : Field → ℕ) := base+total bits
def buy (base : ℕ) (bits : Field → ℕ) (j : Field) : Bank := ⟨base+offset bits j,bits j⟩

theorem buy_end (base : ℕ) (bits : Field → ℕ) (j : Field) :
    (buy base bits j).base+(buy base bits j).size≤finish base bits := by
  have h:=ProtocolRAMPortRanks.prefix_end (count bits) Fin.val j
  simpa only [buy,Bank.size,finish,total,offset,offsetAt,count,Nat.add_assoc] using Nat.add_le_add_left h base

theorem buy_disjoint (base : ℕ) (bits : Field → ℕ) {i j : Field} (earlier : i<j) :
    (buy base bits i).base+(buy base bits i).size≤(buy base bits j).base := by
  have h:=ProtocolRAMPortRanks.prefix_disjoint (count bits) Fin.val (i:=i) (j:=j) earlier
  simpa only [buy,Bank.size,offset,offsetAt,count,Nat.add_assoc] using Nat.add_le_add_left h base

theorem buy_fits (base : ℕ) (bits : Field → ℕ) (j : Field) {w next : ℕ}
    (below : finish base bits≤next) (room : finish base bits<2^w) :
    (buy base bits j).Fits w next := by
  have e:=buy_end base bits j
  exact ⟨Nat.two_pow_pos _,by omega,e.trans below⟩

def bitsFor (need : Field → ℕ) (j : Field) := Nat.clog 2 (need j)

theorem bought (base : ℕ) (need : Field → ℕ) (j : Field) : need j≤(buy base (bitsFor need) j).size :=
  Nat.le_pow_clog (by decide) _

private theorem rounded (n : ℕ) : 2^(Nat.clog 2 n)≤2*n+1 := by
  cases hc : Nat.clog 2 n with
  | zero=>simp
  | succ k=>
    have smaller : k<Nat.clog 2 n:=by omega
    have := Nat.pow_lt_of_lt_clog smaller
    rw [pow_succ]
    omega

theorem total_bought (need : Field → ℕ) : total (bitsFor need)≤2*(∑j,need j)+43 := by
  calc
    total (bitsFor need) ≤ ∑j:Field, (2*need j+1) := Finset.sum_le_sum (fun j _=>rounded _)
    _ = _ := by simp [Finset.sum_add_distrib,Finset.mul_sum]

abbrev Words (bits : Field → ℕ) := (j : Field) → Fin (count bits j) → ℕ

/-- All 43 columns contribute to one literal data sequence. At any address exactly the
one containing interval contributes its own addressed source word. -/
def columnData (size : Field → ℕ) (words : (j:Field)→Fin (size j)→ℕ) (a : ℕ) : ℕ :=
  ∑j:Field, if h:offsetAt size j≤a ∧ a<offsetAt size j+size j
    then words j ⟨a-offsetAt size j,by omega⟩ else 0

theorem columnData_at (size : Field → ℕ) (words : (j:Field)→Fin (size j)→ℕ) (j : Field) (u : Fin (size j)) :
    columnData size words (offsetAt size j+u.val)=words j u := by
  unfold columnData
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ _)]
  · have h : offsetAt size j≤offsetAt size j+u.val ∧ offsetAt size j+u.val<offsetAt size j+size j :=
      ⟨Nat.le_add_right ..,Nat.add_lt_add_left u.isLt _⟩
    rw [dite_eq_left h]
    congr 1
    apply Fin.ext
    change offsetAt size j + u.val - offsetAt size j = u.val
    omega
  · intro k _ ne
    have outside : ¬(offsetAt size k ≤ offsetAt size j+u.val ∧ offsetAt size j+u.val < offsetAt size k+size k) := by
      rcases lt_or_gt_of_ne ne with before|after
      · have bound : offsetAt size k+size k≤offsetAt size j :=
          ProtocolRAMPortRanks.prefix_disjoint size Fin.val before
        omega
      · have bound : offsetAt size j+size j≤offsetAt size k :=
          ProtocolRAMPortRanks.prefix_disjoint size Fin.val after
        have := u.isLt
        omega
    rw [dite_eq_right outside]

def data (bits : Field → ℕ) (words : Words bits) := columnData (count bits) words

theorem data_at (bits : Field → ℕ) (words : Words bits) (j : Field) (u : Fin (count bits j)) :
    data bits words (offset bits j+u.val)=words j u :=
  columnData_at (count bits) words j u

def install (w base : ℕ) (bits : Field → ℕ) (words : Words bits) :=
  DescentStaticWordColumn.program w base (data bits words) (total bits)

def mounted {w : ℕ} (base : ℕ) (bits : Field → ℕ) (words : Words bits) (m : Memory w) :=
  DescentStaticWordColumn.image base (data bits words) m (total bits)

private theorem word_at {w : ℕ} (base : ℕ) (bits : Field → ℕ) (words : Words bits) (m : Memory w)
    (j : Field) (u : Fin (count bits j)) :
    mounted base bits words m ((buy base bits j).base+u.val)=(words j u:Word w) := by
  have last : offset bits j+count bits j≤total bits := ProtocolRAMPortRanks.prefix_end (count bits) Fin.val j
  have within : offset bits j+u.val<total bits := (Nat.add_lt_add_left u.isLt _).trans_le last
  change DescentStaticWordColumn.image base (data bits words) m (total bits) ((base+offset bits j)+u.val)=_
  rw [Nat.add_assoc,DescentStaticWordColumn.read base (total bits) (data bits words) m within,data_at]

theorem mount {w : ℕ} (base : ℕ) (bits : Field → ℕ) (words : Words bits) (m : Memory w)
    (room : finish base bits<2^w) :
    (install w base bits words).Exec m (mounted base bits words m) (4+10*total bits) ∧
    CheapCode (install w base bits words) ∧
    (∀(j:Field) (u:Fin (count bits j)),mounted base bits words m ((buy base bits j).base+u.val)=(words j u:Word w)) ∧
    (∀a,a<base ∨ finish base bits≤a→mounted base bits words m a=m a) := by
  unfold install mounted
  exact ⟨@DescentStaticWordColumn.mount w base (total bits) (data bits words) m room,
    @DescentStaticWordColumn.cheap w base (data bits words) (total bits),word_at base bits words m,
    @DescentStaticWordColumn.frame w base (total bits) (data bits words) m⟩

/-- A native bounded lookup at a true column row recovers the original literal. -/
theorem mounted_read {w : ℕ} (base : ℕ) (bits : Field → ℕ) (words : Words bits) (m : Memory w)
    (room : finish base bits<2^w) (j : Field) (u : Fin (count bits j)) :
    (buy base bits j).read (mounted base bits words m) (u.val:Word w)=(words j u:Word w) := by
  have field := buy_fits base bits j (next:=finish base bits) le_rfl room
  exact (@DescentTerminalDenseHeaderRAM.bank_nat w (buy base bits j) (finish base bits) u.val
    (mounted base bits words m) field u.isLt).trans (word_at base bits words m j u)

theorem names (w base : ℕ) (bits : Field → ℕ) (words : Words bits) :
    DescentStaticWordColumn.names (install w base bits words)=15*(total bits+1) :=
  DescentStaticWordColumn.names_mount ..

end
end Hierarchy.DescentTerminalEmitterSources

end OAI
