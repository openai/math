import OAI.Hierarchy.DescentPackedExponentCheap
import OAI.Hierarchy.DescentLocalPrivateNames
import OAI.Hierarchy.DescentTerminalObservedExponent

namespace OAI
/-! # The native multiplicity gate on the packed local names of an actual archive -/

namespace Hierarchy.DescentPackedTerminalExponent
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open ProtocolRAM DescentSIMDLookup DescentPackedPrivateSum DescentLocalPrivateNames
open DescentKernelHistory DescentBundleHistory Computability.BorderVNP.Crossing DescentTerminalObservedExponent
open scoped Fin.CommRing BigOperators Classical
noncomputable section
variable {w : ℕ} (L : Layout) (O : DescentPrivateExponentRAM.Banks)

variable {U P : Type} {p D n a K M : ℕ} {bits : P→ℕ}
variable (hp : 0<p) (N : Network D P bits) (r : SiteBits (U:=U) N) (s : ∀v,Shape p (r v))
local notation "rows" => (fun v => Shape.recipe hp (s v))

def localRows (sites : Fin n≃N.Site) (slot : ∀v,Slot (rows v)↪Fin K)
    (code : ∀v,(rows v).UsedWord↪Cell a) : Fin 1→Fin n→Cell (a*K) :=
  fun _ i=>encode a K (raw (rows (sites i)) (slot (sites i)) (code (sites i)))

def paddedRows (index : N.Site↪Fin n) (slot : ∀v,Slot (rows v)↪Fin K)
    (code : ∀v,(rows v).UsedWord↪Cell a) : Fin 1→Fin n→Cell (a*K) :=
  fun _ i=>if h : ∃v,index v=i then encode a K (raw (rows h.choose) (slot h.choose) (code h.choose)) else 0

theorem paddedRows_site (index : N.Site↪Fin n) (slot : ∀v,Slot (rows v)↪Fin K)
    (code : ∀v,(rows v).UsedWord↪Cell a) (v : N.Site) :
    paddedRows hp N r s index slot code 0 (index v)=encode a K (raw (rows v) (slot v) (code v)) := by
  have hit : ∃y,index y=index v:=⟨v,rfl⟩
  simp only [paddedRows,dite_eq_left hit]
  exact congrArg (fun y : N.Site => encode a K (raw (rows y) (slot y) (code y)))
    (index.injective hit.choose_spec)

theorem padded_total (index : N.Site↪Fin n) (slot : ∀v,Slot (rows v)↪Fin K)
    (code : ∀v,(rows v).UsedWord↪Cell a) (nz : ∀v h,code v h≠0) :
    (∑i : Fin 1,∑j : Fin n,countCell a K (paddedRows hp N r s index slot code i j))=liveCount hp N r s := by
  rw [Fin.sum_univ_one]
  let f (i : Fin n) := countCell a K (paddedRows hp N r s index slot code 0 i)
  have off (i : Fin n) (_ : i∈Finset.univ) (no : i∉Finset.univ.map index) : f i=0 := by
    have miss : ¬∃v,index v=i := fun ⟨v,e⟩=>no (Finset.mem_map.mpr ⟨v,Finset.mem_univ _,e⟩)
    simp [f,paddedRows,miss]
  change (∑i,f i)=_
  rw [←Finset.sum_subset (Finset.subset_univ (Finset.univ.map index)) off,Finset.sum_map]
  exact Finset.sum_congr rfl (fun v _=>by
    dsimp only [f]
    rw [paddedRows_site, countCell_actual _ _ _ (nz v)])

private theorem read_sum (x : Fin 1→Fin n→Cell (a*K))
    (count : (∑v,∑j,countCell a K (x v j))=liveCount hp N r s)
    (m : Memory w) (space : L.Room w 1 n M) (last : O.Room w) (positive : 0<M)
    (rowsFit : Layout.count 1 n M≤L.source.size) (width : L.rom.bits=(a*K)*M)
    (ready : DescentPackedScore.Input (M:=M) L.source L.rom (countCell a K) x m)
    (dest : O.usedWords=L.starts+Layout.count 1 n M) (old : O.totalBits<L.words)
    (volumeRead : m O.totalBits=(volume N r:Computability.VPVNP.BurstRAM.Word w)) (fits : liveCount hp N r s<2^w) :
    image L O n M p m O.deadBits=(deadCount hp N r s:Computability.VPVNP.BurstRAM.Word w) := by
  have total:=L.read (countCell a K) x m space
    (countCell_zero a K) positive rowsFit width ready
  rw [count,←dest] at total
  have val : (L.image 1 n M m O.usedWords).val=liveCount hp N r s := by
    rw [total,Fin.val_cast_of_lt fits]
  have sum:=partition hp N r s
  have held:=(L.frame 1 n M m O.totalBits old space).trans volumeRead
  rw [image,val,O.read _ _ _ _ last held (by omega)]
  congr 1
  omega


theorem read (sites : Fin n≃N.Site) (slot : ∀v,Slot (rows v)↪Fin K)
    (code : ∀v,(rows v).UsedWord↪Cell a) (nz : ∀v h,code v h≠0)
    (m : Memory w) (space : L.Room w 1 n M) (last : O.Room w) (positive : 0<M)
    (rowsFit : Layout.count 1 n M≤L.source.size) (width : L.rom.bits=(a*K)*M)
    (ready : DescentPackedScore.Input (M:=M) L.source L.rom (countCell a K) (localRows hp N r s sites slot code) m)
    (dest : O.usedWords=L.starts+Layout.count 1 n M) (old : O.totalBits<L.words)
    (volumeRead : m O.totalBits=(volume N r:Computability.VPVNP.BurstRAM.Word w)) (fits : liveCount hp N r s<2^w) :
    image L O n M p m O.deadBits=(deadCount hp N r s:Computability.VPVNP.BurstRAM.Word w) := by
  have each:=fun i : Fin n=>countCell_actual (rows (sites i)) (slot (sites i)) (code (sites i)) (nz (sites i))
  have count : (∑v : Fin 1,∑j : Fin n,countCell a K (localRows hp N r s sites slot code v j))=liveCount hp N r s := by
    simp only [Fin.sum_univ_one,localRows,each]
    exact sites.sum_comp (fun v : N.Site => Fintype.card (rows v).UsedWord)
  exact read_sum L O hp N r s _ count m space last positive rowsFit width ready dest old volumeRead fits

theorem read_padded (index : N.Site↪Fin n) (slot : ∀v,Slot (rows v)↪Fin K)
    (code : ∀v,(rows v).UsedWord↪Cell a) (nz : ∀v h,code v h≠0)
    (m : Memory w) (space : L.Room w 1 n M) (last : O.Room w) (positive : 0<M)
    (rowsFit : Layout.count 1 n M≤L.source.size) (width : L.rom.bits=(a*K)*M)
    (ready : DescentPackedScore.Input (M:=M) L.source L.rom (countCell a K) (paddedRows hp N r s index slot code) m)
    (dest : O.usedWords=L.starts+Layout.count 1 n M) (old : O.totalBits<L.words)
    (volumeRead : m O.totalBits=(volume N r:Computability.VPVNP.BurstRAM.Word w)) (fits : liveCount hp N r s<2^w) :
    image L O n M p m O.deadBits=(deadCount hp N r s:Computability.VPVNP.BurstRAM.Word w) := by
  exact read_sum L O hp N r s _ (padded_total hp N r s index slot code nz) m space last positive rowsFit width
    ready dest old volumeRead fits

end
end Hierarchy.DescentPackedTerminalExponent

end OAI
