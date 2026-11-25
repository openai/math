import OAI.ThreeFlat.Diagonal.InitialSeedProcedure

namespace OAI
/-! # The raw parameter bits and chosen history mount the true initial cursor -/
namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan RAM.PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {W : ℕ} (A : Archive) (ss : List NavigationDirectory.Stage) (edges : ℕ)
variable (library suffix : List ℕ) (raw : ℕ→Bool) (input : Memory W)
local notation "cur" => (A.control:Word W)
local notation "dir" => A.directory ss edges W

structure SeedSources : Prop where
  book : A.codebookWords=library.length
  suffixAt : A.rawStatic=A.rawCodebook+W*library.length
  phase : A.phase<A.seed
  bookAbove : A.seed≤A.staticCodebook
  bookFit : A.staticCodebook+library.length<2^W
  dirLow : A.rawStatic+W*(dir).length≤A.seed
  histLow : (A.hist ss).source input+W*A.histWords ss≤A.seed
  separated : A.seed+(dir).length≤A.cursor.dense
  dirFits : ∀v∈dir,v<2^W
  publicBits : let words:=library++(dir++suffix)
    ∀ i<words.length,∀j<W,input (A.rawCodebook+W*i+j)=
      ((((words[i]?.getD 0:ℕ):Word W).val.testBit (W-1-j)).toNat:Word W)
  historyBits : ∀i<W*A.histWords ss,input ((A.hist ss).source input+i)=(raw i).toNat

def bookWord (a : ℕ) : Word W := (library[a-A.staticCodebook]?.getD 0:ℕ)

def mountedMemory : Memory W :=
  let a:=fillSegment A.staticCodebook A.codebookWords (A.bookWord library) input
  let b:=fillSegment A.seed (dir).length (A.tableWord ss edges) a
  let c:=fillSegment A.cursor.dense (A.histWords ss) (fun i=>RawHistogram.word raw (i-A.cursor.dense)) b
  writeMemory c cur (A.seed:Word W)

def bootTime (W : ℕ) :=
  (A.codebookWords*(5*W+6)+10)+(((A.directory ss edges W).length*(5*W+6)+10)+((A.histWords ss*(5*W+6)+10)+3))

variable {A ss edges library suffix raw input}
theorem SeedSources.boot_of_window {s : A.RelayWindow W} (banks : A.MountedRange ss edges W)
    (src : A.SeedSources ss edges library suffix raw input) :
    (A.boot ss edges).Spec (fun m=>m=input) (fun _ out=>out=A.mountedMemory ss edges library raw input)
      (A.bootTime ss edges W) := by
  have graph : A.cursor.graph≤A.control := by have h:=s.graphBefore;have h':=s.widthsBefore;omega
  have max : A.cursor.graph<2^W:=graph.trans_lt s.controlRoom
  have endDir:=banks.headers.trans_lt max
  have endHist:=banks.counts.trans_lt max
  have phase:=src.phase.trans (by have:=s.seedBefore;omega : A.seed<2^W)
  have libLow : A.rawCodebook+W*library.length≤A.staticCodebook := by
    rw [←src.suffixAt]; exact (Nat.le_add_right _ _).trans (src.dirLow.trans src.bookAbove)
  have pub:=A.mount_public ss edges library suffix input src.book src.suffixAt phase libLow src.dirLow
    src.bookFit endDir src.publicBits
  have lo : (A.hist ss).source input+W*A.histWords ss≤A.cursor.dense :=
    src.histLow.trans ((Nat.le_add_right ..).trans src.separated)
  have hist:=A.mount_histogram ss input raw phase lo endHist src.historyBits
  intro programCount registerCount wordCount machine
  exact A.boot_spec ss edges input (A.bookWord library) raw pub.1 pub.2 hist src.phase src.bookAbove src.dirLow src.histLow machine

theorem SeedSources.boot {s : A.SeedSpace W} (banks : A.MountedRange ss edges W)
    (src : A.SeedSources ss edges library suffix raw input) :
    (A.boot ss edges).Spec (fun m=>m=input) (fun _ out=>out=A.mountedMemory ss edges library raw input)
      (A.bootTime ss edges W) :=
  src.boot_of_window (s:=s.window) banks

theorem SeedSources.mounted_of_window (s : A.RelayWindow W) (banks : A.MountedRange ss edges W)
    (src : A.SeedSources ss edges library suffix raw input) :
    let out:=A.mountedMemory ss edges library raw input
    Scans.Header cur out A.seed 63 A.seedWords ∧ A.Live ss edges raw cur {A.cursor with header:=A.seed} out := by
  let out:=A.mountedMemory ss edges library raw input
  have graph : A.cursor.graph≤A.control := by have h:=s.graphBefore;have h':=s.widthsBefore;omega
  have seed : A.seed<2^W := (by have:=s.seedBefore;omega : A.seed<A.cursor.graph).trans_le graph |>.trans s.controlRoom
  have pointer : (out (cur).val).val=A.seed := by simp [out,mountedMemory,writeMemory,Fin.val_cast_of_lt seed]
  have eqAll (i v : ℕ) (get : dir[i]?=some v) : (out (A.seed+i)).val=v := by
    have hi : i<(dir).length := by by_contra! le;simp [List.getElem?_eq_none le] at get
    have eqv : dir[i]=v := by simpa [List.getElem?_eq_getElem hi] using get
    have fits:=src.dirFits v (eqv ▸ List.getElem_mem (l:=dir) (n:=i) hi)
    have ordinal : i < 64*(ss.length+2) := by simpa only [Archive.directory_length] using hi
    have below := (Nat.add_lt_add_left hi A.seed).trans_le src.separated
    have ctrl := (Nat.add_lt_add_left hi A.seed).trans_le (banks.headers.trans graph)
    simp [out,mountedMemory,writeMemory,Fin.val_cast_of_lt s.controlRoom,ne_of_lt ctrl,fillSegment,
      not_le.mpr below, ordinal, tableWord]
    rw [eqv, Nat.mod_eq_of_lt fits]
  have counts (j : ℕ) (hj : j<A.histWords ss) : out (A.cursor.dense+j)=RawHistogram.word raw j := by
    have low:= (Nat.add_lt_add_left hj A.cursor.dense).trans_le (banks.counts.trans graph)
    simp [out,mountedMemory,writeMemory,Fin.val_cast_of_lt s.controlRoom,ne_of_lt low,fillSegment,
      show A.cursor.dense+j<A.cursor.dense+A.histWords ss by omega]
  refine ⟨⟨pointer,?_,?_⟩,⟨pointer,fun i v _=>eqAll i v,counts⟩⟩
  · have := s.seedBefore.trans_lt (graph.trans_lt s.controlRoom)
    omega
  · intro i hi
    exact eqAll i _ (A.seed_at ss edges W ⟨i,by omega⟩)

theorem SeedSources.mounted (s : A.SeedSpace W) (banks : A.MountedRange ss edges W)
    (src : A.SeedSources ss edges library suffix raw input) :
    let out:=A.mountedMemory ss edges library raw input
    Scans.Header cur out A.seed 63 A.seedWords ∧ A.Live ss edges raw cur {A.cursor with header:=A.seed} out :=
  src.mounted_of_window s.window banks

theorem SeedSources.before_of_window (s : A.RelayWindow W) (src : A.SeedSources ss edges library suffix raw input)
    (i : ℕ) (hi : i<A.seed) : A.mountedMemory ss edges library raw input i=input i := by
  have dense : i<A.cursor.dense := hi.trans_le ((Nat.le_add_right ..).trans src.separated)
  have lib := hi.trans_le src.bookAbove
  have ctrl : i<A.control := by have:=s.seedBefore;have:=s.graphBefore;have:=s.widthsBefore;omega
  simp [mountedMemory,writeMemory,Fin.val_cast_of_lt s.controlRoom,ne_of_lt ctrl,fillSegment,
    not_le.mpr dense,not_le.mpr hi,not_le.mpr lib]


theorem SeedSources.before (s : A.SeedSpace W) (src : A.SeedSources ss edges library suffix raw input)
    (i : ℕ) (hi : i<A.seed) : A.mountedMemory ss edges library raw input i=input i :=
  src.before_of_window s.window i hi



end
end ThreeFlat.Diagonal.NavigationPass.Archive

end OAI
