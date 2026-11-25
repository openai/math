import OAI.Hierarchy.DescentDepotSetup
import OAI.Hierarchy.DescentDepotZipRoom

namespace OAI
/-! # Retain all actually installed donor tables across the per-date preparation -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentPackedZip DescentSIMDLookup DescentPacking.PackedMatch ProtocolRAM Computability.VPVNP.BurstRAM
open DescentSixParty.Chronology ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (s : DepotRAM.Shape) (z : DescentPacking.PackedMatch.Shape) (K H J M unit : ℕ)

private theorem zip_keep {a b c : ℕ} (f : Cell a→Cell b→Cell c) (M out : ℕ) (T : Tables) (m new : Memory w)
    (shape : T.shift.bits=a*M ∧ T.apply.bits=(a+b)*M)
    (limits : T.shift.Fits w out ∧ T.apply.Fits w out)
    (keep : ∀x,x<out→new x=m x) (old : Static T f M m) : Static T f M new := by
  refine ⟨fun i=>?_,fun i=>?_⟩
  · exact (keep _ ((Nat.add_lt_add_left (show i.val<T.shift.size by simp [Bank.size,shape.1]) _).trans_le limits.1.2.2)).trans (old.1 i)
  · exact (keep _ ((Nat.add_lt_add_left (show i.val<T.apply.size by simp [Bank.size,shape.2]) _).trans_le limits.2.2.2)).trans (old.2 i)

namespace Binary
local notation "bytes" => count s*(2*2^(unit*M))
theorem keep_installed (base out : ℕ) (large : 2*totalBits s+1≤unit) (before : base+bytes≤out) (fit : out<2^w)
    (m new : Memory w) (old : Installed s M unit base m) (keep : ∀x,x<out→new x=m x) :
    Installed s M unit base new := by
  have transfer (i : Kind s) := zip_keep (gates s i).eval M out (bank s M unit base i) m new
    (by simp only [bank,Book.tables,menu_at,and_self]) (rooms s M unit base i out large before fit) keep
  refine ⟨⟨transfer (.inl 0) old.1.ab,transfer (.inl 1) old.1.cd,transfer (.inl 2) old.1.ef,
    transfer (.inl 3) old.1.left,transfer (.inl 4) old.1.final⟩,
    fun i=>transfer (.inr (.inl i)) (old.2.1 i),fun i=>transfer (.inr (.inr (.inl i))) (old.2.2.1 i),
    transfer (.inr (.inr (.inr 0))) old.2.2.2⟩
end Binary

namespace Fresh.Book
theorem keep_fixed (base B prof C pad scale : ℕ) (top born : Bank) (m new : Memory w)
    (old : Fresh.Fixed (H:=H) (G:=J) (M:=M) s z (bank s z K H J M base top born) B prof C pad scale m)
    (keep : ∀i,i<base+physicalSize s z K H J M→new i=m i) :
    Fresh.Fixed (H:=H) (G:=J) (M:=M) s z (bank s z K H J M base top born) B prof C pad scale new := by
  have retain (j : Index s z K H J M) : new (address s z K H J M base j)=m (address s z K H J M base j) := by
    apply keep;rw [atOrdinal];exact Nat.add_lt_add_left ((ordinal s z K H J M) j).isLt _
  refine ⟨fun p=>(retain (.inl (row H J M p))).trans (old.active p),fun u=>(retain (.inr (.inl u))).trans (old.terrain u),
    fun t=>(retain (.inr (.inr (.inl t)))).trans (old.top t),?_⟩
  intro q n u t b
  let x : Input s z M:=⟨n,u,t,b⟩
  let idx:=(rawIndex s z M x).castLE (room s z M)
  have value : idx.val=code s z n u t b:=raw_val s z M x
  have eqn:=retain (.inr (.inr (.inr (q,idx))))
  simp only [address,value] at eqn
  exact eqn.trans (old.lookup q n u t b)
end Fresh.Book

namespace Setup
variable (base B prof C pad scale b seats : ℕ)
local notation "first" => DescentSIMDLookup.Book.words (totalBits s) H J M
local notation "second" => base+first
local notation "freshBase" => second+Binary.count s*(2*2^(unit*M))
local notation "rule" => output s B prof b seats
local notation "roof" => base+words s z K H J M unit
local notation "date" => phase s z K H J M unit base B prof C pad scale b seats

/-- The geometry phase can compute real mutable contents anywhere above the
installed interval. All lookup reads below it retain their printed values. -/
theorem prepared (src top born : Bank) (m : Memory w) (large : 2*totalBits s+1≤unit) (room : roof<2^w)
    (geometry : NativePhase w) (runs : geometry.Runs ((date w).image m))
    (keep : ∀j,j<roof → geometry.image ((date w).image m) j=(date w).image m j) :
    let n:=(date w).seq geometry
    let new:=n.image m
    let rom:=DescentSIMDLookup.Book.banks base (totalBits s) H J M src
    n.Runs m ∧
      (∀i : Cell (totalBits s*M)⊕Fin (H*chunks J M),new (fixedAddr rom i)=fixedWord rule i) ∧
      Binary.Installed s M unit second new ∧
      Fresh.Fixed (H:=H) (G:=J) (M:=M) s z (Fresh.Book.bank s z K H J M freshBase top born) B prof C pad scale new := by
  intro n new rom
  obtain ⟨put,look,zips,fresh,_⟩:=mount s z K H J M unit base B prof C pad scale b seats src top born m large room
  have limit : roof=freshBase+Fresh.Book.physicalSize s z K H J M := by unfold words Binary.words;omega
  have freshLow:=Nat.le_add_right freshBase (Fresh.Book.physicalSize s z K H J M)
  refine ⟨NativePhase.seq_runs _ _ m put runs,DescentSIMDLookup.Book.retain rule H J M base src _ _ look (fun j hj=>keep j (by omega)),
    Binary.keep_installed s M unit second roof large (by omega) room _ _ zips keep,
    Fresh.Book.keep_fixed s z K H J M freshBase B prof C pad scale top born _ _ fresh (fun i hi=>keep i (by omega))⟩
end Setup
end
end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
