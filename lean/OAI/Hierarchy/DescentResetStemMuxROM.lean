import OAI.Hierarchy.DescentResetStemMux
import OAI.Hierarchy.DescentZipBook

namespace OAI
/-! # A shared native lookup directory for actor selections and their merge -/

namespace Hierarchy.DescentResetStemMux
open DescentSIMDLookup DescentPackedZip DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

/-- Row zero merges disjoint descriptors. Each following row selects one public
ordinal, with the same tables serving every packed group and actor position. -/
def gates (K a b : ℕ) : Fin (K+1)→Book.Gate :=
  Fin.cases ⟨b,b,b,join⟩ (fun j=>⟨a,b,b,gate j⟩)

def unit (a b : ℕ) := max (a+b) (b+b)
def words (K a b M : ℕ) := (K+1)*(2*2^(unit a b*M))

def tableFor (K a b M base : ℕ) (j : Fin K) : Tables :=
  Book.tables (gates K a b) (unit a b) M base j.succ

def mergeTable (K a b M base : ℕ) : Tables :=
  Book.tables (gates K a b) (unit a b) M base 0

private theorem cap (K a b : ℕ) (j : Fin (K+1)) :
    (gates K a b j).left+(gates K a b j).right≤unit a b := by
  refine Fin.cases ?_ (fun i=>?_) j
  · exact le_max_right ..
  · exact le_max_left ..

theorem mount (K a b M base : ℕ) (m : Memory w) (room : base+words K a b M<2^w) :
    let code:=Book.install (gates K a b) (unit a b) M w base
    let after:=Book.image (gates K a b) (unit a b) M base m
    code.Exec m after (4+10*words K a b M) ∧
      (∀j,Static (tableFor K a b M base j) (gate (a:=a) (b:=b) j) M after) ∧
      Static (mergeTable K a b M base) (join (b:=b)) M after ∧
      (∀x,x<base ∨ base+words K a b M≤x→after x=m x) ∧ CheapCode code := by
  obtain ⟨run,resident,frame,cheap⟩:=Book.mount (gates K a b) (unit a b) M base m (cap K a b) room
  exact ⟨run,fun j=>by simpa only [tableFor,gates,Fin.cases_succ] using resident j.succ,
    by simpa only [mergeTable,gates,Fin.cases_zero] using resident 0,frame,cheap⟩

theorem geometry (K a b M base out w : ℕ) (beyond : base+words K a b M≤out) (room : out<2^w) :
    (∀j,WordRoom (tableFor K a b M base j) a b M w out) ∧
      WordRoom (mergeTable K a b M base) b b M w out := by
  let safe (i : Fin (K+1)) := Book.geometry (gates K a b) (unit a b) M base i beyond room (cap K a b i)
  constructor
  · intro j
    exact ⟨(safe j.succ).1,(safe j.succ).2,rfl,rfl⟩
  · exact ⟨(safe 0).1,(safe 0).2,rfl,rfl⟩

theorem words_le (K a b M w : ℕ) (lanesFit : unit a b*M≤w/2) :
    words K a b M≤(K+1)*(2*2^(w/2)) :=
  Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) lanesFit))

theorem names (K a b M base w : ℕ) :
    DescentStaticWordColumn.names (Book.install (gates K a b) (unit a b) M w base)=15*(words K a b M+1) :=
  Book.names (gates K a b) (unit a b) M w base


end
end Hierarchy.DescentResetStemMux

end OAI
