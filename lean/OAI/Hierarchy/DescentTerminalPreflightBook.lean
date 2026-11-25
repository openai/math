import OAI.Hierarchy.DescentTerminalPreflightRooms
import OAI.Hierarchy.DescentTerminalBookBoardInput

namespace OAI
/-! # The allocated Book fetches original comparators, f0/f1 columns and signed wings -/
namespace Hierarchy.DescentTerminalPreflightSpace.Spec
open ProtocolRAM DescentTerminalLocalPortBook DescentTerminalPrimitiveArena
open ThreeFlat.RAM
noncomputable section
variable (x:Spec) (base:ℕ) (peer:Bank) (wing:Fin x.scalar.blocks→Fin (2*x.cap)→Bank)
def rasters : Rasters x.degree x.scalar.blocks x.cap := ⟨peer,x.channels base,wing⟩
def issuedBook := (x.rasters base peer wing).controller x.scalar.shops (x.bookBegin base) x.printBits

theorem print_layout : x.issuedBook base peer wing=x.book base (x.rasters base peer wing).sources := rfl
theorem print_stop : (x.issuedBook base peer wing).stop=x.bookEnd base := rfl
theorem print_parts :
    (x.issuedBook base peer wing).parts (Book.WeightShelf.banks x.vertices x.arguments (x.weights base))=x.parts base := rfl

private theorem times_fit (w bound d:ℕ) : (timesRow d).Fits w bound := by
  induction d with | zero=>trivial | succ d ih=>exact ⟨ih,trivial⟩

theorem source_fit {w:ℕ} (word:x.maskBase base<2^w) (earlier:peer.base+peer.size≤x.cohortEnd base)
    (wings:∀b j,(wing b j).base+(wing b j).size≤x.cohortEnd base) (i:Fin x.strips) :
    ((x.issuedBook base peer wing).source i).Fits w (x.bookBegin base) := by
  let R:=x.rasters base peer wing
  obtain ⟨a,b,c,d,e,f,g,h,j⟩:=x.layers base
  have early_:x.cohortEnd base≤x.weights base:=a.trans b
  have finish_:x.bookBegin base<2^w:=by omega
  have old (bank:Bank) (q:bank.base+bank.size≤x.weights base) : bank.Fits w (x.bookBegin base) :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt ((q.trans c).trans_lt finish_),q.trans c⟩
  have occ (b:Fin x.scalar.blocks) : (R.geometry.occupied b).Fits w (x.bookBegin base):=
    old _ (x.channel_end base b 1)
  have count (b:Fin x.scalar.blocks) : (R.geometry.primitive b 0).Fits w (x.bookBegin base):=
    old _ (x.channel_end base b 0)
  have seen:R.roster.Fits w (x.bookBegin base):=old peer (earlier.trans (a.trans b))
  have neighbor (j:Fin x.degree) : (R.neighbor j).Fits w (x.bookBegin base):=⟨seen,times_fit ..,trivial⟩
  change (R.sources i).Fits w _
  unfold Rasters.sources
  cases ix:(fieldIndex x.degree x.scalar.blocks x.cap).symm i with
  | inl j=>exact ⟨trivial,neighbor j,trivial,⟨neighbor j,trivial,trivial,trivial⟩⟩
  | inr z=>
    rcases z with ⟨b,j|j⟩
    · refine ⟨?_,trivial⟩
      change (if j=0 then R.geometry.occupied b else R.geometry.primitive b 0).Fits w _
      split <;> first | exact occ b | exact count b
    · exact ⟨old _ ((wings b j).trans early_),trivial⟩

theorem control_fits {w:ℕ} (word:x.maskBase base<2^w) (populated:0<x.strips) :
    (Book.expression (x.parts base)).Fits w (x.controls base).base := by
  have f:= (x.book_fits base word populated).1
  have term (j:Fin 6) : ((x.parts base j).fetch).Fits w (x.bookEnd base) :=
    ⟨(f j).2,(f j).1,trivial⟩
  exact ⟨term 0,term 1,term 2,term 3,term 4,term 5⟩

end
end Hierarchy.DescentTerminalPreflightSpace.Spec

end OAI
