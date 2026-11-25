import OAI.Hierarchy.ProtocolRAMCalendarPrevious

namespace OAI
/-! # Active and saved bank addresses on the original calendar -/
namespace Hierarchy.ProtocolRAM.Calendar.StockBound

structure Banks where
  initial : ℕ
  zeroReserve : ℕ
  active : Event→ℕ
  saved : Attempt→ℕ

def Banks.publications (b : Banks) (e : Event) :=
  match e with
  | .attempt a => [b.active e,b.saved a]
  | .feed _ => [b.active e]

def parent : Event→Option Attempt
  | .attempt (.inner p a _ _) | .feed (.inner p a _) => some (.outer p a)
  | _ => none

def Banks.reserve (b : Banks) (e : Event) := (parent e).elim b.zeroReserve b.saved

def Banks.previous (b : Banks) (c : Mesh) := previousStock c b.initial b.active

end Hierarchy.ProtocolRAM.Calendar.StockBound

end OAI
