import OAI.ThreeFlat.BlankNetwork

namespace OAI
namespace ThreeFlat.RAM.TickWeightedBank

open BitNetwork

abbrev shape (F : Type*) (p H J : ℕ) [Zero F] [One F] := blankNetwork (F:=F) p H J

end ThreeFlat.RAM.TickWeightedBank

end OAI
