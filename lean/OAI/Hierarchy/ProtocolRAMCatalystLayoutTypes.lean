import OAI.Hierarchy.ProtocolRAMCalendarArena
import OAI.Hierarchy.ProtocolRAMReserveUse

namespace OAI
/-! # The physical record, region and page layouts of the native reserve pass -/

noncomputable section
namespace Hierarchy.ProtocolRAM
namespace Calendar.CoreRoute

/-- Three length-only ROM columns. Even addresses select a small operator and its input row;
odd addresses carry the kind and the stock or reserve slot of the original commodity. -/
structure Recipes where
  kind : Bank
  mode : Bank
  operand : Bank

inductive Field | kind | mode | operand

def which (p : Recipes) : Field→Bank
  | .kind=>p.kind
  | .mode=>p.mode
  | .operand=>p.operand

end Calendar.CoreRoute
namespace CatalystArchive
open Calendar Calendar.CoreRoute

structure OwnerLedger where
  arena : Arena
  rows : Event→ℕ
  term : Event→Expr

/-- Addresses use one common absolute history bank. Its lower interval contains real
cash widths, and its upper interval holds the newly written owner words. -/
structure Room (c : Mesh) (A : Arena) (L : OwnerLedger) (a : ReserveUse.Archive)
    (b : RouteSettlement.Banks) (count entries w : ℕ) : Prop where
  zero : a.history.base=0
  kindOrder : a.kind.base+2*entries≤a.pointer.base
  kindSize : 2*entries≤a.kind.size
  ptrSize : 2*entries≤a.pointer.size
  directory : a.pointer.base+2*entries≤A.first
  cash : A.endAddress c≤b.width.base
  owners : b.width.base≤L.arena.first
  archive : L.arena.endAddress c≤a.history.size
  reserved : a.history.base+a.history.size≤b.reserved.base
  control : b.reserved.base+count≤b.used.base
  counters : b.used.base+count≤a.scratch
  end_ : a.scratch+2*entries<2^w
  inputEnds : a.kind.base+a.kind.size≤b.reserved.base ∧ a.pointer.base+a.pointer.size≤b.reserved.base
  usedSize : count≤b.used.size
  reservedSize : count≤b.reserved.size

/-- Two successive dyadic banks store the kind and pointer words for both
slots of each original event. The history bank addresses the genuine event rows. -/
def banks (start n : ℕ) (history : Bank) (scratch : ℕ) : ReserveUse.Archive :=
  let width:=(2*n).log2+1
  ⟨⟨start,width⟩,⟨start+2^width,width⟩,history,scratch⟩

theorem banks_bounds (start n : ℕ) (history : Bank) (scratch : ℕ) :
    let a:=banks start n history scratch
    a.kind.base+2*n≤a.pointer.base ∧ 2*n≤a.kind.size ∧ 2*n≤a.pointer.size := by
  intro a
  have capacity := (Nat.lt_log2_self (n:=2*n)).le
  exact ⟨Nat.add_le_add_left capacity start,capacity,capacity⟩

/-- Total capacity reserved for the two immutable pages, including the two
minimum dyadic pages at a zero-row calendar. -/
theorem banks_footprint (n : ℕ) : 2*2^((2*n).log2+1)≤8*n+4 := by
  by_cases empty : n=0
  · simp [empty]
  · have h:=Nat.log2_self_le (show 2*n≠0 by omega)
    rw [pow_succ]
    omega

structure StaticSpace (a : ReserveUse.Archive) (p : Recipes) (owners : Bank) (n r edges w : ℕ) : Prop where
  reserveOrder : a.kind.base+2*n≤a.pointer.base
  routeStart : a.pointer.base+2*n≤p.kind.base
  kindEnd : p.kind.base+p.kind.size≤p.mode.base
  modeEnd : p.mode.base+p.mode.size≤p.operand.base
  operandEnd : p.operand.base+p.operand.size≤owners.base
  recipeSize : ∀f,2*r≤(which p f).size
  recipeWords : 2*r≤2^w
  ownerSize : 8*edges≤owners.size
  ownerWords : 8*edges<2^w

/-- Three equally sized dyadic route columns immediately after the two pointer
pages, followed by a dyadic packed sink-owner page. -/
def routeBanks (start n r : ℕ) : Recipes :=
  let first:=start+2*2^((2*n).log2+1)
  let bits:=(2*r).log2+1
  ⟨⟨first,bits⟩,⟨first+2^bits,bits⟩,⟨first+2*2^bits,bits⟩⟩

def sinkBank (start n r edges : ℕ) : Bank :=
  let p:=routeBanks start n r
  ⟨p.operand.base+p.operand.size,(8*edges).log2+1⟩

theorem allocated_space (start n r edges w : ℕ) (history : Bank) (scratch : ℕ)
    (wide : (sinkBank start n r edges).base+(sinkBank start n r edges).size<2^w) :
    StaticSpace (banks start n history scratch) (routeBanks start n r) (sinkBank start n r edges) n r edges w := by
  have recordSize:=(Nat.lt_log2_self (n:=2*n)).le
  have routeSize:=(Nat.lt_log2_self (n:=2*r)).le
  have ownerSize:=(Nat.lt_log2_self (n:=8*edges)).le
  dsimp only [sinkBank,routeBanks,Bank.size] at wide
  constructor
  · exact (banks_bounds start n history scratch).1
  · dsimp only [banks,routeBanks]; omega
  · dsimp only [routeBanks,Bank.size]; omega
  · dsimp only [routeBanks,Bank.size]; omega
  · exact le_rfl
  · intro f; cases f <;> exact routeSize
  · omega
  · exact ownerSize
  · omega

theorem static_footprint (start n r edges : ℕ) :
    (sinkBank start n r edges).base+(sinkBank start n r edges).size≤ start+8*n+12*r+16*edges+12 := by
  have round (j : ℕ) : 2^(j.log2+1)≤2*j+2 := by
    by_cases zero : j=0
    · simp [zero]
    · have h:=Nat.log2_self_le zero
      rw [pow_succ]
      omega
  have a:=round (2*n)
  have b:=round (2*r)
  have c:=round (8*edges)
  dsimp only [sinkBank,routeBanks,Bank.size]
  omega

end CatalystArchive
end Hierarchy.ProtocolRAM
end

end OAI
