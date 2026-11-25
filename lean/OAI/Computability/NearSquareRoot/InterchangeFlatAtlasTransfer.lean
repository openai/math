import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasCodec

/-! # Serialization and reconstruction of verified address catalogs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatAtlas

open Interchange Interchange.RectangleAtlas Opcode

variable {L T b a m : ℕ} {bits : List Bool} {r : Fin T → Rectangle (Fin L)}

/-- The packed table for a supplied catalog passes exactly when its native chart tests do. -/
theorem valid_pack_iff (H : Represents bits r) (hb : 1 < b) (w : AddressROM.Catalog r a m b) :
    valid b a m L T bits (pack fun c => (w c).map encode) = true ↔ AddressROM.valid w = true :=
  catalog_iff H hb _ w (chart_pack _)

/-- The finite raw certificate retains every instruction of the supplied catalog. -/
theorem exists_table_of_catalog (H : Represents bits r) (hb : 1 < b)
    (w : AddressROM.Catalog r a m b) (hw : AddressROM.valid w = true) :
    ∃ A : List Word, valid b a m L T bits A = true ∧
      A.length = capacity m L T ∧ ∀ c, chart A (chartIndex c) = (w c).map encode :=
  ⟨_,(valid_pack_iff H hb w).mpr hw,length_pack _,chart_pack _⟩

end FlatAtlas

end NearSquareRoot
end Computability
end OAI
