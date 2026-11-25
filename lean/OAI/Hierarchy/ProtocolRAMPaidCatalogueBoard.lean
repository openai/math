import OAI.Hierarchy.ProtocolRAMCoreCatalogueNative
import OAI.Hierarchy.ProtocolRAMBoughtCatalogue

namespace OAI
/-! # The literal joint catalogue of core and chronological purchased rows -/

namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open ProbeStage
noncomputable section
variable {attempts : ℕ}

/-- A single code word per geometry field, calculated by the actual public and
permutation-dependent core descriptor or by a marked row's two socket readers. -/
def liveBoard (v : BoughtSockets.Directory attempts) (S : PurchaseSampler)
    (z W k depth R K binCount H bits idBase : ℕ) : Board :=
  ⟨R,(v.header z (2^W) k S.degree depth).count,idBase,
    CoreCatalogue.sourceAt z W k attempts R K binCount H bits,v.source S z W k depth K binCount H⟩

end
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end OAI
