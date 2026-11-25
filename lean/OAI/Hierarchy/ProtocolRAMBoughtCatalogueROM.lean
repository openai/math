import OAI.Hierarchy.ProtocolRAMBoughtCatalogue

namespace OAI
/-! # Public directory cells used to label chronological acquired edges -/

namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen ReportSockets ProbeStage.CoreBoard
open TaggedShorterSupergroups Calendar Calendar.CatalogueRows
open scoped Fin.CommRing Classical
noncomputable section
variable {z W k attempts K H q goods r edges N jobs : ℕ}

/-- Static ROMs shared by every permutation, including the quotient/remainder
headers on the fixed chronological candidate list. -/
structure Directory.ROM (v : Directory attempts) (S : PurchaseSampler) (depth : ℕ)
    (groups : Fin K≃AllGroups z (2^W)) (packed : TaggedShorterSupergroups.Directory (reserved z W (ReportSockets.copies k attempts)) H)
    (m : Shelf.Mem z (2^W)) : Prop where
  names : ReportGroupROM.Resident v.remapBase groups PurchaseCT.groupNumber m
  outer : (v.header z (2^W) k S.degree depth).Loaded m
  keys : (StripDirectory.stratumHeader z (2^W) k S.degree depth v.keysBase).Loaded m
  sites : SiteROM.Resident packed v.sitesBase m
  tables : ∀g,let j:=((groups.symm g).val:Word (wordBits z (2^W) Native.copies))
    (ProtocolRAMSupergroupDirectory.groupBank v.superBase K).read m j=((packed.group g).val:Word _) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank v.superBase K).read m j=(packed.base g:Word _)

end
end Hierarchy.ProtocolRAM.BoughtSockets

end OAI
