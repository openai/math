import OAI.Hierarchy.TaggedWideDatedRows
import OAI.Hierarchy.TaggedWirePaidSelection

namespace OAI
/-! # Orientation of the original paid, commodity and reserve endpoint reads -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows
open AdaptiveProbe ReportSockets ProtocolRAM Calendar CatalogueRows RoleProgram
open WireTelescope
open scoped Classical
variable {h W k attempts n : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (mark : Marks h W k attempts) (unique : Exclusive mark)
    (rows : Fin n≃Source S π depth mark)

/-- Only the original paid row inputs were sorted by comparing the native socket
site words; the commodity and reserve rows still come in their original orientation. -/
def inputSide (i : Fin n) (b : Bool) :=
  match rows i with
  | .inl _=>b
  | .inr g=>swap S π depth mark (.inr g) b

theorem input_onto (i : Fin n) : Function.Surjective (inputSide S π depth mark rows i) := by
  intro b
  cases x:rows i with
  | inl e=>exact ⟨b,by simp [inputSide,x]⟩
  | inr d=>
    refine ⟨swap S π depth mark (.inr d) b,?_⟩
    simp only [inputSide,x,swap]
    split <;> simp

theorem input_flip (i : Fin n) (b : Bool) : inputSide S π depth mark rows i (!b)=!(inputSide S π depth mark rows i b) := by
  cases x:rows i <;> simp only [inputSide,x,swap]
  split <;> rfl

variable {edges : ℕ} (ordinal : Catalogue S π depth mark ↪ Fin edges)
    (pay : Fin edges→Bool→Public S h W k attempts)
    (i : Fin n)
local notation "word" => ((ordinal.sumMap (Function.Embedding.refl _)) (rows i))

theorem original_name (s : Bool)
    (paid : ∀e,rows i=.inl e→∀b,pay (ordinal e) b=.inl (HistoryRoles.paid S π depth mark unique (e,b))) :
    publicRoleFor S π pay word s=named S π depth mark unique rows (i,inputSide S π depth mark rows i s) := by
  change publicRoleFor S π pay word s=physical S π depth mark unique
    (rows i,swap S π depth mark (rows i) (inputSide S π depth mark rows i s))
  cases hit:rows i with
  | inl e=>
    have left:=paid e hit false
    have right:=paid e hit true
    have val (b) := paid_site S π depth mark unique e b
    simp only [inputSide,hit,Function.Embedding.coe_sumMap,Sum.map_inl,publicRoleFor,left,right,swap,physicalEnds,
      Sum.elim_inl]
    rw [show site S (.inl (HistoryRoles.paid S π depth mark unique (e,false)))=(actualEnds S π depth mark e).1 from val false,
      show site S (.inl (HistoryRoles.paid S π depth mark unique (e,true)))=(actualEnds S π depth mark e).2 from val true]
    split <;> exact paid e hit _
  | inr g=>
    simp only [Function.Embedding.coe_sumMap,Sum.map_inr,Function.Embedding.refl_apply,inputSide,hit,swap]
    rcases g with v|r <;> split <;> cases s <;> rfl

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.DatedRows

end
end OAI
