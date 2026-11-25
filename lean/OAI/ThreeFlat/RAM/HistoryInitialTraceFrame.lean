import OAI.ThreeFlat.RAM.HistoryInitialRecordScan
import OAI.ThreeFlat.RAM.TraceSuffixPrepared

namespace OAI
/-! # The immutable banks used while a selected trace atom is being scanned -/
namespace ThreeFlat.RAM.HistoryInitialSeed
open Computability.VPVNP.BurstRAM TraceBucketAtom TraceSuffixOracle PhysicalPrelude
variable {W : ℕ}

/-- Each physically mounted input bank survives the selected writes. The long
trace rows are generated from the compact template and have no physical bank here. -/
structure Immutable {F : Type*} [Fintype F] [Field F] {w : ℕ} (A : Layout) (z : Site)
    (B : TraceBucketAtom.Layout) (_cells dictionaryRows maskCount : ℕ) (I : Image F w)
    (loc : Locations) : Prop where
  constants : Protected A z 0 2
  ids : Protected A z B.tableIds B.slots
  dictionary : Protected A z B.dictionary dictionaryRows
  masks : Protected A z B.masks (max maskCount (1+2*B.depth))
  description : Protected A z loc.description I.advice
  parameters : Protected A z loc.parameters I.parameters
  table : Protected A z loc.table (w*FixedTraceImage.count I.G)

variable {F : Type*} [Fintype F] [Field F] {w : ℕ} {A : Layout} {z : Site} {B : TraceBucketAtom.Layout}
    {dict mask : ℕ} {I : Image F w} {loc : Locations} {m src : Memory W}

def immutableBanks (B : TraceBucketAtom.Layout) (_cells dict mask : ℕ) (I : Image F w) (loc : Locations) :
    List (ℕ×ℕ) :=
  [(0,2),(B.tableIds,B.slots),
    (B.dictionary,dict),(B.masks,max mask (1+2*B.depth)),(loc.description,I.advice),
    (loc.parameters,I.parameters),(loc.table,w*FixedTraceImage.count I.G)]

theorem Immutable.of_spans {cells : ℕ} (sep : Separated A z)
    (away : ∀ span ∈ immutableBanks B cells dict mask I loc,
      span.1 + span.2 ≤ z.stream A ∨ A.ctrl + 42 ≤ span.1) : Immutable A z B cells dict mask I loc := by
  have protectedBank (base length : ℕ) (present : (base,length)∈immutableBanks B cells dict mask I loc) :
      Protected A z base length := Protected.of_span sep (away (base,length) present)
  constructor <;> apply protectedBank <;> simp [immutableBanks]

theorem Immutable.mounted {cells : ℕ} (Q : Immutable A z B cells dict mask I loc) (keep : z.retains A m src)
    {D : Fin I.advice→Bool} {par : Fin I.parameters→Bool}
    (h : Mounted I loc (fun a=>(src a).val) D par) : Mounted I loc (fun a=>(m a).val) D par where
  description i:=by rw [Q.description.read keep _ i.isLt];exact h.description i
  parameters i:=by rw [Q.parameters.read keep _ i.isLt];exact h.parameters i
  table i:=by rw [Q.table.read keep _ i.isLt];exact h.table i


end ThreeFlat.RAM.HistoryInitialSeed

end OAI
