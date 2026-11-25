import OAI.Computability.BorderVNP.DiagonalTallyPacketTable
import OAI.Computability.BorderVNP.DiagonalTallyMaterializeLoop

/-! # Fixed native lookup of the selected cube gadget IDs

Each owned cube vertex has one descriptor giving the first and ending word of a vector
of bit addresses. The native gather reads the actual selector and vertex bits and the
actual incident arguments. Its resulting word is an index in the fixed cube ID table.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyPacket

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM DiagonalTallyGather
open private digitsAt_of_refsAt from OAI.Computability.BorderVNP.DiagonalTallyMaterialize

/-- Public two-word descriptor and the reached bit values for a selected packet vertex. -/
structure Request where
  /-- First address of the vector of bit references. -/
  start : ℕ
  /-- Actual addresses and bits in most-significant-first order. -/
  digits : List (ℕ × Bool)

/-- The complete raw argument code for one native lookup. -/
def Request.index (r : Request) : ℕ := readDigits 0 (r.digits.map Prod.snd)

/-- Load the bit address vector and initialize its accumulator. -/
def startLookup : Code := .block [.load 50 40, .binary .add 40 40 63, .load 52 40,
  .binary .add 40 40 63, .constant 55 0]

/-- Compute the physical table address and fetch its selected gadget ID. -/
def lookupWord : Code := .block [.binary .add 56 43 55,.load 55 56]

/-- Keep the read ID in the output bank for the subsequent sparse tally record. -/
def keepWord : Code := .block [.store 42 55,.binary .add 42 42 63]

/-- One selected table-position lookup for one vertex. -/
def body : Code := .block [startLookup,gather,lookupWord,keepWord]

/-- Scan every public packet-vertex descriptor for this team. -/
def loop : Code := .whileLt 40 41 body

/-- Slots 45 through 47 give the descriptor base, vertex count and shared fixed table.
Slot 71 is a fresh bank for the selected ID words. -/
def setup : Code := .block [readFrame 40 60 61 45,readFrame 41 60 61 46,
  readFrame 43 60 61 47,readFrame 42 60 61 71,.binary .add 41 41 41,
  .binary .add 41 40 41,.constant 63 1]

/-- Entry before materializing the corresponding cube tally increments. -/
def packetLookup : Code := .seq setup loop

variable {w : ℕ}

/-- Values of the descriptor fields and the input addresses they reference. -/
def Request.resident (r : Request) (m : Memory w) (p : ℕ) : Prop :=
  (m p).val = r.start ∧ (m (p+1)).val = r.start+r.digits.length ∧
    DiagonalTallyMaterialize.digitRefsAt m r.start r.digits

/-- Loop registers for the input row interval, next output ID and shared fixed table. -/
def ready (s : Bank w) (p stop dst table : ℕ) : Prop :=
  (s 40).val = p ∧ (s 41).val = stop ∧ (s 42).val = dst ∧ (s 43).val = table ∧ (s 63).val = 1

/-- Each native row fetches a genuine value at the index computed from its reached
bits, at a cost of at most eight ticks per bit plus ten ticks for the row. -/
theorem body_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (r : Request) (p stop dst table : ℕ) (hs : ready s p stop dst table) (hr : r.resident m p)
    (hptr : p+2 < 2^w) (hout : dst+1 < 2^w) (haddr : table+r.index < 2^w) :
    ∃ es t, Runs pub mac body s m es t (Function.update m dst (m (table+r.index))) ∧
      traceCost es ≤ 10+8*r.digits.length ∧ ready t (p+2) stop (dst+1) table := by
  obtain ⟨h40,h41,h42,h43,h63⟩ := hs
  obtain ⟨head,stopDigits,hrefs⟩ := hr
  have ha : startLookup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp [startLookup,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,addressOpFits,addressOp,
      readings,h40,h63]; omega
  obtain ⟨a,t,ra,ca,ta⟩ := Code.runReadOnly startLookup pub mac m s ha
  have ht : ready t (p+2) stop dst table ∧ readings t 50 = r.start ∧
      readings t 52 = r.start+r.digits.length ∧ readings t 55 = 0 := by
    change (readings t 40 = _ ∧ readings t 41 = _ ∧ readings t 42 = _ ∧ readings t 43 = _ ∧
      readings t 63 = _) ∧ _
    rw [ta]
    simp [startLookup,Code.block,Code.evalNat,Function.update,addressOp,readings,
      h40,h41,h42,h43,h63,head,stopDigits]
  obtain ⟨b,u,rb,cb,_,u55,keep⟩ := gather_runs pub mac t m (r.digits.map Prod.snd)
    r.start 0 (r.start+r.digits.length) ht.2.1 ht.2.2.2 ht.2.2.1 ht.1.2.2.2.2 (by simp)
    (digitsAt_of_refsAt m _ _ hrefs) (show r.index < 2^w by omega)
  have hu : ready u (p+2) stop dst table := by
    simpa only [ready,keep 40 (by decide) (by decide) (by decide),
      keep 41 (by decide) (by decide) (by decide),keep 42 (by decide) (by decide) (by decide),
      keep 43 (by decide) (by decide) (by decide),keep 63 (by decide) (by decide) (by decide)] using ht.1
  obtain ⟨u40,u41,u42,u43,u63⟩ := hu
  change (u 55).val = r.index at u55
  have hlookup : lookupWord.safeReadOnly w (readings pub) (readings m) (readings u) := by
    simp [lookupWord,Code.block,Code.safeReadOnly,readings,addressOpFits,u43,u55,haddr]
  obtain ⟨c,y,rc,cc,tc⟩ := Code.runReadOnly lookupWord pub mac m u hlookup
  have hy : ready y (p+2) stop dst table ∧ readings y 55 = (m (table+r.index)).val := by
    change (readings y 40 = _ ∧ readings y 41 = _ ∧ readings y 42 = _ ∧ readings y 43 = _ ∧
      readings y 63 = _) ∧ _
    rw [tc]
    simp [lookupWord,Code.block,Code.evalNat,readings,addressOp,Function.update,u40,u41,u42,u43,u55,u63]
  obtain ⟨⟨y40,y41,y42,y43,y63⟩,y55⟩ := hy
  have ys : y 55 = m (table+r.index) := Fin.ext y55
  let e := effect false y m keepWord
  have rd := effect_runs pub mac false y m keepWord (by decide)
  change Runs pub mac keepWord y m e.trace e.bank e.mem at rd
  have me : e.mem = Function.update m dst (m (table+r.index)) := by
    change Function.update m (y 42).val (y 55) = _
    rw [y42,ys]
  rw [me] at rd
  have y42' : (y 42+y 63).val = dst+1 := by rw [Fin.val_add,y42,y63,Nat.mod_eq_of_lt hout]
  have endState : ready e.bank (p+2) stop (dst+1) table := by
    simp [ready,e,keepWord,Code.block,effect,Function.update,BinaryOp.eval,y40,y41,y42',y43,y63]
  refine ⟨_,_,ra.seq (rb.seq (rc.seq rd)),?_,endState⟩
  unfold traceCost
  simp only [VPVNP.RAMBuckets.cost_append]
  change traceCost a+(traceCost b+(traceCost c+traceCost e.trace)) ≤ _
  have c₁ : startLookup.slots = 5 := by decide
  have c₂ : lookupWord.slots = 2 := by decide
  have c₃ : traceCost e.trace = 2 := (DiagonalTallyRAM.ordinary_cost (by decide) rd).trans rfl
  simp only [List.length_map] at cb
  omega

end DiagonalTallyPacket

end BorderVNP
end Computability
end OAI
