import OAI.Hierarchy.DescentTerminalBookCalibration
import OAI.Hierarchy.DescentTerminalFormatCalibration
import OAI.Hierarchy.DescentEarlyMatrixBudget
import OAI.Hierarchy.DescentExteriorTableBits

namespace OAI
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentCompiler.TerminalScale DescentTerminalLocalPortBook
open DescentPrimitivePalette Filter
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec)
variable (drift t f g reset τ B : ℕ)
local notation "κ" => groupRate G t f g reset
local notation "L" => localSocketRate G t g
local notation "uRate" => Nat.clog 2 G.b*(t+1)

/-- Literal domains used by the single terminal instruction, for every allowed original host. -/
structure EarnedTables (S : AtomSchedule) (k j rest W q p height : ℕ) : Prop where
  book : Book.fixedWords (S.groupCount S.length*2^k) (NativeBranch.localLimit G S) W q≤2^(height/2)
  keys : let V:=S.groupCount S.length*2^k
         DescentTerminalSiteShelves.alphabet V W (max 1 (V*actualSpan G S op q p drift))≤2^(height/2)
  headers : let K:=NativeBranch.privateSlotCapacity G S drift
            let tags:=DescentBundleTagKeys.capacity (colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
              (max 8 (2^S.capGain)) K p drift
            (DescentTerminalPrintedFields.capacity q tags K (S.epochPower^S.localTokenExponent) K p
              (S.groupCount S.length*2^k)).total≤2^(height/2)
  exterior : DescentExteriorShelf.tableBits j rest (S.firstWidth G.b p)≤height/2

theorem earned_tables (branch : G.b≤2^(capRate G t g)) (big : 20≤B) (reserve : 2*L≤τ)
    (packing : 2*(L+(τ+κ+4))+uRate≤B)
    (router : 2*((τ+κ+4)+(L+uRate)+2)≤B)
    (cohorts : 2*(τ+κ+(6*(terminalDegree G t f g reset+1)+19))≤B)
    (books : 2*bookRate G t f g reset τ≤B) :
    ∀ᶠ height:ℕ in atTop,let J:=Nat.log 2 height/(2*B)
      ∀M : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
      let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
      let W:=NativeBranch.binLimit (k:=k) S
      let j:=Nat.clog 2 (NativeBranch.localLimit G S)
      let dim:=S.groupWidth k (tail τ J) 0+k
      let q:=2^j*(G.b^(t*J)*G.b)
      let p:=W*(height/(16*(q*W)))
      EarnedTables G op drift S k j (dim-2*j) W q p height :=by
  filter_upwards [terminal_format_calibration_full G op drift t f g reset τ B branch (by omega) cohorts router,
    terminal_book_and_route_room G t f g reset τ B (by omega) books,early_matrix_words G t f g reset τ B big,
    early_native_packing G t f g reset τ B big reserve packing] with height ft bk mx pk
  intro J M S k W j dim q p
  have domains:=ft M
  obtain ⟨sliced,_,_,packed,_⟩:=pk M
  have square : 4*(dim*dim+dim+1)≤height :=(mx M).2.2
  refine ⟨bk M,domains.2.2.2.1,domains.2.2.2.2.1,?_⟩
  have shape : dim=j+(j+(dim-2*j)):=sliced
  have size : 16*(2^j*S.firstWidth G.b p)≤height:=packed
  rw [shape] at square
  unfold DescentExteriorShelf.tableBits DescentExterior.keyBits
  omega

end
end Hierarchy.DescentSixParty

end OAI
