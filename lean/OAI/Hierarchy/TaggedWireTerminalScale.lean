import OAI.Hierarchy.TaggedWireTerminalOriginal

namespace OAI
/-! # Physical endpoint anchors after the actual stage-scale width mask -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
open ProbeStage CoreBoard AdaptiveProbe ReportSockets Tagged Tagged.WideStack
open ProtocolRAMEmit ProtocolRAMReportedPorts TaggedShorterBudget TaggedShorterSupergroups
open scoped Classical
variable {h W k attempts M : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)
    (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k) (acquired : Bought S π depth marked→Fin b.boughtRows)
    (raw : Fin b.rows→ProtocolRAMEmit.Row)
local notation "name" => b.original S π depth marked order acquired
variable (receipt : Alignment b S π depth marked M raw (fun i=>(raw i).width)
    (b.original S π depth marked order acquired))
variable (stage : Fin b.rows→ℕ) (scale w : ℕ) (hw : 0<w)
local notation "selected" => atScale (b.transport order) stage scale raw
local notation "Live" => {i // 0<pieces selected w i}

section
variable {S}
include hw in
/-- A physical positive-width packet has precisely one active stage. No
zero-width or permanent private socket occurs in the shorter bank. -/
theorem atScale_iff (i : Fin b.rows) :
    0<pieces selected w i ↔ b.transport order i ∧ stage i=scale ∧ 0<(raw i).width := by
  have positive : 0<(w:ℝ):=by exact_mod_cast hw
  rw [pieces,TaggedShorterBudget.copies,Nat.ceil_pos,div_pos_iff_of_pos_right positive,Nat.cast_pos]
  change 0<(if b.transport order i ∧ stage i=scale then (raw i).width else 0) ↔ _
  split <;> simp_all

abbrev Occupied := {i : Active b raw // b.transport order i.val}

def atOriginal (i : Live) : Occupied b order raw :=
  let a:=(atScale_iff b order raw stage scale w hw i.val).mp i.property
  ⟨⟨i.val,a.2.2⟩,a.1⟩

end

def reportedRow : Live ↪ ReportSockets.Row S π depth marked where
  toFun q:=positiveRow S π depth marked b order acquired raw receipt (atOriginal b order raw stage scale w hw q)
  inj' := by
    intro i j eq
    have hit:=(positiveRows S π depth marked b order acquired raw receipt).injective eq
    exact Subtype.ext (congrArg (fun q:Occupied b order raw=>q.val.val) hit)

private theorem flip_twice (i : Active b raw) (s : Bool) :
    sourceSide S π depth marked b order acquired raw receipt i
      (sourceSide S π depth marked b order acquired raw receipt i s) = s :=
  congrArg Prod.snd ((HistoryRoles.orient S π depth marked).left_inv (.inl (receipt.ident i),s))

def flipped : Live×Bool ≃ Live×Bool where
  toFun x:=(x.1,sourceSide S π depth marked b order acquired raw receipt
    (atOriginal b order raw stage scale w hw x.1).val x.2)
  invFun x:=(x.1,sourceSide S π depth marked b order acquired raw receipt
    (atOriginal b order raw stage scale w hw x.1).val x.2)
  left_inv := by
    rintro ⟨i,s⟩
    exact congrArg (fun bit => (i,bit))
      (flip_twice S π depth marked b order acquired raw receipt (atOriginal b order raw stage scale w hw i).val s)
  right_inv := by
    rintro ⟨i,s⟩
    exact congrArg (fun bit => (i,bit))
      (flip_twice S π depth marked b order acquired raw receipt (atOriginal b order raw stage scale w hw i).val s)

/-- The actual grouped anchor passed to `WideStack.output_record`: its first
coordinate is the original emitted group and its second is the source's
immutable stage port, with exactly the same two physical endpoints. -/
def location : Live×Bool ↪ StageColumns h (2^W) × Role k attempts :=
  (flipped S π depth marked b order acquired raw receipt stage scale w hw).toEmbedding.trans
    (((reportedRow S π depth marked b order acquired raw receipt stage scale w hw).prodMap
      (Function.Embedding.refl Bool)).trans (locate S π depth marked unique))

theorem atScale_port (i : Live) (side : Bool) :
    originalPort S π depth marked unique b order acquired raw receipt (atOriginal b order raw stage scale w hw i).val side=
      .inl (.inr (location S π depth marked unique b order acquired raw receipt stage scale w hw (i,side))) :=
  positive_original S π depth marked unique b order acquired raw receipt (atOriginal b order raw stage scale w hw i) side

variable {S} in
include hw in
theorem atScale_width (i : Live) : (selected i.val).width=(raw i.val).width := by
  obtain ⟨positive,time,used⟩:=(atScale_iff b order raw stage scale w hw i.val).mp i.property
  simp [atScale,positive,time]

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment

end
end OAI
