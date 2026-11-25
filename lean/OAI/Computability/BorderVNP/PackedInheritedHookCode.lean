import OAI.Computability.BorderVNP.PackedInheritedHookQuery

/-! # Word template for a terminal-side clipped-hook record

One arithmetic record takes the looked-up matched count, a live interval's
ordinal and span, and its canonical virtual wire start. It is exactly the
compressed equality of the terminal's immutable sparse program. Empty spans
retain their encoded ordinal, while no bit is read at that ordinal.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedHook

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Crossing.Profile.Cell Inherited InheritedProfile BankSite BankJoint BankCircuit BankPacket CellSparse Word
open scoped Classical

/-- The four live numeric operands of one hook equality. -/
inductive Arg where | matched | span | ordinal | wire
  deriving DecidableEq

instance : Fintype Arg := ⟨{.matched,.span,.ordinal,.wire},by intro i; cases i <;> simp⟩

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- The terminal original row's start per matched block. -/
noncomputable def originalScale := (Fintype.equivFin (Unit ⊕ Unit ⊕ Fin e.count) (.inr (.inl ()))).val *
  (Nat.clog 2 e.count+2*m)

/-- The generated record word tape for one candidate, with exact copy and lane strides. -/
noncomputable def code : RecordCode Arg :=
  let stage := WidthExpr.binary .add (PoolCircuit.scaleExpr .matched (originalScale e)) (.field .ordinal)
  let work := Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)
  let cable := WidthExpr.binary .add (PoolCircuit.scaleExpr .matched work) (.field .wire)
  .equal (.const 1) (.field .span) ⟨stage,.const 0,.const 1⟩ ⟨cable,.const 0,.const 1⟩

/-- The compressed tag, copy and span fields and the two three-word ports occupy nine words. -/
theorem code_length : (code e).words.length = 9 := rfl

/-- Fixed straight-line node count for the nine payload fields. -/
noncomputable def nodes := ∑ j : Fin 9, ((code e).words[j.val]'(j.isLt.trans_eq (code_length e).symm)).nodes

/-- The two address additions are the only arithmetic which needs headroom beyond the four inputs. -/
theorem words_fit (w : ℕ) (x : Arg → ℕ) (h : ∀ i,x i < 2^w) (hone : 1 < 2^w)
    (hstage : originalScale e*x .matched+x .ordinal < 2^w)
    (hwire : Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)*x .matched+x .wire < 2^w) :
    ∀ expr ∈ (code e).words,expr.Fits w x := by
  have hs := PoolCircuit.scale_fits w x .matched (originalScale e) (h _) (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hstage)
  have hc := PoolCircuit.scale_fits w x .matched (Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m))
    (h _) (Nat.lt_of_le_of_lt (Nat.le_add_right _ _) hwire)
  change ∀ expr ∈ ([WidthExpr.const 1,.const 1,.field .span,
    .binary .add (PoolCircuit.scaleExpr .matched (originalScale e)) (.field .ordinal),.const 0,.const 1,
    .binary .add (PoolCircuit.scaleExpr .matched (Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)))
      (.field .wire),.const 0,.const 1] : List (WidthExpr Arg)),expr.Fits w x
  simp only [List.forall_mem_cons,List.not_mem_nil,IsEmpty.forall_iff,implies_true,and_true,
    WidthExpr.Fits,WidthExpr.eval,PoolCircuit.scale_eval,Op.apply]
  exact ⟨hone,hone,h _,⟨hs,h _,hstage⟩,Nat.two_pow_pos _,hone,⟨hc,h _,hwire⟩,Nat.two_pow_pos _,hone⟩

/-- The mathematical four-field row for a clipped hook whose physical destination owns the terminal. -/
def fields (j span ordinal wire : ℕ) : Arg → ℕ
  | .matched => j | .span => span | .ordinal => ordinal | .wire => wire

variable [NeZero D] {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
variable (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
variable (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
private noncomputable abbrev G := (output e p bin perm positive first q).layout
variable (a : S) {ns ne np : ℕ} (siteID : (G e p bin perm positive first q).Site ↪ Fin ns)
variable (edgeID : (G e p bin perm positive first q).Edge ↪ Fin ne) (portID : P ↪ Fin np)
variable (binName : S → ℕ) (d : Fin D) (z : {z : p.layout.Edge // bin z = some (perm d a)}) (src : Bool)
local notation3 "G₀" => G e p bin perm positive first q
local notation3 "j₀" => blocks p.layout bin perm m a
local notation3 "work₀" => workAt e p bin perm positive first q
local notation3 "edge₀" => seedHook e p bin perm a d z src

/-- At the actual live matched cable this word template decodes to the physical
terminal-side hook equality, including its original row ordinal and the true
incident word start. -/
theorem read_record :
    let desc := descriptor p.layout bin perm m binName z (some (d,true))
    let v := (G₀).dst edge₀
    let wire := wireStart G₀ edgeID portID v ⟨edge₀,.inr rfl⟩
    (code e).read (fields j₀ desc.span desc.ordinal wire) =
      terminalHook e p bin perm positive first q a id work₀ siteID edgeID portID binName d z src := by
  intro desc v wire
  let t := (d,if src then positive z.val else !(positive z.val))
  let node := seedSite e p bin perm positive first q a (.inr (.inl t))
  have hv : v = node := (hook_fields e p bin perm positive first q binName a d z src).2.1
  have off : CellAddresses.siteBase G₀ id v siteID work₀ ⟨v,rfl⟩ = 0 :=
    (congrArg (fun u => CellAddresses.siteBase G₀ id u siteID work₀ ⟨u,rfl⟩) hv).trans
      (profile_start e p bin perm positive first q a siteID (.inr t))
  have hn : ∀ u : Incident G₀ v, (G₀).src u.val ≠ (G₀).dst u.val :=
    hv.symm ▸ profile_noLoop e p bin perm positive first q a (.inr t)
  have hwire := singleton_wire G₀ v work₀ edgeID portID hn ⟨edge₀,.inr rfl⟩
  let L := terminalLayout j₀ m (q a).val
  have stride := terminalStride j₀ m (q a).val (profileCounts_total e _ q a)
  have base : (L.port (.inr (.inl ()))).base = originalScale e*j₀ := by
    simp only [L,BankLayout.port,stride,originalScale]
    ac_rfl
  have work : work₀ v = Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*(Nat.clog 2 e.count+2*m)*j₀ := by
    rw [hv]
    change BankCharges.volume e j₀ (q a).val (.inr (.inl t)) = _
    simp only [BankCharges.volume,stride]
    ac_rfl
  simp only [code,RecordCode.read,PortCode.read,WidthExpr.eval,PoolCircuit.scale_eval,Op.apply,fields]
  change _ = Record.equal 1 desc.span
    (desc.terminalPort ⟨CellAddresses.siteBase G₀ id v siteID work₀ ⟨v,rfl⟩+(L.port (.inr (.inl ()))).base,0,1⟩)
    ⟨CellAddresses.wireBase G₀ id v edgeID portID work₀ ⟨v,rfl⟩ ⟨edge₀,.inr rfl⟩,0,1⟩
  rw [off,zero_add,base,hwire,work]
  simp [CutDescriptor.terminalPort,CutDescriptor.slice,wire]

end Packing.InheritedHook

end BorderVNP
end Computability
end OAI
