import OAI.Computability.VPVNP.PairShrinkRoleExact
import OAI.Computability.VPVNP.PairShrinkHiddenHeaderTrace
import OAI.Computability.VPVNP.PairNodeChildScanCost

/-! # Trace charges of the selected shrinking role

The child and hidden readers derive field widths from their respective
directories. The private bit loops spend six instructions per bit. Their
external probes depend on the number of fields and children. The locator,
the four handoffs, and both headers are charged at their native instruction
counts, including at a site with an empty child or map list.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkNodeCost

open BurstRAM PrivateRAM DFS Compression CompressorRecords NodeArguments NodeArguments.ChildScan
open ShrinkRole ShrinkHiddenGuess
open scoped Fin.CommRing

variable {w endAddr a g : ℕ} {X : State a g}

private theorem bind_trace {α β : Type*} (a : Reader w endAddr α) (b : α → Reader w endAddr β)
    (node : Word w) (s : Scratch w endAddr) (bs : List Bool) {out : Outcome w endAddr β}
    {rest : List Bool}
    (h : ShrinkRole.bind a b node s bs = some (out, rest)) :
    ∃ first mid last, a node s bs = some (first,mid) ∧
      b first.value node first.updated mid = some (last,rest) ∧
      out.trace = first.trace ++ last.trace := by
  cases h₁ : a node s bs with
  | none => simp [ShrinkRole.bind,h₁] at h
  | some pair =>
    obtain ⟨first,mid⟩ := pair
    obtain ⟨⟨last,tail⟩,h₂,eqn⟩ :=
      Option.map_eq_some_iff.mp (by simpa only [ShrinkRole.bind,h₁] using h)
    cases eqn
    exact ⟨first,mid,last,rfl,h₂,rfl⟩

private theorem decode_shape (seed : List Row) (bs : List Bool)
    (h : (stream seed).length ≤ bs.length) :
    (decode seed bs).1.length=seed.length ∧
      (stream (decode seed bs).1).length=(stream seed).length := by
  induction seed generalizing bs with
  | nil => exact ⟨rfl,rfl⟩
  | cons e es ih =>
    have enough : e.2.length+(stream es).length ≤ bs.length := by
      simpa only [stream,List.flatMap_cons,List.length_append] using h
    obtain ⟨hn,hw⟩ := ih (bs.drop e.2.length) (by simp only [List.length_drop]; omega)
    exact ⟨congrArg Nat.succ hn,by
      simp only [decode,stream,List.flatMap_cons,List.length_append,List.length_take]
      rw [Nat.min_eq_left (by omega : e.2.length ≤ bs.length)]
      exact congrArg (e.2.length+·) hw⟩

theorem hidden_trace (args : Args w) (m : Memory w) (seed : List Row) (node : Word w)
    (s : Scratch w endAddr) (bs tail : List Bool) (out : Outcome w endAddr (List Row))
    (h : hiddenReader args m seed node s bs = some (out, tail)) :
    out.trace=events args m out.value ∧ out.value.length=seed.length ∧
      (stream out.value).length=(stream seed).length := by
  unfold hiddenReader at h
  split at h
  · rename_i enough
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact ⟨rfl,decode_shape seed bs enough⟩
  · contradiction

section

variable (A : Arena) (T : IncidenceDirectory w) (m : Memory w) (older cap : ℕ)
    (desc : Word w → ChildArguments.Descriptor w X)
    (args : List (Child X) → Args w) (seed : List (Child X) → List Row)
    (maps : List (Child X) → List Row → List (ResidentMapLoop.Exact.Action w endAddr))
    (s₁ : Setup w endAddr) (s₂ : List (Child X) → Setup w endAddr)
    (s₃ : List (Child X) → List Row → Setup w endAddr)
    (node : Word w) (s : Scratch w endAddr) (bs tail : List Bool) (out : Outcome w endAddr Unit)
    (run : visitReader A T m older cap desc args seed maps s₁ s₂ s₃ node s bs = some (out, tail))

include run

/-- The two successful reads pass their returned scratch and tape suffix to the
next setup and reader. The map scan runs on the scratch prepared from the
hidden outcome and contributes the final segment of the trace. -/
theorem visit_trace_reached :
    ∃ child mid hidden mapOut ms,
      ChildArguments.reader A T m older cap desc node (s₁.updated node s) bs = some (child,mid) ∧
      hiddenReader (args child.value) m (seed child.value) node
        ((s₂ child.value).updated node child.updated) mid = some (hidden,tail) ∧
      ResidentMapLoop.Exact.scan node (maps child.value hidden.value)
        ((s₃ child.value hidden.value).updated node hidden.updated) = some (ms,mapOut) ∧
      child.value.map Child.site = (desc node).sites ∧
      hidden.value.length = (seed child.value).length ∧
      (stream hidden.value).length = (stream (seed child.value)).length ∧
      out.trace = s₁.trace node s ++
        (ChildHeader.events m node (desc node).directoryBase ++
          ChildScan.events X T m (desc node).source child.value) ++
        (s₂ child.value).trace node child.updated ++
        ShrinkHiddenGuess.events (args child.value) m hidden.value ++
        (s₃ child.value hidden.value).trace node hidden.updated ++ ms := by
  obtain ⟨b₁,bs₁,r₁,h₁,hnext,e₁⟩ := bind_trace _ _ node s bs run
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h₁)
  obtain ⟨child,bs₂,r₂,hc,hnext,e₂⟩ := bind_trace _ _ _ _ _ hnext
  have hChild := ChildArguments.reader_some A T m older cap desc hc
  obtain ⟨b₂,bs₃,r₃,h₂,hnext,e₃⟩ := bind_trace _ _ _ _ _ hnext
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h₂)
  obtain ⟨hidden,bs₄,r₄,hh,hnext,e₄⟩ := bind_trace _ _ _ _ _ hnext
  obtain ⟨trace,hlen,hbits⟩ := hidden_trace _ _ _ _ _ _ _ _ hh
  obtain ⟨b₃,bs₅,r₅,h₃,hnext,e₅⟩ := bind_trace _ _ _ _ _ hnext
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj h₃)
  obtain ⟨⟨mapTrace,mapOut⟩,hmap,eqn⟩ := Option.map_eq_some_iff.mp hnext
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj eqn
  refine ⟨child,bs₂,hidden,mapOut,mapTrace,hc,hh,hmap,hChild.1,hlen,hbits,?_⟩
  rw [e₁,e₂,e₃,e₄,e₅,trace]
  have hct := congrArg Outcome.trace hChild.2.1
  simp only [ChildArguments.outcome] at hct
  simp only [hct,List.append_assoc]

/-- Split the emitted trace of an accepted node into the very child, hidden
and resident-map traces read on this path. The map list and its input scratch
are those produced by the preceding two scans. -/
theorem visit_trace :
    ∃ xs hs t₂ t₃ mapInput mapOut mapTrace,
      xs.map Child.site=(desc node).sites ∧ hs.length=(seed xs).length ∧
      (stream hs).length=(stream (seed xs)).length ∧
      ResidentMapLoop.Exact.scan node (maps xs hs) mapInput = some (mapTrace,mapOut) ∧
      out.trace = s₁.trace node s ++
        (ChildHeader.events m node (desc node).directoryBase ++
          ChildScan.events X T m (desc node).source xs) ++
        (s₂ xs).trace node t₂ ++ ShrinkHiddenGuess.events (args xs) m hs ++
        (s₃ xs hs).trace node t₃ ++ mapTrace := by
  obtain ⟨child,_,hidden,mapOut,mapTrace,_,_,hmap,sites,hlen,hbits,trace⟩ :=
    visit_trace_reached A T m older cap desc args seed maps s₁ s₂ s₃ node s bs tail out run
  exact ⟨child.value,hidden.value,child.updated,hidden.updated,_,mapOut,mapTrace,
    sites,hlen,hbits,hmap,trace⟩

end

open private lines_probes from OAI.Computability.VPVNP.CompressorRecordRegisterSetup
open private eval_cost from OAI.Computability.VPVNP.CompressorRecordsRowRecipe

theorem hidden_header_cost (selectors stride : ℕ) (ptr : Word w) (m : Memory w) :
    (Header.canonicalTrace selectors stride ptr m).length =
      (RegisterSetup.lines (Header.recipe selectors stride)).length ∧
    countProbes (Header.canonicalTrace selectors stride ptr m)=5 := by
  refine ⟨(eval_cost ..).1,(lines_probes ..).trans ?_⟩
  simp only [Fin.sum_univ_succ,Fin.sum_univ_zero,Header.recipe,PhaseRecipe.Expr.header,
    PhaseRecipe.Expr.headerAddress,PhaseRecipe.Expr.add]
  rfl

end PairSimulation.ShrinkNodeCost

end VPVNP
end Computability
end OAI
