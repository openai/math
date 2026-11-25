import OAI.ThreeFlat.RAM.PhysicalProgram

namespace OAI
/-! # Execution of the fixed physical descriptor and the contraction tail -/

namespace ThreeFlat.RAM.PhysicalPinsExpr.Program

open scoped Fin.CommRing

open Diagonal BitLayout Computability.VPVNP.BurstRAM GeneratedContraction Contraction DescriptorScan

variable {F : Type*} [Fintype F] [Field F] {w b : ℕ}
variable (s : Shape) [NeZero s.period] (N : BitNetwork F (s.area+2*s.halfBits))
variable (params : Fin s.parameterBits → Bool)

abbrev sizePins := Diagonal.BoundaryWire.pinWidth s.chunks s.bits s.advice

noncomputable abbrev pub (fit : Fits (H s N params) w) :=
  extraWords s N (codec (H s N params) fit)
    (cellsBase (sizePins s) (H s N params).internal)

noncomputable abbrev native (fit : Fits (H s N params) w) :=
  machine (H s N params) fit (program w).first (expressionRows (program w)) (pub s N params fit)

abbrev cost := 13+5*(H s N params).internal+22*(H s N params).cells+
  (11*(H s N params).cells)*(2*(program w).binds+4)

theorem value (fit : Fits (H s N params) w) (pin : Fin (sizePins s) → Bool) (m₀ : Memory w)
    (margin : 5*b+128≤w) (shapeFit : ∀ p,s.words p<2^b)
    (rowsFit : N.cells≤2^b) (pinsFit : s.area+2*s.halfBits≤2^b)
    (blockFit : s.last+1≤2^b) (ticksFit : (s.last+1)*(s.inside+1)≤2^w)
    (teamFit : s.teams≤2^w) (eleven : 11≤2^b)
    (srcFit : 2+(s.area+2*s.halfBits)+N.internal<2^w) (widthFit : N.cells+s.halfBits<2^w)
    (hparams : mulBase (sizePins s) (H s N params).internal (H s N params).cells≤s.parameterBase)
    (hrows : mulBase (sizePins s) (H s N params).internal (H s N params).cells≤s.templateBase)
    (rp : ∀ j : Fin s.parameterBits,(m₀ (s.parameterBase+j.val)).val=(params j).toNat)
    (rr : ∀ i j,m₀ (s.templateBase+11*(i:Fin N.cells).val+(j:Fin 11).val)=
      record N (codec (H s N params) fit) i j)
    (initial : ∀ a<footprint (H s N params), a<cellsBase (sizePins s) (H s N params).internal ∨
      mulBase (sizePins s) (H s N params).internal (H s N params).cells≤a →
      m₀ a = memory (H s N params) (codec (H s N params) fit) pin (fun _=>false) a)
    (state : Word w) (extra : ℕ) :
    RAM.value (codec (H s N params) fit) (native s N params fit) (extra+cost (w:=w) s N params)
      state m₀ = (H s N params).eval pin := by
  let net := H s N params
  let base := cellsBase (sizePins s) net.internal
  let stop := mulBase (sizePins s) net.internal net.cells
  let code := codec net fit
  let M := native s N params fit
  have hdata (i : Fin 20) : M.publicData (extraIndex i)=extraWords s N code base i := by
    simp [M,GeneratedContraction.machine,DescriptorScan.assemble,extraIndex,pub,code,base,net]
  have hc : 11<2^w := by
    have hb : b<w := by omega
    exact eleven.trans_lt (Nat.pow_lt_pow_right (by decide) hb)
  suffices h : RAM.value code M (extra+13+5*net.internal+22*net.cells+
      (11*net.cells)*(2*(program w).binds+4)) state m₀=net.eval pin by
    simpa only [cost,Nat.add_assoc] using h
  apply value_eq_expression net fit (program w) (extraWords s N code base) pin
    (fun _=>false) m₀ state extra ?_ initial
  dsimp only
  intro addr m lo hi untouched
  obtain ⟨⟨cell,slot⟩,k⟩ := BitNetwork.exists_rowLocation (q:=net.cells) lo hi
  let col : Fin 11 := finSumFinEquiv slot
  obtain ⟨⟨block,localCell⟩,hCell⟩ := (finProdFinEquiv (m:=s.last+1) (n:=N.cells+s.halfBits)).surjective cell
  let a := GuardedDescriptor.recordAddress base N.cells s.halfBits block.val localCell.val col.val
  have addrEq : a=addr.val := by
    rw [← k,← hCell]
    change base+(11*(block.val*(N.cells+s.halfBits)+localCell.val)+col.val) =
      base+11*(localCell.val+(N.cells+s.halfBits)*block.val)+col.val
    ac_rfl
  have kr (i : Fin N.cells) (j : Fin 11) :
      m (s.templateBase+11*i.val+j.val) = record N code i j :=
    (untouched _ (Or.inr ((hrows.trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)))).trans (rr i j)
  have kp (i : Fin s.parameterBits) : (m (s.parameterBase+i.val)).val=(params i).toNat := by
    rw [untouched _ (Or.inr (hparams.trans (Nat.le_add_right _ _))),rp]
  have checked := reads s m params N code margin shapeFit rowsFit pinsFit blockFit ticksFit teamFit kp kr eleven
  have bound : a<2^w := by rw [addrEq]; exact addr.isLt
  have hw := row s N code base params m M.publicData hdata checked block localCell col srcFit widthFit hc bound
  have addrWord : (a : Word w)=addr := by rw [addrEq]; exact Fin.cast_val_eq_self _
  change (program w).eval M.publicData m (fun _=>addr)=_
  calc
    _ = (program w).eval M.publicData m (fun _=>(a : Word w)) :=
      congrArg (fun z => (program w).eval M.publicData m (fun _=>z)) addrWord.symm
    _ = record net code (finProdFinEquiv (block,localCell)) col := hw
    _ = record net code cell col := congrArg (fun z : Fin net.cells => record net code z col) hCell
    _ = memory net code pin (fun _=>false) (base+11*cell.val+col.val) :=
      (read_record net code pin (fun _=>false) cell col).symm
    _ = memory net code pin (fun _=>false) addr.val := congrArg (memory net code pin (fun _=>false)) k

end ThreeFlat.RAM.PhysicalPinsExpr.Program

end OAI
