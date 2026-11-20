import Savitch.TM.Layout
import Savitch.TM.Digits
import Savitch.Machine.Next
import Mathlib.Tactic.DeriveFintype

/-!
# The Savitch TM's alphabet, and building a successor block

Phase 4b-4 of the Savitch formalization (see `PLAN.md`).

`Sym Λ Γ` is the tape alphabet: blank, the left marker `mk`, the bits `z` / `o`, the
flags `yes` / `no`, records `rc r` (one per work cell of `M`), and `key q i g`
(used to case-split on `M`'s transition table).

`buildS q₂ g₂ U S A₁ A₂ P₂` writes, on tape `S`, the record block whose cell `j` is
`(if A₁ marks j then g₂ else symbol of U_j, A₂ marks j, bit j of P₂, q₂)`, in four
passes (`Spec.buildS`). With `A₁` marking `M`'s work head, `A₂` marking the moved
head and `P₂` holding the moved input position, this is exactly the encoding of the
successor configuration (`build_eq_encR`).
-/

set_option linter.unusedSectionVars false

namespace Savitch.Edge

open TM Machine Machine.NTM

/-- The tape alphabet of the Savitch Turing machine. -/
inductive Sym (Λ Γ : Type) where
  | blank
  | mk
  | z
  | o
  | yes
  | no
  | rc (r : Rec Λ Γ)
  | key (q : Λ) (i : Option Bool) (g : Γ)
  deriving DecidableEq, Fintype

variable {Λ Γ : Type} [Fintype Λ] [Fintype Γ] [DecidableEq Λ] [DecidableEq Γ]

def isRec : Sym Λ Γ → Bool
  | .rc _ => true
  | _ => false

/-- The bit symbol of `b`. -/
abbrev bit (b : Bool) : Sym Λ Γ := bsym .z .o b

/-- Is the symbol the bit `o`? -/
def isO : Sym Λ Γ → Bool
  | .o => true
  | _ => false

/-! ### The pure construction -/

/-- One cell of a built block. -/
def buildRec (q₂ : Λ) (g₂ : Γ) (r : Rec Λ Γ) (b₁ b₂ b₃ : Bool) : Rec Λ Γ :=
  (if b₁ then g₂ else r.1, b₂, b₃, q₂)

def build (q₂ : Λ) (g₂ : Γ) : List (Rec Λ Γ) → List Bool → List Bool → List Bool → List (Rec Λ Γ)
  | r :: rs, b₁ :: l₁, b₂ :: l₂, b₃ :: l₃ => buildRec q₂ g₂ r b₁ b₂ b₃ :: build q₂ g₂ rs l₁ l₂ l₃
  | _, _, _, _ => []

theorem build_ofFn (q₂ : Λ) (g₂ : Γ) : ∀ {L : ℕ} (f : Fin L → Rec Λ Γ) (m₁ m₂ m₃ : Fin L → Bool),
    build q₂ g₂ (List.ofFn f) (List.ofFn m₁) (List.ofFn m₂) (List.ofFn m₃) =
      List.ofFn (fun j => buildRec q₂ g₂ (f j) (m₁ j) (m₂ j) (m₃ j))
  | 0, _, _, _, _ => rfl
  | L + 1, f, m₁, m₂, m₃ => by
    simp only [List.ofFn_succ, build]
    rw [build_ofFn q₂ g₂ (fun j => f j.succ) (fun j => m₁ j.succ) (fun j => m₂ j.succ)
      (fun j => m₃ j.succ)]

/-- **The built block is the successor's encoding.** -/
theorem build_eq_encR {n L : ℕ} (hL : 0 < L) (u : Fin (nV Λ Γ L)) (t : Λ × Γ × Dir × Dir)
    (b' : BCfg Λ Γ n L) (hb' : nextB (decV (n := n) hL u) t = some b') :
    build t.1 t.2.1 (List.ofFn (recs u))
        (List.ofFn fun j => decide (j = (decV (n := n) hL u).2.2.1))
        (List.ofFn fun j => decide (j = b'.2.2.1))
        (toBits b'.2.1.val L) =
      List.ofFn (encR b') := by
  rw [← ofFn_getD (toBits b'.2.1.val L) (toBits_length _ L), build_ofFn]
  obtain ⟨q₂, g₂, di, dw⟩ := t
  simp only [nextB] at hb'
  split_ifs at hb' with hlt
  simp only [Option.some.injEq] at hb'
  subst hb'
  congr 1
  funext j
  simp only [buildRec, encR, decV, decR, Function.update_apply]
  by_cases hj : j = firstFlag hL (recs u)
  · simp [hj]
  · simp [hj]

/-! ### The four passes on tape -/

variable {k : ℕ} {x : List Bool} {B : ℕ}

/-- Pass 1: copy the symbols of `U`, clearing the flag and bit tracks, state `q₂`. -/
def h₁ (q₂ : Λ) : Sym Λ Γ → Sym Λ Γ
  | .rc r => .rc (r.1, false, false, q₂)
  | g => g

/-- Pass 2: write `g₂` where `A₁` is marked. -/
def F₂ (g₂ : Γ) : Sym Λ Γ → Sym Λ Γ → Sym Λ Γ
  | .rc r, .o => .rc (g₂, r.2.1, r.2.2.1, r.2.2.2)
  | g, _ => g

/-- Pass 3: set the head flag where `A₂` is marked. -/
def F₃ : Sym Λ Γ → Sym Λ Γ → Sym Λ Γ
  | .rc r, .o => .rc (r.1, true, r.2.2.1, r.2.2.2)
  | g, _ => g

/-- Pass 4: copy the bits of `P₂` into the input-bit track. -/
def F₄ : Sym Λ Γ → Sym Λ Γ → Sym Λ Γ
  | .rc r, b => .rc (r.1, r.2.1, isO b, r.2.2.2)
  | g, _ => g

/-- Build the successor block on tape `S`. -/
noncomputable def buildS (q₂ : Λ) (g₂ : Γ) (U S A₁ A₂ P₂ : Fin k) : Code k (Sym Λ Γ) :=
  copyPass U S .mk isRec (h₁ q₂) ++ zipPass S A₁ .mk isRec (F₂ g₂) ++
    zipPass S A₂ .mk isRec F₃ ++ zipPass S P₂ .mk isRec F₄

theorem pass_list (q₂ : Λ) (g₂ : Γ) : ∀ (ru : List (Rec Λ Γ)) (m₁ m₂ m₃ : List Bool),
    m₁.length = ru.length → m₂.length = ru.length → m₃.length = ru.length →
    List.zipWith F₄ (List.zipWith F₃ (List.zipWith (F₂ g₂) ((ru.map Sym.rc).map (h₁ q₂))
        (m₁.map bit)) (m₂.map bit)) (m₃.map bit) =
      (build q₂ g₂ ru m₁ m₂ m₃).map Sym.rc
  | [], [], [], [], _, _, _ => rfl
  | r :: rs, b₁ :: l₁, b₂ :: l₂, b₃ :: l₃, h₁', h₂', h₃' => by
    simp only [List.map_cons, List.zipWith_cons_cons, build, List.cons.injEq]
    refine ⟨?_, pass_list q₂ g₂ rs l₁ l₂ l₃ (by simpa using h₁') (by simpa using h₂')
      (by simpa using h₃')⟩
    cases b₁ <;> cases b₂ <;> cases b₃ <;> rfl

theorem not_mk_rec {l : List (Rec Λ Γ)} : ∀ g ∈ l.map (Sym.rc (Λ := Λ) (Γ := Γ)), g ≠ .mk := by
  intro g hg; obtain ⟨r, _, rfl⟩ := List.mem_map.1 hg; exact fun h => by cases h

theorem not_mk_bit {l : List Bool} : ∀ g ∈ l.map (bit (Λ := Λ) (Γ := Γ)), g ≠ .mk := by
  intro g hg; obtain ⟨b, _, rfl⟩ := List.mem_map.1 hg
  cases b <;> simp [bit, bsym]

theorem isRec_rec {l : List (Rec Λ Γ)} : ∀ g ∈ l.map (Sym.rc (Λ := Λ) (Γ := Γ)), isRec g = true := by
  intro g hg; obtain ⟨r, _, rfl⟩ := List.mem_map.1 hg; rfl

theorem forall_mem_zipWith {α β γ : Type} (F : α → β → γ) (P : γ → Prop) :
    ∀ {la : List α} {lb : List β}, (∀ a ∈ la, ∀ b, P (F a b)) → ∀ g ∈ List.zipWith F la lb, P g
  | [], _, _, g, hg => by simp at hg
  | _ :: _, [], _, g, hg => by simp at hg
  | a :: la, b :: lb, h, g, hg => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at hg
    rcases hg with rfl | hg
    · exact h a (List.mem_cons_self) b
    · exact forall_mem_zipWith F P (fun a' ha' b' => h a' (List.mem_cons_of_mem _ ha') b') g hg

theorem agree_lay {k : ℕ} {S' : Fin k → Prop} {T T' : Tapes k (Sym Λ Γ)}
    (h : T.Agree S' T') {t : Fin k} (ht : ¬ S' t) {m₀ e₀ : Sym Λ Γ} {l : List (Sym Λ Γ)}
    (hl : Lay t m₀ e₀ T l) : Lay t m₀ e₀ T' l :=
  hl.congr (h t ht).1 (h t ht).2

theorem agree_layW {k : ℕ} {S' : Fin k → Prop} {T T' : Tapes k (Sym Λ Γ)}
    (h : T.Agree S' T') {t : Fin k} (ht : ¬ S' t) {m₀ : Sym Λ Γ} {l : List (Sym Λ Γ)}
    (hl : LayW t m₀ T l) : LayW t m₀ T' l :=
  hl.congr (h t ht).1 (h t ht).2

/-- A record-valued cell map keeps records records. -/
def RecPres (F : Sym Λ Γ → Sym Λ Γ → Sym Λ Γ) : Prop := ∀ r b, ∃ r', F (.rc r) b = .rc r'

theorem recPres_F₂ (g₂ : Γ) : RecPres (F₂ (Λ := Λ) g₂) := fun r b => by
  cases b <;> exact ⟨_, rfl⟩

theorem recPres_F₃ : RecPres (F₃ (Λ := Λ) (Γ := Γ)) := fun r b => by
  cases b <;> exact ⟨_, rfl⟩

theorem recPres_F₄ : RecPres (F₄ (Λ := Λ) (Γ := Γ)) := fun _ _ => ⟨_, rfl⟩

/-- Lists of records: every element is `rc _`. -/
def AllRec (l : List (Sym Λ Γ)) : Prop := ∀ g ∈ l, ∃ r, g = .rc r

theorem AllRec.isRec {l : List (Sym Λ Γ)} (h : AllRec l) : ∀ g ∈ l, isRec g = true := by
  intro g hg; obtain ⟨r, rfl⟩ := h g hg; rfl

theorem AllRec.not_mk {l : List (Sym Λ Γ)} (h : AllRec l) : ∀ g ∈ l, g ≠ .mk := by
  intro g hg; obtain ⟨r, rfl⟩ := h g hg; exact fun e => by cases e

theorem AllRec.zipWith {F : Sym Λ Γ → Sym Λ Γ → Sym Λ Γ} (hF : RecPres F) {la lb : List (Sym Λ Γ)}
    (h : AllRec la) : AllRec (List.zipWith F la lb) :=
  forall_mem_zipWith F _ (fun a ha b => by obtain ⟨r, rfl⟩ := h a ha; exact hF r b)

/-- What the four passes produce, as a list. -/
theorem Spec.buildS {U S A₁ A₂ P₂ : Fin k} (hUS : U ≠ S) (hS1 : S ≠ A₁) (hS2 : S ≠ A₂)
    (hSP : S ≠ P₂) (q₂ : Λ) (g₂ : Γ)
    {ru : List (Rec Λ Γ)} {ls : List (Sym Λ Γ)}
    {m₁ m₂ m₃ : List Bool} {T : Tapes k (Sym Λ Γ)}
    (hU : Lay U .mk .blank T (ru.map .rc)) (hS : Lay S .mk .blank T ls)
    (hA₁ : LayW A₁ .mk T (m₁.map bit)) (hA₂ : LayW A₂ .mk T (m₂.map bit))
    (hP₂ : LayW P₂ .mk T (m₃.map bit))
    (hls : ls.length = ru.length) (hm₁ : m₁.length = ru.length) (hm₂ : m₂.length = ru.length)
    (hm₃ : m₃.length = ru.length) (hT : T.Within B) (hB : ru.length + 2 ≤ B) :
    ∃ T', Spec (Edge.buildS q₂ g₂ U S A₁ A₂ P₂) x B T T' ∧
      Lay S .mk .blank T' ((build q₂ g₂ ru m₁ m₂ m₃).map .rc) ∧
      T.Agree (fun i => i = S) T' ∧ T'.ih = T.ih ∧ T'.Within B := by
  have hmb : (Sym.mk : Sym Λ Γ) ≠ .blank := fun h => by cases h
  have hrl : (ru.map (Sym.rc (Λ := Λ) (Γ := Γ))).length = ru.length := List.length_map _
  -- pass 1: copy symbols from `U`
  obtain ⟨T₁, s1, hU₁, hS₁, ag1, ih1, hW₁⟩ := Spec.copyPass (x := x) (p := isRec) (h := h₁ q₂)
    hUS hmb hU hS (by rw [hrl, hls]) isRec_rec rfl not_mk_rec
    (fun g hg => by obtain ⟨r, _, rfl⟩ := List.mem_map.1 hg; exact fun h => by cases h)
    hT (by rw [hrl]; exact hB)
  set l₁ := (ru.map (Sym.rc (Λ := Λ) (Γ := Γ))).map (h₁ q₂)
  have hl₁ : AllRec l₁ := fun g hg => by
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    obtain ⟨r, _, rfl⟩ := List.mem_map.1 hg'
    exact ⟨_, rfl⟩
  have hl₁len : l₁.length = ru.length := by simp [l₁]
  have hA₁₁ := agree_layW ag1 (Ne.symm hS1) hA₁
  have hA₂₁ := agree_layW ag1 (Ne.symm hS2) hA₂
  have hP₂₁ := agree_layW ag1 (Ne.symm hSP) hP₂
  -- pass 2: write `g₂` at the old head
  obtain ⟨T₂, s2, hS₂, _, ag2, ih2, hW₂⟩ := Spec.zipPass (x := x) (p := isRec) (F := F₂ g₂)
    hS1 hmb hS₁ hA₁₁ (by simp [hm₁, hl₁len]) hl₁.isRec rfl not_mk_bit
    (hl₁.zipWith (recPres_F₂ g₂)).not_mk hW₁ (by rw [hl₁len]; exact hB)
  set l₂ := List.zipWith (F₂ g₂) l₁ (m₁.map bit)
  have hl₂ : AllRec l₂ := hl₁.zipWith (recPres_F₂ g₂)
  have hl₂len : l₂.length = ru.length := by simp [l₂, List.length_zipWith, hm₁, hl₁len]
  have hA₂₂ := agree_layW ag2 (Ne.symm hS2) hA₂₁
  have hP₂₂ := agree_layW ag2 (Ne.symm hSP) hP₂₁
  -- pass 3: set the new head flag
  obtain ⟨T₃, s3, hS₃, _, ag3, ih3, hW₃⟩ := Spec.zipPass (x := x) (p := isRec) (F := F₃)
    hS2 hmb hS₂ hA₂₂ (by simp [hm₂, hl₂len]) hl₂.isRec rfl not_mk_bit
    (hl₂.zipWith recPres_F₃).not_mk hW₂ (by rw [hl₂len]; exact hB)
  set l₃ := List.zipWith F₃ l₂ (m₂.map bit)
  have hl₃ : AllRec l₃ := hl₂.zipWith recPres_F₃
  have hl₃len : l₃.length = ru.length := by simp [l₃, List.length_zipWith, hm₂, hl₂len]
  have hP₂₃ := agree_layW ag3 (Ne.symm hSP) hP₂₂
  -- pass 4: copy the input-position bits
  obtain ⟨T₄, s4, hS₄, _, ag4, ih4, hW₄⟩ := Spec.zipPass (x := x) (p := isRec) (F := F₄)
    hSP hmb hS₃ hP₂₃ (by simp [hm₃, hl₃len]) hl₃.isRec rfl not_mk_bit
    (hl₃.zipWith recPres_F₄).not_mk hW₃ (by rw [hl₃len]; exact hB)
  refine ⟨T₄, ((s1.seq s2).seq s3).seq s4, ?_, ?_, by rw [ih4, ih3, ih2, ih1], hW₄⟩
  · have := pass_list q₂ g₂ ru m₁ m₂ m₃ hm₁ hm₂ hm₃
    rw [← this]; exact hS₄
  · exact ((ag1.trans ag2).trans ag3).trans ag4

end Savitch.Edge
