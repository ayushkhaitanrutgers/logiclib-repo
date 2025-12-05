import Mathlib

namespace LogicBook
namespace ChapterI

universe u


/-- Propositional formulas over variables of type `α`. -/
inductive PropForm (α : Type u) where
  | var  : α → PropForm α
  | bot  : PropForm α                  -- ⊥
  | top  : PropForm α                     -- ⊤
  | not  : PropForm α → PropForm α          -- ¬A
  | and  : PropForm α → PropForm α → PropForm α -- A ∧ B
  | or   : PropForm α → PropForm α → PropForm α -- A ∨ B
  | imp  : PropForm α → PropForm α → PropForm α -- A → B
  | iff  : PropForm α → PropForm α → PropForm α -- A ↔ B
  | nand : PropForm α → PropForm α → PropForm α -- A ∣ B  (nand)
  | nor  : PropForm α → PropForm α → PropForm α -- A ↓ B  (nor)
deriving Repr, DecidableEq

namespace PropForm

variable {α : Type u}

notation:max "⊥ₚ" => PropForm.bot
notation:max "⊤ₚ" => PropForm.top
notation:40 "¬ₚ " A => PropForm.not A
infixr:35 " ∧ₚ " => PropForm.and
infixr:30 " ∨ₚ " => PropForm.or
infixr:25 " →ₚ " => PropForm.imp
infixr:20 " ↔ₚ " => PropForm.iff
infixr:20 " ∣ₚ " => PropForm.nand
infixr:20 " ↓ₚ " => PropForm.nor

/-- Truth assignments (`φ` in the book). -/
abbrev Valuation (α : Type u) := α → Bool

/-- Semantic evaluation `φ(A)` of a formula under a valuation. -/
def eval (v : Valuation α) : PropForm α → Bool
  | .var p     => v p
  | .bot       => false
  | .top       => true
  | .not A     => Bool.not (eval v A)
  | .and A B   => eval v A && eval v B
  | .or  A B   => eval v A || eval v B
  | .imp A B   => Bool.not (eval v A) || eval v B
  | .iff A B   =>
      (eval v A && eval v B) || (Bool.not (eval v A) && Bool.not (eval v B))
  | .nand A B  => Bool.not (eval v A && eval v B)
  | .nor  A B  => Bool.not (eval v A || eval v B)

/-- `v` satisfies `Γ` iff it makes every formula in `Γ` true. -/
def satisfies (v : Valuation α) (Γ : Set (PropForm α)) : Prop :=
  ∀ A ∈ Γ, eval v A = true

/-- A set of formulas is satisfiable if some valuation satisfies it. -/
def Satisfiable (Γ : Set (PropForm α)) : Prop :=
  ∃ v : Valuation α, satisfies v Γ

/-- A set of formulas is unsatisfiable if no valuation satisfies it. -/
def Unsatisfiable (Γ : Set (PropForm α)) : Prop :=
  ¬ Satisfiable Γ

/-- Semantic consequence (`Γ ⊧ₚ A`). -/
def Entails (Γ : Set (PropForm α)) (A : PropForm α) : Prop :=
  ∀ v : Valuation α, satisfies v Γ → eval v A = true

infix:55 " ⊧ₚ " => Entails

/-- Validity: `⊧ₚ A` means `A` is true under every valuation. -/
def valid (A : PropForm α) : Prop :=
  (∅ : Set (PropForm α)) ⊧ₚ A

notation "⊧ₚ " A => valid A

/-- One-premise entailment: `A ⊧₁ B` abbreviates `{A} ⊧ₚ B`. -/
def entails1 (A B : PropForm α) : Prop :=
  ({A} : Set (PropForm α)) ⊧ₚ B

notation A " ⊧₁ " B => entails1 A B

/-- Tautology: true for every valuation. -/
def Tautology (A : PropForm α) : Prop :=
  ∀ v : Valuation α, eval v A = true

/-- Tautological equivalence. -/
def TautEquiv (A B : PropForm α) : Prop :=
  (A ⊧₁ B) ∧ (B ⊧₁ A)

/-- Notation for tautological equivalence. -/
infix:50 " ≡ₜ " => TautEquiv

open Set

/-
  Theorem I.13.
  If Γ ⊆ Δ then:
  (a) every valuation satisfying Δ also satisfies Γ;
  (b) if Δ is satisfiable then Γ is satisfiable;
  (c) if Γ ⊧ₚ A then Δ ⊧ₚ A.
-/
theorem I13a {Γ Δ : Set (PropForm α)} (hsub : Γ ⊆ Δ)
    {v : Valuation α} (hv : satisfies v Δ) :
    satisfies v Γ := by
  sorry

theorem I13b {Γ Δ : Set (PropForm α)} (hsub : Γ ⊆ Δ)
    (hSat : Satisfiable Δ) :
    Satisfiable Γ := by
  sorry

theorem I13c {Γ Δ : Set (PropForm α)} {A : PropForm α}
    (hsub : Γ ⊆ Δ) (hEnt : Γ ⊧ₚ A) :
    Δ ⊧ₚ A := by
  sorry

/-
  Theorem I.14.
  (a) `{A, ¬A}` entails every formula.
  (b) If Γ is unsatisfiable, then Γ entails every formula.
-/
theorem I14a (A B : PropForm α) :
    ({A, ¬ₚ A} : Set (PropForm α)) ⊧ₚ B := by
  sorry

theorem I14b (Γ : Set (PropForm α)) (B : PropForm α)
    (hUnsat : Unsatisfiable Γ) :
    Γ ⊧ₚ B := by
  sorry

/-
  Theorem I.16 (Semantic Deduction Theorem).
  (a) `A ⊧₁ B` iff `⊧ₚ (A →ₚ B)`.
  (b) `Γ ∪ {A} ⊧ₚ B` iff `Γ ⊧ₚ (A →ₚ B)`.
-/
theorem I16a (A B : PropForm α) :
  (A ⊧₁ B) ↔ (⊧ₚ (A →ₚ B)) := by
  sorry

theorem I16b (Γ : Set (PropForm α)) (A B : PropForm α) :
  (Γ ∪ {A} : Set (PropForm α)) ⊧ₚ B ↔ Γ ⊧ₚ (A →ₚ B) := by
  sorry

/-- Big conjunction over a list, using `⊤ₚ` for the empty list. -/
def bigConj : List (PropForm α) → PropForm α
  | []      => ⊤ₚ
  | A :: l  => A ∧ₚ bigConj l

/-
  Theorem I.18.
  If Γ is a finite set `{A₁, ..., Aₙ}`, then
  `Γ ⊧ₚ B` iff `⊧ₚ ((A₁ ∧ₚ ... ∧ₚ Aₙ) →ₚ B)`.
-/
theorem I18 {Γ : Set (PropForm α)} (B : PropForm α)
    (l : List (PropForm α))
    (hΓ : Γ = {X | X ∈ l}) :
    Γ ⊧ₚ B ↔
      ⊧ₚ (bigConj l →ₚ B) := by
  sorry

/-
  Theorem I.19.
  `A ≡ₜ B` iff `⊧ₚ (A ↔ₚ B)`.
-/
theorem I19 (A B : PropForm α) :
  (A ≡ₜ B) ↔ ⊧ₚ (A ↔ₚ B) := by
  sorry

/-
  Theorem I.20.
  `A` is a tautology iff `¬A` is unsatisfiable.
-/
theorem I20 (A : PropForm α) :
  Tautology A ↔ Unsatisfiable ({¬ₚ A} : Set (PropForm α)) := by
  sorry

/-
  Theorem I.21.
  `Γ ⊧ₚ A` iff `Γ ∪ {¬A}` is unsatisfiable.
-/
theorem I21 (Γ : Set (PropForm α)) (A : PropForm α) :
  Γ ⊧ₚ A ↔ Unsatisfiable (Γ ∪ {¬ₚ A}) := by
  sorry

/-- Boolean functions of arity `k`. -/
def BoolFun (k : ℕ) := (Fin k → Bool) → Bool

/-- The Boolean function represented by a formula in variables `0,…,k-1`. -/
def fOfFormula {k : ℕ} (A : PropForm (Fin k)) : BoolFun k :=
  fun v => eval v A

/-
  Theorem I.25.
  Every Boolean function is represented by some propositional formula
  (using the usual connectives).
-/
theorem I25 (k : ℕ) (f : BoolFun k) :
  ∃ A : PropForm (Fin k), fOfFormula A = f := by
  sorry

/-
  Literals, DNF and CNF (for Theorems I.29 and I.30).
-/

/-- A literal is a variable or the negation of a variable. -/
def isLiteral (A : PropForm α) : Prop :=
  match A with
  | .var _         => True
  | .not (.var _)  => True
  | _              => False

/-- A conjunction of literals. -/
def isConjOfLiterals : PropForm α → Prop
  | .and A B => isConjOfLiterals A ∧ isConjOfLiterals B
  | A        => isLiteral A

/-- A clause is a disjunction of literals. -/
def isClause : PropForm α → Prop
  | .or A B => isClause A ∧ isClause B
  | A       => isLiteral A

/-- Disjunctive normal form (DNF). -/
def isDNF : PropForm α → Prop
  | .or A B => isDNF A ∧ isDNF B
  | A       => isConjOfLiterals A

/-- Conjunctive normal form (CNF). -/
def isCNF : PropForm α → Prop
  | .and A B => isCNF A ∧ isCNF B
  | A        => isClause A

/-
  Theorem I.29 (Adequacy of DNF formulas).
  Every Boolean function is represented by a DNF formula.
-/
theorem I29 (k : ℕ) (f : BoolFun k) :
  ∃ A : PropForm (Fin k), isDNF A ∧ fOfFormula A = f := by
  sorry

/-
  Theorem I.30 (Adequacy of CNF formulas).
  Every Boolean function is represented by a CNF formula.
-/
theorem I30 (k : ℕ) (f : BoolFun k) :
  ∃ A : PropForm (Fin k), isCNF A ∧ fOfFormula A = f := by
  sorry

/-
  Adequate sets of connectives (Section I.8).
-/

/-- Primitive connectives for adequacy discussions. -/
inductive Conn where
  | not | and | or | imp | iff | top | bot
  | nand | nor
deriving DecidableEq, Repr

abbrev Language := Set Conn

/-- `A` is an `L`-formula: it uses only connectives from `L`. -/
def InLanguage (L : Language) : PropForm α → Prop
  | .var _     => True
  | .bot       => Conn.bot ∈ L
  | .top       => Conn.top ∈ L
  | .not A     => Conn.not ∈ L ∧ InLanguage L A
  | .and A B   => Conn.and ∈ L ∧ InLanguage L A ∧ InLanguage L B
  | .or A B    => Conn.or ∈ L ∧ InLanguage L A ∧ InLanguage L B
  | .imp A B   => Conn.imp ∈ L ∧ InLanguage L A ∧ InLanguage L B
  | .iff A B   => Conn.iff ∈ L ∧ InLanguage L A ∧ InLanguage L B
  | .nand A B  => Conn.nand ∈ L ∧ InLanguage L A ∧ InLanguage L B
  | .nor A B   => Conn.nor ∈ L ∧ InLanguage L A ∧ InLanguage L B

/-- `L` is adequate if it can represent every Boolean function. -/
def adequate (L : Language) : Prop :=
  ∀ k (f : BoolFun k),
    ∃ A : PropForm (Fin k), InLanguage L A ∧ fOfFormula A = f

/-
  Theorem I.35.
  The full language and the language with just {¬, ∨, ∧} are adequate.
-/
def Lfull : Language :=
  {Conn.not, Conn.and, Conn.or, Conn.imp, Conn.iff}

def LnegOrAnd : Language :=
  {Conn.not, Conn.or, Conn.and}

theorem I35a : adequate Lfull := by
  sorry

theorem I35b : adequate LnegOrAnd := by
  sorry

/-
  Theorem I.36.
  The sets {¬, ∨} and {¬, ∧} are adequate.
-/
def LnegOr : Language := {Conn.not, Conn.or}
def LnegAnd : Language := {Conn.not, Conn.and}

theorem I36a : adequate LnegOr := by
  sorry

theorem I36b : adequate LnegAnd := by
  sorry

/-
  Theorem I.37.
  The set {¬, →} is adequate.
-/
def LnegImp : Language := {Conn.not, Conn.imp}

theorem I37 : adequate LnegImp := by
  sorry

/-
  Theorem I.38.
  (a) {¬} is not adequate.
  (b) {∧, ∨} is not adequate.
-/
def Lneg : Language := {Conn.not}
def LandOr : Language := {Conn.and, Conn.or}

theorem I38a : ¬ adequate Lneg := by
  sorry

theorem I38b : ¬ adequate LandOr := by
  sorry

/-
  Theorem I.39.
  The set {nand} is adequate.
-/
def Lnand : Language := {Conn.nand}

theorem I39 : adequate Lnand := by
  sorry

/-
  Theorem I.40.
  The set {⊥, →} is adequate.
-/
def LbotImp : Language := {Conn.bot, Conn.imp}

theorem I40 : adequate LbotImp := by
  sorry

/-
  Theorem I.41.
  Truth of a formula depends only on the variables that occur in it.
-/

/-- The set of variables that occur in a formula. -/
def vars : PropForm α → Set α
  | .var p    => {p}
  | .bot      => ∅
  | .top      => ∅
  | .not A    => vars A
  | .and A B  => vars A ∪ vars B
  | .or  A B  => vars A ∪ vars B
  | .imp A B  => vars A ∪ vars B
  | .iff A B  => vars A ∪ vars B
  | .nand A B => vars A ∪ vars B
  | .nor  A B => vars A ∪ vars B

theorem I41 (A : PropForm α)
    (φ ψ : Valuation α)
    (h : ∀ p ∈ vars A, φ p = ψ p) :
    eval φ A = eval ψ A := by
  sorry

/-
  Theorem I.42.
  In any formula, the number of open and close parentheses in its
  fully parenthesised string representation are equal.

  We treat the parenthesis counts abstractly via two placeholder functions.
-/

/-- Number of open parentheses in the usual string representation of a formula. -/
axiom mParens : PropForm α → ℕ

/-- Number of close parentheses in the usual string representation of a formula. -/
axiom nParens : PropForm α → ℕ

theorem I42 (A : PropForm α) :
  mParens A = nParens A := by
  sorry

/-
  Theorem I.43.
  For a formula whose first symbol is "(", every non-empty proper
  initial subexpression has more "(" than ")" and hence is not a formula.

  We encode this using abstract predicates capturing the relevant combinatorics.
-/

/-- `B` is a non-empty proper initial subexpression of `A`. -/
axiom IsProperPrefixSubexpr (B A : PropForm α) : Prop

/-- Number of open parentheses in such an initial subexpression. -/
axiom mPrefix : PropForm α → PropForm α → ℕ

/-- Number of close parentheses in such an initial subexpression. -/
axiom nPrefix : PropForm α → PropForm α → ℕ

/-- `A` is written with an initial open parenthesis. -/
axiom startsWithOpenParen (A : PropForm α) : Prop

theorem I43 {A B : PropForm α}
    (hStart : startsWithOpenParen A)
    (hPref  : IsProperPrefixSubexpr B A) :
    mPrefix B A > nPrefix B A := by
  sorry

/-
  Theorem I.44.
  If a formula has `m` binary connectives and `n` propositional
  variables, then `n = m + 1`.

  Again we encode the counting functions abstractly.
-/

/-- Number of occurrences of binary connectives in a formula. -/
axiom numBinaryConns : PropForm α → ℕ

/-- Number of occurrences of propositional variables in a formula. -/
axiom numVars : PropForm α → ℕ

theorem I44 (A : PropForm α) :
  numVars A = numBinaryConns A + 1 := by
  sorry

/-
  Substitution of propositional formulas (Section I.10).
-/

variable [DecidableEq α]

/-- Substitution `A(B/p)` of a formula `B` for a variable `p` in `A`. -/
def substVar (A : PropForm α) (p : α) (B : PropForm α) : PropForm α :=
  match A with
  | .var q     => if q = p then B else .var q
  | .bot       => .bot
  | .top       => .top
  | .not C     => .not (substVar C p B)
  | .and C D   => .and (substVar C p B) (substVar D p B)
  | .or  C D   => .or  (substVar C p B) (substVar D p B)
  | .imp C D   => .imp (substVar C p B) (substVar D p B)
  | .iff C D   => .iff (substVar C p B) (substVar D p B)
  | .nand C D  => .nand (substVar C p B) (substVar D p B)
  | .nor  C D  => .nor  (substVar C p B) (substVar D p B)

/-
  Theorem I.48.
  If `φ(B) = φ(C)` then `φ(A(B/p)) = φ(A(C/p))`.
-/
theorem I48 (A B C : PropForm α) (p : α) (φ : Valuation α)
    (h : eval φ B = eval φ C) :
    eval φ (substVar A p B) = eval φ (substVar A p C) := by
  sorry

/-
  Theorem I.50.
  If `B ≡ₜ C` then `B(A/p) ≡ₜ C(A/p)`.
-/
theorem I50 (A B C : PropForm α) (p : α)
    (h : B ≡ₜ C) :
    substVar B p A ≡ₜ substVar C p A := by
  sorry

end PropForm
end ChapterI
end LogicBook
