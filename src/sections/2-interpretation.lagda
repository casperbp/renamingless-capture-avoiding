%%
%% Agda setup
%%

\begin{code}[hide]

module sections.2-interpretation where

open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning
open import Relation.Nullary
open import Data.Maybe
open import Data.List using (List; []; _∷_)
open import Algebra using (Op₂)
open import Algebra.Definitions

\end{code}

\section{Interpretation}

\begin{code}
record NameIntf (Name : Set) : Set₁ where
  field _≡?_ : (x y : Name) → Dec (x ≡ y)
\end{code}

\begin{code}[hide]
module Interpreter (Name : Set) (NI : NameIntf Name) where
\end{code}

\begin{code}
  open NameIntf NI
 
  data Expr : Set where
    lam : Name → Expr → Expr
    var : Name → Expr
    app : (e₁ e₂ : Expr) → Expr

  [_/_]_ : Expr → Name → Expr → Expr
  [ e′ / y ] (lam x e) = case (x ≡? y) of λ where
    (yes _) → lam x e
    (no  _) → lam x ([ e′ / y ] e)
  [ e′ / y ] (var x) = case (x ≡? y) of λ where
    (yes _) → e′
    (no  _) → var x
  [ e′ / y ] (app e₁ e₂) = app ([ e′ / y ] e₁) ([ e′ / y ] e₂)

  data Val : Set where
    lam : Name → Expr → Val

  V2E : Val → Expr
  V2E (lam x e) = lam x e
  
  {-# NON_TERMINATING #-}
  interpret : Expr → Maybe Val
  interpret (lam x e)   = just (lam x e)
  interpret (var x)     = nothing
  interpret (app e₁ e₂) = case (interpret e₁) of λ where
    (just (lam x e)) → case (interpret e₂) of λ where
      (just v) → interpret ([ V2E v / x ] e)
      nothing → nothing
    _ → nothing
\end{code}

\begin{code}
  data ExprC (V : Set) : Set where
    lam : Name → ExprC V → ExprC V
    var : Name → ExprC V
    app : (e₁ e₂ : ExprC V) → ExprC V
    val : V → ExprC V

  data ValC : Set where
    lam : Name → ExprC ValC → ValC
    var : Name → ValC

  ⟨_/_⟩_ : {V : Set} → ExprC V → Name → ExprC V → ExprC V
  ⟨ e′ / y ⟩ (lam x e) = case (x ≡? y) of λ where
    (yes p) → lam x e
    (no  _) → lam x (⟨ e′ / y ⟩ e)
  ⟨ e′ / y ⟩ (var x) = case (x ≡? y) of λ where
    (yes _) → e′
    (no  _) → var x
  ⟨ e′ / y ⟩ (app e₁ e₂) = app (⟨ e′ / y ⟩ e₁) (⟨ e′ / y ⟩ e₂)
  ⟨ e′ / y ⟩ (val v) = val v

  {-# NON_TERMINATING #-}
  interpretC : ExprC ValC → Maybe ValC
  interpretC (lam x e)   = just (lam x e)
  interpretC (var x)     = just (var x)
  interpretC (app e₁ e₂) = case (interpretC e₁) of λ where
    (just (lam x e)) → case (interpretC e₂) of λ where
      (just v) → interpretC (⟨ val v / x ⟩ e)
      nothing → nothing
    _ → nothing
  interpretC (val v) = just v
\end{code}
