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

\section{Renamingless Capture Avoiding Substitution}
\label{sec:interpretation}

We present our technique for renamingless capture avoiding substitution by implementing a definitional interpreter for the untyped $\lambda$-calculus in Agda.
We do not assume familiarity with Agda, but assume some familiarity with typed programming and \emph{generalized algebraic data types} (GADTs).
We first implement a renamingless substitution function for closed terms, and then show how to generalize this to a renamingless substitution function for open terms.

\subsection{Interpreting Closed $\lambda$ Terms}

For generality, our interpreters are parametric what notion of name they use.
They only assume that it is decidable whether two names are the same.
The following module declares these assumptions as parameters:\footnote{The use of underscores declares functions mixfix syntax. For example, \ab{\_≡?\_} is an infix function whose first argument is written to the left of \af{≡?} and whose second argument is to the right.}$^,$\footnote{The \ab{\_≡?\_} parameter has a \emph{dependent type}: it takes two names as input, where the return type depends on these names. The type \ad{Dec}~\as{(}\ab{x}~\ad{≡}~\ab{y}\as{)} represents a proof that \ab{x} and \ab{y} are (un)equal.}
%
\begin{code}
module Interpreter  (Name : Set)
                    (_≡?_ : (x y : Name) → Dec (x ≡ y)) where
\end{code}
%
Using these parameters we declare a data type representing untyped $\lambda$ terms:
%
\begin{code}
  data Term : Set where
    lam : Name → Term → Term
    var : Name → Term
    app : (t₁ t₂ : Term) → Term
\end{code}
%
The following substitution function is the standard definition of substitution for $\lambda$ terms, assuming that the term being substituted is closed:\footnote{Here, \af{case\_of\_} is a mixfix function whose second argument is a pattern matching function.  The \as{λ}~\ak{where}~$\ldots$ is Agda syntax for a pattern matching function.  Finally, \ac{yes} and \ac{no} are the two constructors of the \ad{Dec} type, each parameterized by either a proof that two names are equal, or a proof that they are not.}
%
\begin{code}
  [_/_]_ : Term → Name → Term → Term
  [ s / y ] (lam x t) = case (x ≡? y) of λ where
    (yes  _)  → lam x t
    (no   _)  → lam x ([ s / y ] t)
  [ s / y ] (var x) = case (x ≡? y) of λ where
    (yes _) → s
    (no  _) → var x
  [ s / y ] (app t₁ t₂) = app ([ s / y ] t₁) ([ s / y ] t₂)
\end{code}

\begin{code}
  data Val : Set where
    lam : Name → Term → Val

  V2E : Val → Term
  V2E (lam x e) = lam x e
  
  {-# NON_TERMINATING #-}
  interpret : Term → Maybe Val
  interpret (lam x e)   = just (lam x e)
  interpret (var x)     = nothing
  interpret (app e₁ e₂) = case (interpret e₁) of λ where
    (just (lam x e)) → case (interpret e₂) of λ where
      (just v) → interpret ([ V2E v / x ] e)
      nothing → nothing
    _ → nothing
\end{code}

\begin{code}
  data TermC (V : Set) : Set where
    lam : Name → TermC V → TermC V
    var : Name → TermC V
    app : (e₁ e₂ : TermC V) → TermC V
    val : V → TermC V

  data ValC : Set where
    lam : Name → TermC ValC → ValC
    var : Name → ValC

  ⟨_/_⟩_ : {V : Set} → TermC V → Name → TermC V → TermC V
  ⟨ e′ / y ⟩ (lam x e) = case (x ≡? y) of λ where
    (yes p) → lam x e
    (no  _) → lam x (⟨ e′ / y ⟩ e)
  ⟨ e′ / y ⟩ (var x) = case (x ≡? y) of λ where
    (yes _) → e′
    (no  _) → var x
  ⟨ e′ / y ⟩ (app e₁ e₂) = app (⟨ e′ / y ⟩ e₁) (⟨ e′ / y ⟩ e₂)
  ⟨ e′ / y ⟩ (val v) = val v

  {-# NON_TERMINATING #-}
  interpretC : TermC ValC → Maybe ValC
  interpretC (lam x e)   = just (lam x e)
  interpretC (var x)     = just (var x)
  interpretC (app e₁ e₂) = case (interpretC e₁) of λ where
    (just (lam x e)) → case (interpretC e₂) of λ where
      (just v) → interpretC (⟨ val v / x ⟩ e)
      nothing → nothing
    _ → nothing
  interpretC (val v) = just v
\end{code}
