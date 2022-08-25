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
    lam  : Name → Term     → Term
    var  : Name            → Term
    app  : (t₁ t₂ : Term)  → Term
\end{code}
%
The following standard substitution function assumes that the term being substituted for (i.e., the first parameter of the function) is closed:
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
Here, \af{case\_of\_} is a mixfix function whose second argument is a pattern matching function.
The \as{λ}~\ak{where}~$\ldots$ is Agda syntax for a pattern matching function, and \ac{yes} and \ac{no} are the two constructors of the \ad{Dec} type, each parameterized by a proof that the two names are (un)equal.
Our pattern matching functions use the wildcard pattern (\as{\_}) for these (in)equality proofs since our substitution function does not make use of them.
In \cref{sec:normalization} we give an \emph{intrinsically capture avoiding} version of this substution function which does make use of these proofs.

Using the substitution function above, we can now define an interpreter.
Our interpreter assumes that the input term is closed, and yields an error in case it encounters a free variable.
It computes $\lambda$ terms to \emph{weak head normal form}, and does not evaluate under $\lambda$s.
Thus the values that our interpreter returns is given by the following data type:
\begin{code}
  data Val : Set where
    lam : Name → Term → Val
\end{code}
Now, our interpreter, which uses the \ad{Maybe} type to indicate that it either returns a value wrapped in a \ac{just} or errs by yielding \ac{nothing}:
\begin{code}
  {-# NON_TERMINATING #-}
  interpret : Term → Maybe Val
  interpret (lam x e)    = just (lam x e)
  interpret (var x)      = nothing
  interpret (app e₁ e₂)  = case (interpret e₁) of λ where
    (just (lam x e)) → case (interpret e₂) of λ where
      (just v) → interpret ([ V2T v / x ] e)
      nothing → nothing
    _ → nothing
      where
        V2T : Val → Term
        V2T (lam x e) = lam x e
\end{code}
Since interpretation of untyped $\lambda$ terms may non-terminate, we use the \ak{NON\_TERMINATING} pragma to disable Agda's termination checker.

Similar definitions as what we have shown in this section can be found in many programming language educational texts and research papers.
The definitions allow us to correctly normalize \emph{closed} terms.
If we try to use the definitions to normalize \emph{open} terms instead, we get wrong results.
For example, the following term should not be normalizable since it contains an (underbraced) free variable.

\begin{equation}
  (\lambda f .\, (\lambda y .\, (f\ (\lambda one.\, one))))\ (\lambda z.\, \underbrace{y}_{\mathclap{\text{free variable}}})\ (\lambda two.\, two)
  \label{eq1}
\end{equation}

\begin{code}[hide]
module _ where
  open import Data.String
  open Interpreter String _≟_

  example = interpret (app (app (lam "f" (lam "y" (app (var "f") (lam "one" (var "one"))))) (lam "z" (var "y"))) (lam "two" (var "two")))
  -- = just (lam "two" (var "two"))
\end{code}

The interpreter above will incorrectly normalize this term to $\lambda two.\, two$.
However, it is supposed to normalize the term to the free variable $y$.
In the next section we present a technique that does capture avoiding substitution without renaming.

\subsection{Interpreting Open $\lambda$ Terms using Renamingless Substitution}

\begin{code}[hide]
module InterpreterV  (Name : Set)
                     (_≡?_ : (x y : Name) → Dec (x ≡ y)) where
\end{code}

As mentioned in the introduction, the idea is to distinguish those terms that have been computed to normal forms (values).
The motivation for distinguishing values, is that values are terms that have been closed under all substitutions arising from the lexically enclosing context of the term.
Thus, it is futile (and arguably wrong) to substitute inside values.

The \ad{TermV} data type below is the same as \ad{Term} but has a distinguished \ac{val} constructor for representing values, where values are given by the type parameter \ab{V}~\as{:}~\ad{Set}:
%
\begin{code}
  data TermV (V : Set) : Set where
    lam  : Name → TermV V     → TermV V
    var  : Name               → TermV V
    app  : (e₁ e₂ : TermV V)  → TermV V
    val  : V                  → TermV V
\end{code}
%
We can define a substitution function for \ad{TermV} that is case-by-case exactly the same as the substitution function from the previous subsection, except that it also has a case for values (\ac{val}).
This case says that we never substitute inside values.
%
\begin{code}
  ⟨_/_⟩_ : {V : Set} → TermV V → Name → TermV V → TermV V
  ⟨ e′ / y ⟩ (lam x e) = case (x ≡? y) of λ where
    (yes p) → lam x e
    (no  _) → lam x (⟨ e′ / y ⟩ e)
  ⟨ e′ / y ⟩ (var x) = case (x ≡? y) of λ where
    (yes _) → e′
    (no  _) → var x
  ⟨ e′ / y ⟩ (app e₁ e₂) = app (⟨ e′ / y ⟩ e₁) (⟨ e′ / y ⟩ e₂)
  ⟨ e′ / y ⟩ (val v) = val v
\end{code}
%
This substitution function still assumes that the term being substituted for (i.e., the first parameter of the function) is closed.
However, since values may contain free variables, the substitution function supports capture avoiding substitution involving open terms.
Free variables in open terms can never be captured because we never propagate substitutions into values.

Using these definitions, we define an interpreter that normalizes terms to values where a value is either a function (\ac{lam}) or a variable (\ac{var}):
%
\begin{code}
  data ValV : Set where
    lam : Name → TermV ValV → ValV
    var : Name → ValV
    
  {-# NON_TERMINATING #-}
  interpretV : TermV ValV → Maybe ValV
  interpretV (lam x e)   = just (lam x e)
  interpretV (var x)     = just (var x)
  interpretV (app e₁ e₂) = case (interpretV e₁) of λ where
    (just (lam x e)) → case (interpretV e₂) of λ where
      (just v) → interpretV (⟨ val v / x ⟩ e)
      nothing → nothing
    _ → nothing
  interpretV (val v) = just v
\end{code}
%
\begin{code}[hide]
module _ where
  open import Data.String
  open InterpreterV String _≟_

  exampleV = interpretV (app (app (lam "f" (lam "y" (app (var "f") (lam "one" (var "one"))))) (lam "z" (var "y"))) (lam "two" (var "two")))
  -- = just (lam "two" (var "two"))
\end{code}
%
With this interpreter, the term in \cref{eq1} normalizes to the free variable $y$, as intended.
