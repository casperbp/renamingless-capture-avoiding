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

We present our technique for renamingless capture avoiding substitution by implementing normalizers for the untyped $\lambda$-calculus in Agda.
We do not assume familiarity with Agda, but assume some familiarity with typed functional programming and \emph{generalized algebraic data types} (GADTs).
We include footnotes to explain Agda specific syntax.
Familiarity with dependent types is not needed to read this section, but is needed for \cref{sec:normalization}.

We first implement a normalizer for \emph{closed} terms (in \cref{sec:interpreting-closed}) using a standard renamingless substitution function, and then use our technique to generalize this to a normalizer for \emph{open} terms (in \cref{sec:interpreting-open}) that uses an equally simple and renamingless substitution function.

\subsection{Normalizing Closed $\lambda$ Terms}
\label{sec:interpreting-closed}

Our normalizers assume that terms use a notion of name for which it is decidable whether two names are the same.
We use a parameterized Agda module to declare these assumptions:\footnote{In Agda, \ad{Set} is the type of types. So \ab{Name}~\as{:}~\ad{Set} declares a type parameter.
The \ab{\_≡?\_} parameter has a \emph{dependent type}: it takes two names as input, where the return type depends on these names. The type \ad{Dec}~\as{(}\ab{x}~\ad{≡}~\ab{y}\as{)} represents a proof that \ab{x} and \ab{y} are (un)equal.
The use of underscores on the left hand side of a function declarations declares the function as mixfix syntax. For example, \ab{\_≡?\_} is an infix function whose first argument is written to the left of \af{≡?} and whose second argument is to the right.}
%
\begin{code}
module Normalizer  (Name : Set)
                   (_≡?_ : (x y : Name) → Dec (x ≡ y)) where
\end{code}
%
Using these parameters we declare a data type representing untyped $\lambda$ terms:
%
\begin{code}
  data Term : Set where
    lam  : Name → Term   → Term
    var  : Name          → Term
    app  : Term → Term   → Term
\end{code}
%
The following standard substitution function assumes that the term being substituted for (i.e., the first parameter of the function) is closed:\footnote{\af{case\_of\_} is a mixfix function whose second argument is a pattern matching function.
The \as{λ}~\ak{where}~$\ldots$ is Agda syntax for a pattern matching function, and \ac{yes} and \ac{no} are the two constructors of the \ad{Dec} type, each parameterized by a proof that the two names are (un)equal.
The substitution function in this section does not make use of these proofs; however, in \cref{sec:normalization} we will.}
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
The reason this substitution function assumes that the term being substituted for is closed is that we could otherwise get variable capture when propagating a substitution under a $\lambda$ binder, as illustrated in the introduction.

Using the substitution function above, we can now define a normalizer which also assumes that the input term is closed, and yields an error in case it encounters a free variable.
It normalizes $\lambda$ terms to \emph{weak head normal form}, and does not evaluate under $\lambda$s.
Thus, the normal forms computed by our normalizer are simply functions whose bodies may contain further normalizable terms:
\begin{code}
  data Val : Set where
    lam : Name → Term → Val
\end{code}
The normalization function below uses the \ad{Maybe} type to indicate that it either returns a value wrapped in a \ac{just} or errs by yielding \ac{nothing} if it encounters a free variable:
\begin{code}
  {-# NON_TERMINATING #-}
  normalize : Term → Maybe Val
  normalize (lam x t)    = just (lam x t)
  normalize (var x)      = nothing
  normalize (app t₁ t₂)  = case (normalize t₁) of λ where
    (just (lam x t)) → case (normalize t₂) of λ where
      (just v)  → normalize ([ V2T v / x ] t)
      _         → nothing
    _ → nothing
\end{code}
\begin{code}[hide]
      where
        V2T : Val → Term
        V2T (lam x t) = lam x t
\end{code}
The function uses an auxiliary function \af{V2T}~\as{:}~\ad{Val}~\as{→}~\ad{Term} which transforms values to terms. 
The \ak{NON\_TERMINATING} pragma disables Agda's termination checker because normalization of untyped $\lambda$ terms may non-terminate.

Similar definitions as what we have shown in this section can be found in many programming language educational texts and research papers.
The definitions let us correctly normalize \emph{closed} terms.
If we attempt to use \af{normalize} to normalize \emph{open} terms instead we may get wrong results.
For example, the following term should normalize to the free variable $y$:
%
\begin{equation}
  (\lambda f .\, (\lambda y .\, (f\ (\lambda one.\, one))))\ (\lambda z.\, \underbrace{y}_{\mathclap{\text{free variable}}})\ (\lambda two.\, two)
  \label{eq1}
\end{equation}
%
\begin{code}[hide]
module _ where
  open import Data.String
  open Normalizer String _≟_

  example = normalize (app (app (lam "f" (lam "y" (app (var "f") (lam "one" (var "one"))))) (lam "z" (var "y"))) (lam "two" (var "two")))
  -- = just (lam "two" (var "two"))
\end{code}
%
However, the \af{normalize} function \emph{incorrectly} normalizes this term to $\lambda two.\, two$ instead.
In the next section we present our technique which performs capture avoiding substitution to correctly normalize the term above, without relying on fiddly renaming during normalization.

\subsection{Normalizing Open $\lambda$ Terms using Renamingless Substitution}
\label{sec:interpreting-open}

\begin{code}[hide]
module NormalizerV  (Name : Set)
                     (_≡?_ : (x y : Name) → Dec (x ≡ y)) where
\end{code}

The idea is to enrich our notion of term to distinguish those terms that have been computed to normal forms (values).
The motivation for distinguishing values, is that values represent terms where all substitutions from their lexically enclosing context have already been applied.
It is futile (and morally wrong) to propagate substitutions into values.
The reason that traditional expositions of the untyped $\lambda$ calculus rely on renaming of bound variables, is that they propagate substitutions into values.
By distinguishing values, we avoid this pitfall, and thus the need for renaming.

The \ad{TermV} data type below is the same as \ad{Term} but has a distinguished \ac{val} constructor for representing values given by a type parameter \ab{V}~\as{:}~\ad{Set}:
%
\begin{code}
  data TermV (V : Set) : Set where
    lam  : Name → TermV V     → TermV V
    var  : Name               → TermV V
    app  : TermV V → TermV V  → TermV V
    val  : V                  → TermV V
\end{code}
%
We can define a substitution function for \ad{TermV} that is case-by-case the same as the substitution function in \cref{sec:interpreting-closed}, except that it also has a case for values (\ac{val}).
This case says that we never substitute inside values.\footnote{The curly braces \as{\{}$\ldots$\as{\}} in the type signature of \af{⟨\_/\_⟩\_} denotes an \emph{implicit parameter} which does not need to be passed explicitly when we call the function.  Agda will automatically infer what the parameter is.}
%
\begin{code}
  ⟨_/_⟩_ : {V : Set} → TermV V → Name → TermV V → TermV V
  ⟨ s / y ⟩ (lam x t) = case (x ≡? y) of λ where
    (yes p) → lam x t
    (no  _) → lam x (⟨ s / y ⟩ t)
  ⟨ s / y ⟩ (var x) = case (x ≡? y) of λ where
    (yes _) → s
    (no  _) → var x
  ⟨ s / y ⟩ (app t₁ t₂) = app (⟨ s / y ⟩ t₁) (⟨ s / y ⟩ t₂)
  ⟨ s / y ⟩ (val v) = val v
\end{code}
%
This substitution function still assumes that the term being substituted for (i.e., the first parameter of the function) is closed.
However, since values may contain free variables, the substitution function does support substitution involving open terms.
Free variables in values are never be captured because we never propagate substitutions into values.

Using these definitions, we define a normalizer to values in weak head normal form, which is now either a function, a free variable, or an application whose sub-terms are also in weak head-normal form:
%
\begin{code}
  data ValV : Set where
    lam  : Name → TermV ValV  → ValV
    var  : Name               → ValV
    app  : ValV → ValV        → ValV
    
  {-# NON_TERMINATING #-}
  normalizeV : TermV ValV → ValV
  normalizeV (lam x t)   = lam x t
  normalizeV (var x)     = var x
  normalizeV (app t₁ t₂) = case (normalizeV t₁) of λ where
    (lam x t)  → normalizeV (⟨ val (normalizeV t₂) / x ⟩ t)
    v₁         → app v₁ (normalizeV t₂)
  normalizeV (val v) = v
\end{code}
%
\begin{code}[hide]
module _ where
  open import Data.String
  open NormalizerV String _≟_

  exampleV = normalizeV (app (app (lam "f" (lam "y" (app (var "f") (lam "one" (var "one"))))) (lam "z" (var "y"))) (lam "two" (var "two")))
  -- = y
\end{code}
%
Unlike the normalizer in \cref{sec:interpreting-closed}, \af{normalizeV} is a \emph{total}, possibly non-terminating function, which takes open untyped $\lambda$ calculus terms as input and yields their weak head normal form as output.
Unlike the substitution functions and normalizers found in most educational texts and research papers in the literature, the normalizer above does not rely on renaming, but does do capture avoiding substitution.
For example, normalizing the term in \cref{eq1} yields the free variable $y$, as intended.

More generally, any substitution performed by \af{normalizeV} is going to be capture avoiding because it only ever performs substitution of \emph{closed} terms under $\lambda$ binders.
The difference between the normalizer in \cref{sec:interpreting-closed} and here is that our normalizer above has a more liberal notion of what it means for a term to be closed.
The next section makes this intuition formal.
