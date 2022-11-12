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

We present our technique by implementing normalizers for the untyped $\lambda$-calculus in Agda.
We do not assume familiarity with Agda, but assume some familiarity with typed functional programming and \emph{generalized algebraic data types} (GADTs).
We explain Agda specific syntax in footnotes.
%Familiarity with dependent types is not needed to read this section, but is needed for \cref{sec:normalization}.

We first implement a normalizer for \emph{closed} terms (in \cref{sec:interpreting-closed}) using a standard renamingless substitution function.
We then generalize this normalizer to work on \emph{open} terms (i.e., terms with free variables; in \cref{sec:interpreting-open}) using our simple renamingless substitution strategy instead.

\subsection{Normalizing Closed $\lambda$ Terms}
\label{sec:interpreting-closed}

Our normalizers assume that terms use a notion of name for which it is decidable whether two names are the same.
We use a parameterized Agda module to declare these assumptions:\footnote{\ad{Set} is the type of types. So \ab{Name}~\as{:}~\ad{Set} declares a type parameter.
The \ab{\_≡?\_} parameter is a \emph{dependently typed function}: it takes two names $x$ and $y$ as input, and returns a proof that \ab{x} and \ab{y} are (un)equal (\ad{Dec}~\as{(}\ab{x}~\ad{≡}~\ab{y}\as{)}).
The underscores in \ab{\_≡?\_} indicates that the function is written as infix syntax; i.e., its first argument is written to the left of \af{≡?} and the second to the right.}
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
The \as{λ}~\ak{where}~$\ldots$ is a pattern matching function, where \ac{yes} and \ac{no} are the constructors \ad{Dec}, each parameterized by a proof that two names are (un)equal.
In this section we do not use these proofs; in \cref{sec:normalization} we do.}
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
%
Line 4 %(\as{(}\ac{no}~\as{\_)~→}~\ac{lam}~\ab{x}~\as{(}\af{[}~\ab{s}~\af{/}~\ab{y}~\af{]}~\ab{t}~\as{)})
above propagates \ab{s} under a $\lambda$ that binds an \ab{x}, which is only capture avoiding if we assume that \ab{s} does not contain the variable \ab{x}---or, simply, that \ab{s} is \emph{closed}.

Using the substitution function above, we can define a normalizer for closed terms which normalizes $\lambda$ terms to \emph{weak head normal form}, does not evaluate under $\lambda$s, and errs in case it encounters a free variable.
The normal forms (or \emph{values}) computed by our normalizer are functions whose bodies may contain further normalizable terms; i.e.:
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

Similar definitions as shown above can be found in many programming language educational texts and research papers.
The definitions correctly normalize \emph{closed} terms.
If we apply \af{normalize} to \emph{open} terms instead we may get wrong results.
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
In the next section we present a simple renamingless capture avoiding substitution strategy which correctly normalizes the term above to $y$.

\subsection{Normalizing Open $\lambda$ Terms using Renamingless Substitution}
\label{sec:interpreting-open}

\begin{code}[hide]
module NormalizerV  (Name : Set)
                     (_≡?_ : (x y : Name) → Dec (x ≡ y)) where
\end{code}

The idea is to add a term which delimits and distinguishes those terms that have been computed to normal forms (values) already.
Values represent terms where all substitutions from their lexically enclosing context have already been applied, so it is futile to propagate substitutions into values.
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
We can define a substitution function for \ad{TermV} that is case-by-case the same as the substitution function in \cref{sec:interpreting-closed}, except that (1) it substitutes \emph{values} (\ab{V}) into terms, and (2) it has a case for value terms (\ac{val}):\footnote{The curly braces \as{\{}$\ldots$\as{\}} in the type signature of \af{⟨\_/\_⟩\_} denotes an \emph{implicit parameter} which does not need to be passed explicitly when we call the function.  Agda will automatically infer what the parameter is.}
%
\begin{code}
  ⟨_/_⟩_ : {V : Set} → V → Name → TermV V → TermV V
  ⟨ v / y ⟩ (lam x t) = case (x ≡? y) of λ where
    (yes p) → lam x t
    (no  _) → lam x (⟨ v / y ⟩ t)
  ⟨ v / y ⟩ (var x) = case (x ≡? y) of λ where
    (yes _) → val v
    (no  _) → var x
  ⟨ v / y ⟩ (app t₁ t₂) = app (⟨ v / y ⟩ t₁) (⟨ v / y ⟩ t₂)
  ⟨ v / y ⟩ (val u) = val u
\end{code}
%
The final case above says that we never substitute inside values.
This way, free variables that occur in values are never captured because we never propagate substitutions into values.
In other words, values are \emph{closed}.

As opposed to the substitution function in \cref{sec:interpreting-closed}, the function above accepts values rather than terms as its first argument.
However, this suffices to define a normalizer to values in weak head normal form.
Since terms may contain free variables, the notion of values for this normalizer is now \emph{either} a function, a free variable, \emph{or} an application whose sub-terms are also in values (i.e., weak head-normal forms):
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
    (lam x t)  → normalizeV (⟨ normalizeV t₂ / x ⟩ t)
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
Unlike the normalizer in \cref{sec:interpreting-closed}, \af{normalizeV} is a \emph{total} (but possibly non-terminating) function, which takes open untyped $\lambda$ calculus terms as input and yields their weak head normal form as output.
For example, normalizing the term labeled (\ref{eq1}) yields the free variable $y$, as intended.
Unlike the substitution functions and normalizers found in most educational texts and research papers in the literature, the normalizer above does not rely on renaming.

The substitutions performed by \af{normalizeV} are capture avoiding because we only ever propagate closed terms under $\lambda$ binders.
However, these closed terms may now contain free (but unsubstitutable) variables.
The difference between the normalizer in \cref{sec:interpreting-closed} and here is thus that our normalizer above has a more liberal notion of what it means for a term to be closed.
The next section makes this intuition formal.
