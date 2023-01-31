%if False
\begin{code}
data Nat
  = Z
  | S Nat
  deriving (Show, Eq, Ord)

monus :: Nat -> Nat -> Nat
monus Z     _     = Z
monus m     Z     = m
monus (S m) (S n) = monus m n

foldNat :: a -> (a -> a) -> Nat -> a
foldNat base _ Z = base
foldNat base ind (S n) = ind (foldNat base ind n)
\end{code}
%endif

\section{Berkling-Fehr Substitution}
\label{sec:shifting}

Motivated by how to implement a functional programming language based on Church's $\lambda$-calculus~\cite{10.2307/1968337}, Berkling~and~Fehr~\cite{berkling1982amodification} introduced a modified $\lambda$-calculus which uses a different kind of name binding and substitution.
The key idea is to use a special operator ($\#$) that acts on variables to neutralize the effect of one $\lambda$ binding.
For example, in the term $\lambda x.\, \lambda x.\, \# x$ the sub-term $\# x$ is a variable that references the \emph{outermost} binding of $x$, whereas in $\lambda x.\, \lambda y.\, \# x$ the sub-term $\# x$ is a free variable.

Berkling~and~Fehr's $\#$ operator is related to De Bruijn indices~\cite{de_Bruijn_1972} insofar as $\#^n x$ acts like an index that tells us to move $n$ binders of $x$ outwards.
Indeed, if we were to restrict programs in Berkling~and~Fehr's calculus to use exactly one name, Berkling-Fehr substitution coincides with De Bruijn substitution.
However, whereas De Bruijn indices can be notoriously difficult for humans to read (especially for beginners), Berkling-Fehr uses named variables such that indices only appear for substitutions that would otherwise have variable capture.
This makes Berkling-Fehr variables easier to read for humans.

The definitions of shifting and substitution which we summarize in this section are taken from the work Berkling~and~Fehr~\cite{berkling1982amodification} with virtually no changes.
However, the language we implement is slightly different: they implement a modified $\lambda$-calculus with a call-by-name semantics, whereas we implement the same call-by-value language as in \cref{sec:interpretation}.
Our purpose of replicating their work is two-fold: to increase the awareness of Berkling-Fehr substitution and its seemingly nice properties, and to facilitate comparison with the renamingless approach we presented in \cref{sec:interpreting-open}.


\subsection{Interpreting Open Expressions with Berkling-Fehr Substitution}

Below (left) is a syntax for $\lambda$ expressions similarly to earlier, but now with Berkling-Fehr indices (right) instead of variables, where |Nat| is the type of natural numbers:
\\
%format Expr2
%format Lam2
%format Var2
%format App2
%format Num2
\begin{minipage}{0.395\linewidth}
\begin{code}
data Expr2
  =  Lam2 String Expr2
  |  Var2 Index
  |  App2 Expr2 Expr2
  |  Num2 Int
\end{code}
%if False
\begin{code}
  deriving Show
\end{code}
%endif
\end{minipage}
\vline
\begin{minipage}{0.595\linewidth}
\begin{code}
data Index = I { depth :: Nat, name :: String }
\end{code}
%if False
\begin{code}
  deriving (Show, Eq)
\end{code}
%endif
\end{minipage}
\\
%format Z = 0
%
Here the (record) data constructor |I n x| corresponds to an $n$-ary application of the special $\#$ operator to the name $x$; i.e., $\#^n x$.
We will refer to the $n$ in |I n x| as the |depth| of an index.
As discussed above, a Berkling-Fehr index is similar to a De Bruijn index except that whereas a De Bruijn index tells us how many scopes to move out in order to locate a binder, a Berkling-Fehr index tells us how many scopes \emph{that bind the same name} to move out in order to locate a binder.
In what follows, we will sometimes use $\lambda$ notation as informal syntactic sugar for the constructors in Haskell above.
When doing so, we use ``naked'' variables $x$ as informal syntactic sugar for a variable at depth 0; i.e., |Var2 (I Z x)|.

%if False
\begin{code}
inc :: Index -> Index
dec :: Index -> Index
\end{code}
\begin{code}
inc i = i { depth = S $ depth i }

dec i = i { depth = depth i `monus` S Z }
\end{code}
%endif

To define Berkling-Fehr substitution, we need a notion of \emph{shifting}.
Shifting is used when we propagate a substitution, say $x \mapsto e$ where $x$ is a name and $e$ is an expression, under a binder $y$.
To this end, a shift increments the depth of all free occurrences of $y$ in $s$ by one.
Such shifting guarantees that free occurrences of $y$ in $s$ are not accidentally captured.
%
\begin{code}
shift :: Index -> Expr2 -> Expr2
shift i (Lam2 x e)    |  name i == x             = Lam2 x (shift (inc i) e)
                      |  otherwise               = Lam2 x (shift i e)
shift i (Var2 i')     |  name i == name i'
                         && depth i <= depth i'  = Var2 (inc i')
                      |  otherwise               = Var2 i'
shift i (App2 e1 e2)  =  App2 (shift i e1) (shift i e2)
shift _ (Num2 z)      =  Num2 z
\end{code}
%
The |shift| function binds an index as its first argument.
The name of this index (e.g., $x$) denotes the name to be shifted.
The depth of the index denotes the \emph{cut-off} for the shift; i.e., how many $\#$'s an $x$ must at least be prefixed by before it is a free variable reference to $x$.
For example, say we wish to shift all free references to |x| in the term $\lambda x.\, x\ (\# x)$.
We should only shift $\# x$, not $x$, since $x$ references the locally $\lambda$ bound $x$.
For this reason, the shift function uses a cut-off which is incremented when we move under binders by the same name as we are trying to shift.
For example:
\begin{align*}
        & |shift|\ x\ (\lambda x.\, x\ (\# x)) \\
  |==|\ & \lambda x.\, (|shift|\ (\# x)\ x)\ (|shift|\ (\# x)\ (\# x)) \\
  |==|\ & \lambda x.\, x\ (\#\# x)
\end{align*}
%
%format subst2
%
The Berkling-Fehr substitution function |subst2| applies shifting to avoid variable capture when propagating substitutions under $\lambda$ binders:
%
\begin{code}
subst2 :: Index -> Expr2 -> Expr2 -> Expr2
subst2 i s (Lam2 x e)    | name i == x  = Lam2 x (subst2 (inc i) (shift (I Z x) s) e)
                         | otherwise    = Lam2 x (subst2 i       (shift (I Z x) s) e)
subst2 i s (Var2 i')     | i == i'      = s
                         | otherwise    = Var2 i'
subst2 i s (App2 e1 e2)  = App2 (subst2 i s e1) (subst2 i s e2)
subst2 _ _ (Num2 z)      = Num2 z
\end{code}

To interpret an |Expr2| application $e_1\ e_2$, we first interpret |e1| to a function $\lambda x.\, e$, and then substitute |x| in the body |e|, such that occurrences of |x| at a higher depth are left untouched.
But after we have substituted the bound occurrences of |x| in $e$, the depth of the remaining occurrences of |x| in $e$ need to be decremented.
To this end, we use an |unshift| function which decrements the depth of a given name, modulo a cut-off which now tells us what depth a name has to strictly be larger than in order for it to be a free variable to be unshifted:
%
\begin{code}
unshift :: Index -> Expr2 -> Expr2
unshift i (Lam2 x e)    | name i == x            = Lam2 x (unshift (inc i) e)
                        | otherwise              = Lam2 x (unshift i e)
unshift i (Var2 i')     | name i == name i'
                          && depth i < depth i'  = Var2 (dec i')
                        | otherwise              = Var2 i'
unshift i (App2 t1 t2)  = App2 (unshift i t1) (unshift i t2)
unshift _ (Num2 z)      = Num2 z
\end{code}
%
Using |unshift|, we can now implement an interpreter that does evaluation under $\lambda$s and that uses capture-avoiding substitution:
%
%format normalize2
\begin{code}
normalize2 :: Expr2 -> Expr2
normalize2 (Lam2 x e)    = Lam2 x (normalize2 e)
normalize2 (Var2 i)      = Var2 i
normalize2 (App2 e1 e2)  = case normalize2 e1 of
  Lam2 x e  -> unshift (I Z x) (normalize2 (subst2 (I Z x) (normalize2 e2) e))
  e1'       -> App2 e1' (normalize2 e2)
normalize2 (Num2 z)      = Num2 z
\end{code}
%
The problematic program from \cref{sec:renamingless-bad} now yields a result with a free variable, as expected:
%
\[
      |normalize2|\ ((\lambda x.\, \lambda y.\, x)\ y)\
|==|\ \lambda y.\, \# y
\]

\subsection{Relation to Renamingless Substitution}
\label{sec:relation-renaming}

On the surface, the techniques involved in Berkling-Fehr substitution and our renamingless substitution strategy from \cref{sec:interpretation} may seem different.
A common point between the two is that they avoid renaming by strategically closing off certain variables to protect them from substitutions from lexically closer binders, and strategically reopening those variables to substitutions coming from lexically distant binders.

The renamingless substitution strategy achieves this by using a syntactic and rather coarse-grained discipline which closes entire sub-branches over all possible substitutions, similar to how closures \`{a} la Landin~\cite{Landin64}.
When the interpreter reaches a closed sub-expression, it is re-opened.
As discussed, this discipline works well for languages that do not perform evaluation under binders.
While we demonstrated the technique using a call-by-value language in \cref{sec:interpretation}, the technique is equally applicable to call-by-name interpretation.
But not for languages that perform evaluation under binders.

Berkling-Fehr substitution uses a more fine-grained approach to strategically close off variables to protect them from substitutions from lexically closer binders, by shifting free occurrences of variables when moving under a binder.
When a binder is eliminated, terms are unshifted.
This fine-grained approach is not subject to the same limitations as the renamingless approach from \cref{sec:interpreting-open}.
Indeed, in their paper, Berkling~and~Fehr~\cite{berkling1982amodification} prove that their notion of substitution and their modified $\lambda$-calculus is consistent with Church's $\lambda$ calculus.
Since shifting and unshifting requires more recursion over terms than the simpler renamingless approach from \cref{sec:interpretation}, Berkling-Fehr substitution is less efficient.
However, it is still more efficient than the renaming approach discussed in \cref{sec:intermezzo}.

As discussed, Berkling-Fehr substitution is closely related to De Bruijn indices, the main difference being that Berkling-Fehr use names and are more readable.
To work around the readability issue with De Bruijn indices, one might also combine a named and De Bruijn approach where variable nodes comprise \emph{both} a name \emph{and} a De Bruijn index.
But that leaves the question of how to disambiguate programs with ambiguous name.
For example, using this approach, how would the pretty-printed version of the Berkling-Fehr indexed expression $\lambda x.\, \lambda x.\, \# x$ look?
Berkling-Fehr indices strike an attractive balance between efficiency, preserving names from source programs, and readability.

%if False
\begin{code}
interp2 :: Expr2 -> Expr2
interp2 (Lam2 x t)    = Lam2 x t
interp2 (Var2 i)      = Var2 i
interp2 (App2 t1 t2)  = let v2 = interp2 t2
  in case interp2 t1 of
       Lam2 x t -> unshift (I Z x) $ interp2 (subst2 (I Z x) v2 t)
       v1       -> App2 v1 v2
interp2 (Num2 z)      = Num2 z


mkDeepApp :: Int -> Expr2
mkDeepApp n = go n (Lam2 "x" (Var2 (I Z "x")))
  where go n e | n <= 0 = App2 e (Num2 42)
        go n e = let x = "x" ++ show n
          in go (n - 1) (Lam2 x (App2 e (Var2 (I Z x))))
\end{code}
%endif


%%% Local Variables:
%%% reftex-default-bibliography: ("../references.bib")
%%% End:
